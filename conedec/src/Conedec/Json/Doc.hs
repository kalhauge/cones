{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Conedec.Json.Doc (
  debugCodec,
  Doc,
  prettyViaCodec,
) where

-- base
import Data.Monoid
import Data.Proxy
import Data.String
import Data.Void
import GHC.TypeLits

-- aeson
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Key as Aeson
import qualified Data.Aeson.KeyMap as Aeson

-- mtl
import Control.Monad.State

-- cone
import Data.Cone

-- text
import qualified Data.Text.Lazy.Encoding as Text

-- prettyprinter
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

-- condec
import Conedec.Codec
import Conedec.Json
import Control.Monad

data PrettyState = PrettyState
  { knownSymbols :: !(Aeson.KeyMap ())
  , _workList :: ![(Aeson.Key, Pretty)]
  }

newtype PrettyM a = PrettyM {runPrettyM :: State PrettyState a}
  deriving newtype (Functor, Applicative, Monad)

runPretty :: Pretty -> PP.Doc Void
runPretty p =
  let
    (res, PrettyState st wl) = runState (runPrettyM p) (PrettyState Aeson.empty [])
   in
    PP.vcat
      [ "------"
      , renderSmartDoc res
      , "------"
      , PP.vcat (go st wl)
      , "------"
      ]
 where
  go ks = \case
    [] -> []
    (k, v) : xs -> do
      ["<" PP.<> PP.pretty (Aeson.toText k) PP.<> ">" PP.<> " ::= " PP.<> PP.nest 2 (renderSmartDoc' res)] <> go ks' deps
     where
      (res, PrettyState ks' deps) = runState (runPrettyM v) (PrettyState ks xs)

type Pretty = PrettyM SmartDoc

prettyCodec :: forall ctx a. Codec ValueC ctx Doc a -> Pretty
prettyCodec = prettyViaCodec' prettyViaValueCodec
 where
  prettyViaCodec' :: (forall b. e ctx Doc b -> Pretty) -> Codec e ctx Doc t -> Pretty
  prettyViaCodec' fn = \case
    BrokenCodec ->
      pure ">broken<"
    SumCodec order diag -> do
      (Any a, res) <-
        getAp $
          diagramFold
            order
            ( \a -> Ap do
                res <- prettyViaCodec' fn a
                pure case res of
                  AnyDoc x ds -> (Any x, ds)
                  x -> (Any False, [renderSmartDoc x])
            )
            diag
      pure $ AnyDoc a res
    ProductCodec order diag -> do
      res <-
        getAp $
          diagramFold
            order
            ( \a -> Ap do
                res <- prettyViaCodec' fn a
                pure case res of
                  AllDoc ds -> ds
                  x -> [renderSmartDoc x]
            )
            diag
      pure $ AllDoc res
    ReferenceCodec (Ref :: Ref s) f -> do
      let n = symbolVal (Proxy :: Proxy s)
      let k = Aeson.fromString n
      let ca = f (def @s)
      alreadyMember <- PrettyM (gets (Aeson.member k . knownSymbols))
      unless alreadyMember do
        PrettyM (modify $ \(PrettyState x y) -> PrettyState (Aeson.insert k () x) ((k, prettyViaCodec' fn ca) : y))
      pure . Doc $ "<" <> PP.pretty n <> ">"
    DimapCodec _ _ c ->
      prettyViaCodec' fn c
    ElementCodec c ->
      fn c
    AnnotateCodec s c -> do
      res <- prettyViaCodec' fn c
      pure . Doc $ renderSmartDoc res <> PP.line <> "-- " <> s

  prettyViaValueCodec :: forall t. ValueC ctx Doc t -> Pretty
  prettyViaValueCodec = \case
    StringCodec ->
      pure "<string>"
    NumberCodec ->
      pure "<number>"
    BoolCodec ->
      pure "<bool>"
    ManyOfCodec a -> do
      res <- prettyViaCodec' prettyViaValueCodec a
      doc $ "manyOf" PP.<+> renderSmartDoc' res
    MapOfCodec a -> do
      res <- prettyViaCodec' prettyViaValueCodec a
      doc $ "mapOf" PP.<+> renderSmartDoc' res
    ArrayCodec a -> do
      res <- prettyViaCodec' prettyViaArrayCodec a
      doc $ "array" PP.<+> renderSmartDoc' res
    ObjectCodec a -> do
      res <- prettyViaCodec' prettyViaObjectCodec a
      doc $ "object" PP.<+> renderSmartDoc' res
    ExactValueCodec e ->
      case e of
        Aeson.Null -> do
          pure $ AnyDoc True []
        _ ->
          doc $ PP.pretty . Text.decodeUtf8 $ Aeson.encode e

  prettyViaObjectCodec :: forall t. ObjectC ctx Doc t -> Pretty
  prettyViaObjectCodec = \case
    EmptyObjectCodec -> pure "<empty>"
    FieldCodec k cd -> do
      res <- prettyViaCodec' prettyViaValueCodec cd
      doc $ PP.hsep [PP.pretty (Aeson.toString k), ":", renderSmartDoc' res]

  prettyViaArrayCodec :: forall t. ArrayC ctx Doc t -> Pretty
  prettyViaArrayCodec = \case
    EmptyArrayCodec -> pure "<empty>"
    SingleCodec cd ->
      prettyViaCodec' prettyViaValueCodec cd

debugCodec :: Codec ValueC ctx Doc a -> IO ()
debugCodec c = PP.putDoc (runPretty $ prettyCodec c)
{-# INLINE debugCodec #-}

prettyViaCodec :: Codec ValueC ctx Doc a -> Doc
prettyViaCodec = runPretty . prettyCodec
{-# INLINE prettyViaCodec #-}

type Doc = PP.Doc Void

data SmartDoc
  = Doc (PP.Doc Void)
  | AnyDoc Bool [PP.Doc Void]
  | AllDoc [PP.Doc Void]

instance IsString SmartDoc where
  fromString = Doc . fromString

renderSmartDoc :: SmartDoc -> PP.Doc Void
renderSmartDoc = \case
  Doc d -> d
  AnyDoc False [d] -> d
  AnyDoc False ds ->
    PP.vcat ["+ " <> PP.nest 2 d | d <- ds]
  AnyDoc True [] -> "null"
  AnyDoc True [d] -> "nullable" PP.<+> d
  AnyDoc True ds ->
    PP.vcat ["? " <> PP.nest 2 d | d <- ds]
  AllDoc ds ->
    PP.vcat ["* " <> PP.nest 2 d | d <- ds]

renderSmartDoc' :: SmartDoc -> PP.Doc Void
renderSmartDoc' = \case
  Doc d -> d
  AnyDoc False [d] -> d
  AnyDoc False ds ->
    PP.line <> PP.vcat ["+ " <> PP.nest 2 d | d <- ds]
  AnyDoc True [] -> "null"
  AnyDoc True [d] -> "nullable" PP.<+> d
  AnyDoc True ds ->
    PP.line <> PP.vcat ["? " <> PP.nest 2 d | d <- ds]
  AllDoc ds ->
    PP.line <> PP.vcat ["* " <> PP.nest 2 d | d <- ds]

doc :: PP.Doc Void -> PrettyM SmartDoc
doc = pure . Doc
