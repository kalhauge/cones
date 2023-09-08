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
) where

-- base
import Data.Proxy
import Data.String
import Data.Void
import GHC.TypeLits

-- mtl
import Control.Monad.Reader
import Control.Monad.Writer

-- aeson
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Key as Aeson
import qualified Data.Aeson.KeyMap as Aeson

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

prettyCodec :: forall ctx a. Codec ValueC ctx Doc a -> Pretty
prettyCodec = prettyViaCodec prettyViaValueCodec
 where
  prettyViaCodec :: (forall b. e ctx Doc b -> Pretty) -> Codec e ctx Doc t -> Pretty
  prettyViaCodec fn = \case
    BrokenCodec ->
      pure ">broken<"
    SumCodec order diag -> do
      res <-
        getAp $
          diagramFold
            order
            ( \a -> Ap do
                res <- prettyViaCodec fn a
                pure case res of
                  AnyDoc ds -> ds
                  x -> [renderSmartDoc x]
            )
            diag
      pure $ AnyDoc res
    ProductCodec order diag -> do
      res <-
        getAp $
          diagramFold
            order
            ( \a -> Ap do
                res <- prettyViaCodec fn a
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
      alreadyMember <- asks (Aeson.member k)
      unless alreadyMember do
        tell [(k, prettyViaCodec fn ca)]
      pure . Doc $ "<" <> PP.pretty n <> ">"
    DimapCodec _ _ c ->
      prettyViaCodec fn c
    ElementCodec c ->
      fn c
    AnnotateCodec s c -> do
      res <- prettyViaCodec fn c
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
      res <- prettyViaCodec prettyViaValueCodec a
      doc $ "manyOf" PP.<+> renderSmartDoc res
    MapOfCodec a -> do
      res <- prettyViaCodec prettyViaValueCodec a
      doc $ "mapOf" PP.<+> renderSmartDoc res
    ArrayCodec a -> do
      res <- prettyViaCodec prettyViaArrayCodec a
      doc $ "array" PP.<> PP.line PP.<> renderSmartDoc res
    ObjectCodec a -> do
      res <- prettyViaCodec prettyViaObjectCodec a
      doc $ "object" PP.<> PP.line PP.<> renderSmartDoc res
    ExactValueCodec e ->
      doc $ PP.pretty . Text.decodeUtf8 $ Aeson.encode e

  prettyViaObjectCodec :: forall t. ObjectC ctx Doc t -> Pretty
  prettyViaObjectCodec = \case
    EmptyObjectCodec -> pure "<empty>"
    FieldCodec k cd -> do
      res <- prettyViaCodec prettyViaValueCodec cd
      doc $ PP.hsep [PP.pretty (Aeson.toString k), ":", renderSmartDoc res]

  prettyViaArrayCodec :: forall t. ArrayC ctx Doc t -> Pretty
  prettyViaArrayCodec = \case
    EmptyArrayCodec -> pure "<empty>"
    SingleCodec cd ->
      prettyViaCodec prettyViaValueCodec cd

debugCodec :: Codec ValueC ctx Doc a -> IO ()
debugCodec c = do
  putStrLn "------"
  let (res, deps) = runWriter $ runReaderT (runPrettyM $ prettyCodec c) Aeson.empty
  PP.putDoc (renderSmartDoc res <> PP.line)
  putStrLn "------"
  go (Aeson.fromList $ map (\(a, _) -> (a, ())) deps) deps
  putStrLn "------"
 where
  go keys = \case
    [] -> pure ()
    (k, v) : xs -> do
      let (res, deps) = runWriter $ runReaderT (runPrettyM v) keys
      PP.putDoc $ "<" <> PP.pretty (Aeson.toText k) <> ">" <> " ::= " <> PP.nest 2 (renderSmartDoc res) <> PP.line
      go (keys <> Aeson.fromList (map (\(a, _) -> (a, ())) deps)) (deps <> xs)

newtype PrettyM a = PrettyM {runPrettyM :: ReaderT (Aeson.KeyMap ()) (Writer [(Aeson.Key, Pretty)]) a}
  deriving newtype (Functor, Applicative, Monad, MonadWriter [(Aeson.Key, Pretty)], MonadReader (Aeson.KeyMap ()))

type Pretty = PrettyM SmartDoc

type Doc = PP.Doc Void

data SmartDoc
  = Doc (PP.Doc Void)
  | AnyDoc [PP.Doc Void]
  | AllDoc [PP.Doc Void]

instance IsString SmartDoc where
  fromString = Doc . fromString

renderSmartDoc :: SmartDoc -> PP.Doc Void
renderSmartDoc = \case
  Doc d -> d
  AnyDoc ds ->
    PP.vcat ["+ " <> PP.nest 2 d | d <- ds]
  AllDoc ds ->
    PP.vcat ["* " <> PP.nest 2 d | d <- ds]

doc :: PP.Doc Void -> PrettyM SmartDoc
doc = pure . Doc
