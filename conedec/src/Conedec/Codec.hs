{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Conedec.Codec (
  Codec (..),
  Ref (..),
  Def (..),
  destroy,
  build,
  ValueCodec (..),
  ArrayCodec (..),
  ObjectCodec (..),
  toJSONViaCodec,
  parseJSONViaCodec,
  prettyCodec,
  debugCodec,
  -- parseJSONViaCodec,
  -- toJSONViaCodec,
) where

-- base
import Control.Applicative
import Data.Functor.Contravariant
import Data.Monoid hiding (Product, Sum)
import Data.Void

-- aeson
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Key as Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types hiding (object, (.:))

-- vector
import qualified Data.Vector as V

-- barbies
import Barbies hiding (Void)

-- mtl
import Control.Monad.Reader
import Control.Monad.State.Strict (StateT (..))

-- text
import qualified Data.Text as Text

-- cones
import Data.Cone

-- scientific
import Data.Scientific hiding (scientific)

-- prettyprinter

import Control.Monad.Writer
import qualified Data.Aeson.KeyMap as Aeson
import Data.Proxy
import GHC.TypeLits
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

data Ref (s :: Symbol) = Ref

class Def (s :: Symbol) e ctx a | ctx s -> e a where
  unref :: Codec e ctx a

{- | A redesign of the codec.

The codec contains of three type variables context @ctx@, encoder @e@ and type @t@.
-}
data Codec e ctx a where
  -- | All codecs can be created in a broken state, to ease development.
  -- This is easy to check for though.
  BrokenCodec
    :: Codec e ctx a
  -- | A Sum of different codec, choosing the first matching when parsing.
  SumCodec
    :: (IsColimit a)
    => DiagramOrder a
    -> Diagram a (Codec e ctx)
    -> Codec e ctx a
  -- | A Product of different codec, where the order of the elements is decided by the order.
  ProductCodec
    :: (IsLimit a)
    => DiagramOrder a
    -> Diagram a (Codec e ctx)
    -> Codec e ctx a
  -- | Adding a line of documentation to the codec.
  DocumentationCodec
    :: Text.Text
    -> Codec e ctx a
    -> Codec e ctx a
  DimapCodec
    :: (b -> Either String a)
    -> (a -> Either String b)
    -> Codec e ctx a
    -> Codec e ctx b
  -- | The reference codec.
  -- The trick here is to ensure that there exist only one Codec per context and name.
  ReferenceCodec
    :: (KnownSymbol s, Def s e ctx a)
    => Ref s
    -> Codec e ctx a
  ElementCodec
    :: e ctx a
    -> Codec e ctx a

data ValueCodec ctx a where
  NullCodec :: ValueCodec ctx ()
  StringCodec :: ValueCodec ctx Text.Text
  BoolCodec :: ValueCodec ctx Bool
  NumberCodec :: ValueCodec ctx Scientific
  ManyOfCodec :: Codec ValueCodec ctx a -> ValueCodec ctx (V.Vector a)
  ArrayCodec :: Codec ArrayCodec ctx a -> ValueCodec ctx a
  ObjectCodec :: Codec ObjectCodec ctx a -> ValueCodec ctx a

data ObjectCodec ctx a where
  EmptyObjectCodec :: ObjectCodec ctx ()
  FieldCodec
    :: Key
    -> Codec ValueCodec ctx a
    -> ObjectCodec ctx a

data ArrayCodec ctx a where
  EmptyArrayCodec :: ArrayCodec ctx ()
  SingleCodec
    :: Codec ValueCodec ctx a
    -> ArrayCodec ctx a

destroy :: forall ctx e a m x. (MonadFail m, Monoid x) => (forall t. e ctx t -> t -> m x) -> Codec e ctx a -> a -> m x
destroy fn = \case
  BrokenCodec ->
    const $ fail "broken"
  SumCodec _ diag ->
    cofactor (bmap (Op . destroy fn) diag)
  ProductCodec order diag ->
    getAp . foldOfLimit order (\c -> Ap . destroy fn c) diag
  DimapCodec to _ c ->
    either fail pure . to >=> destroy fn c
  DocumentationCodec _ c ->
    destroy fn c
  ReferenceCodec (Ref :: Ref s) ->
    destroy fn (unref @s @e @ctx)
  ElementCodec c ->
    fn c

build :: forall ctx e m a. (Alternative m, MonadFail m) => (forall t. e ctx t -> m t) -> Codec e ctx a -> m a
build fn = \case
  BrokenCodec ->
    fail "broken"
  SumCodec order diag ->
    altOfColimit order . bmap (build fn) $ diag
  ProductCodec order diag ->
    apOfLimit order . bmap (build fn) $ diag
  DimapCodec _ from c ->
    build fn c >>= either fail pure . from
  DocumentationCodec _ c ->
    build fn c
  ReferenceCodec (Ref :: Ref s) ->
    build fn (unref @s @e @ctx)
  ElementCodec c ->
    fn c

data ZeroOrMore a = Zero | One a | More
  deriving (Show)

instance Semigroup (ZeroOrMore a) where
  Zero <> a = a
  More <> _ = More
  x <> a = case a of
    Zero -> x
    _ -> More

instance Monoid (ZeroOrMore a) where
  mempty = Zero

expectOne :: MonadFail m => m (ZeroOrMore a) -> m a
expectOne fn =
  fn >>= \case
    One a -> pure a
    Zero -> fail "expected at least one element"
    More -> fail "expected no more than one element"

toJSONViaCodec :: forall ctx m a. MonadFail m => Codec ValueCodec ctx a -> a -> m Value
toJSONViaCodec c a = do
  expectOne $ destroy (\e t -> One <$> toJSONViaValueCodec e t) c a
 where
  toJSONViaValueCodec :: ValueCodec ctx t -> t -> m Value
  toJSONViaValueCodec = \case
    NullCodec -> \() ->
      pure Aeson.Null
    StringCodec ->
      pure . Aeson.String
    BoolCodec ->
      pure . Aeson.Bool
    NumberCodec ->
      pure . Aeson.Number
    ObjectCodec oc ->
      fmap Aeson.object . destroy toJSONViaObjectCodec oc
    ManyOfCodec oc ->
      fmap Aeson.Array . V.mapM (toJSONViaCodec oc)
    ArrayCodec oc ->
      fmap Aeson.Array . destroy toJSONViaArrayCodec oc

  toJSONViaObjectCodec :: ObjectCodec ctx t -> t -> m [Pair]
  toJSONViaObjectCodec = \case
    EmptyObjectCodec -> \_ ->
      pure []
    FieldCodec name ca -> \a' ->
      pure $ (name,) <$> toJSONViaCodec ca a'

  toJSONViaArrayCodec :: ArrayCodec ctx t -> t -> m Array
  toJSONViaArrayCodec = \case
    EmptyArrayCodec -> \_ ->
      pure mempty
    SingleCodec ca ->
      fmap V.singleton . toJSONViaCodec ca

parseJSONViaCodec :: forall ctx a. Codec ValueCodec ctx a -> Value -> Parser a
parseJSONViaCodec c =
  runReaderT $ build parseJSONViaValueCodec c
 where
  parseJSONViaValueCodec :: forall t. ValueCodec ctx t -> ReaderT Value Parser t
  parseJSONViaValueCodec cd = ReaderT $ case cd of
    NullCodec -> \case
      Null -> pure ()
      a -> typeMismatch "Null" a
    NumberCodec -> \case
      Number s -> pure s
      a -> typeMismatch "Number" a
    StringCodec -> \case
      String txt -> pure txt
      v -> typeMismatch "String" v
    BoolCodec -> \case
      Bool b -> pure b
      v -> typeMismatch "Bool" v
    ManyOfCodec ca -> \case
      Array arr -> V.mapM (runReaderT $ build parseJSONViaValueCodec ca) arr
      v -> typeMismatch "Array" v
    ArrayCodec ca ->
      runArrayParser "no-name" (build parseJSONViaArrayCodec ca)
    ObjectCodec ca ->
      runObjectParser "no-name" (build parseJSONViaObjectCodec ca)

  parseJSONViaObjectCodec :: ObjectCodec ctx t -> ObjectParser t
  parseJSONViaObjectCodec = \case
    EmptyObjectCodec ->
      pure ()
    FieldCodec name ca ->
      mkObjectParser (parseJSONViaCodec ca) name

  parseJSONViaArrayCodec :: ArrayCodec ctx t -> ArrayParser t
  parseJSONViaArrayCodec = \case
    EmptyArrayCodec ->
      pure ()
    SingleCodec ca ->
      mkArrayParser (parseJSONViaCodec ca)

newtype ObjectParser a = ObjectParser (Object -> Parser a)
  deriving (Functor)
  deriving (Applicative, Alternative, Monad, MonadFail) via (ReaderT Object Parser)

runObjectParser :: String -> ObjectParser t -> Value -> Parser t
runObjectParser n (ObjectParser f) = withObject n f

mkObjectParser :: (Value -> Parser t) -> Key -> ObjectParser t
mkObjectParser fn key = ObjectParser \obj ->
  case KM.lookup key obj of
    Just val -> fn val Aeson.<?> Key key
    Nothing -> fail "not could not find element" Aeson.<?> Key key
newtype ArrayParser a = ArrayParser (Array -> Int -> Parser (a, Int))
  deriving (Functor)
  deriving (Applicative, Alternative, Monad, MonadFail) via (ReaderT Array (StateT Int Parser))

mkArrayParser :: (Value -> Parser t) -> ArrayParser t
mkArrayParser fn = ArrayParser \arr i ->
  case arr V.!? i of
    Just val -> (,i + 1) <$> (fn val Aeson.<?> Index i)
    Nothing -> fail "not enough elements in the array"

runArrayParser :: String -> ArrayParser t -> Value -> Parser t
runArrayParser n (ArrayParser f) = withArray n \arr ->
  fst <$> f arr 0

{- $prettyprinter
Here:
-}

type Pretty = Writer (Aeson.KeyMap (PP.Doc Void)) (PP.Doc Void)

prettyCodec :: forall ctx a. Codec ValueCodec ctx a -> Pretty
prettyCodec = prettyViaCodec prettyViaValueCodec
 where
  prettyViaCodec :: (forall b. e ctx b -> Pretty) -> Codec e ctx t -> Pretty
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
                pure ["+ " <> PP.nest 2 res]
            )
            diag
      pure $ "any" PP.<+> (PP.line <> PP.vcat res)
    ProductCodec order diag -> do
      res <-
        getAp $
          diagramFold
            order
            ( \a -> Ap do
                res <- prettyViaCodec fn a
                pure ["* " <> PP.nest 2 res]
            )
            diag
      pure $ "all" PP.<+> (PP.line <> PP.vcat res)
    DocumentationCodec s c -> do
      res <- prettyViaCodec fn c
      pure $ "-- " <> PP.pretty s <> PP.line <> res
    ReferenceCodec (Ref :: Ref s) -> do
      -- let (n, ca) = f ctx
      -- x <- prettyViaCodec fn ca
      -- tell (Aeson.singleton (Aeson.fromText n) x)
      pure $ "<" <> PP.pretty (symbolVal (Proxy :: Proxy s)) <> ">"
    DimapCodec _ _ c ->
      prettyViaCodec fn c
    ElementCodec c ->
      fn c

  prettyViaValueCodec :: forall t. ValueCodec ctx t -> Pretty
  prettyViaValueCodec = \case
    StringCodec ->
      pure "<string>"
    NumberCodec ->
      pure "<number>"
    NullCodec ->
      pure "null"
    BoolCodec ->
      pure "<bool>"
    ManyOfCodec a -> do
      res <- prettyViaCodec prettyViaValueCodec a
      pure $ "manyOf" PP.<+> res
    ArrayCodec a -> do
      res <- prettyViaCodec prettyViaArrayCodec a
      pure $ "array" PP.<+> res
    ObjectCodec a -> do
      res <- prettyViaCodec prettyViaObjectCodec a
      pure $ "object" PP.<+> res

  prettyViaObjectCodec :: forall t. ObjectCodec ctx t -> Pretty
  prettyViaObjectCodec = \case
    EmptyObjectCodec -> pure "<empty>"
    FieldCodec k cd -> do
      res <- prettyViaCodec prettyViaValueCodec cd
      pure $ PP.hsep [PP.pretty (Aeson.toString k), ":", PP.nest 2 res]

  prettyViaArrayCodec :: forall t. ArrayCodec ctx t -> Pretty
  prettyViaArrayCodec = \case
    EmptyArrayCodec -> pure "<empty>"
    SingleCodec cd ->
      prettyViaCodec prettyViaValueCodec cd

debugCodec :: Codec ValueCodec ctx a -> IO ()
debugCodec c = do
  putStrLn "------"
  let (res, deps) = runWriter $ prettyCodec c
  forM_ deps \d ->
    PP.putDoc (d <> PP.line)
  putStrLn "------"
  PP.putDoc (res <> PP.line)
  putStrLn "------"
