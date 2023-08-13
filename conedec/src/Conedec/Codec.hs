{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Conedec.Codec (
  Codec (..),
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
import Data.String

-- aeson
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Key as Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types hiding (object, (.:))

-- vector
import qualified Data.Vector as V

-- barbies
import Barbies

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
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

type ErrorMsg = String

{- | A redesign of the codec.

The codec contains of three type variables context @ctx@, encoder @e@ and type @t@.
-}
data Codec ctx e a where
  -- | All codecs can be created in a broken state, to ease development.
  -- This is easy to check for though.
  Broken
    :: Codec ctx e a
  -- | A Sum of different codec, choosing the first matching when parsing.
  Sum
    :: (IsColimit a)
    => DiagramOrder a
    -> Diagram a (Codec ctx e)
    -> Codec ctx e a
  -- | A Product of different codec, where the order of the elements is decided by the order.
  Product
    :: (IsLimit a)
    => DiagramOrder a
    -> Diagram a (Codec ctx e)
    -> Codec ctx e a
  -- | Adding a line of documentation to the codec.
  Documentation
    :: Text.Text
    -> Codec ctx e a
    -> Codec ctx e a
  Dimap
    :: (b -> Either ErrorMsg a)
    -> (a -> Either ErrorMsg b)
    -> Codec ctx e a
    -> Codec ctx e b
  Reference
    :: ctx a
    -> Codec ctx e a
  Element
    :: e ctx a
    -> Codec ctx e a

data ValueCodec ctx a where
  NullCodec :: ValueCodec ctx ()
  StringCodec :: ValueCodec ctx Text.Text
  BoolCodec :: ValueCodec ctx Bool
  NumberCodec :: ValueCodec ctx Scientific
  ManyOfCodec :: Codec ctx ValueCodec a -> ValueCodec ctx (V.Vector a)
  ArrayCodec :: Codec ctx ArrayCodec a -> ValueCodec ctx a
  ObjectCodec :: Codec ctx ObjectCodec a -> ValueCodec ctx a

data ObjectCodec ctx a where
  EmptyObjectCodec :: ObjectCodec ctx ()
  FieldCodec
    :: Key
    -> Codec ctx ValueCodec a
    -> ObjectCodec ctx a

data ArrayCodec ctx a where
  EmptyArrayCodec :: ArrayCodec ctx ()
  SingleCodec
    :: Codec ctx ValueCodec a
    -> ArrayCodec ctx a

destroy :: (MonadFail m, Monoid x) => (forall t. e ctx t -> t -> m x) -> Codec ctx e a -> a -> m x
destroy fn = \case
  Broken ->
    const $ fail "broken"
  Sum _ diag ->
    cofactor (bmap (Op . destroy fn) diag)
  Product order diag ->
    getAp . foldOfLimit order (\c -> Ap . destroy fn c) diag
  Dimap to _ c ->
    either fail pure . to >=> destroy fn c
  Documentation _ c ->
    destroy fn c
  Reference _ ->
    undefined
  Element c ->
    fn c

build :: (Alternative m, MonadFail m) => (forall t. e ctx t -> m t) -> Codec ctx e a -> m a
build fn = \case
  Broken ->
    fail "broken"
  Sum order diag ->
    altOfColimit order . bmap (build fn) $ diag
  Product order diag ->
    apOfLimit order . bmap (build fn) $ diag
  Dimap _ from c ->
    build fn c >>= either fail pure . from
  Documentation _ c ->
    build fn c
  Reference _ ->
    undefined
  Element c ->
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

toJSONViaCodec :: forall m ctx a. MonadFail m => Codec ctx ValueCodec a -> a -> m Value
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

parseJSONViaCodec :: forall ctx a. Codec ctx ValueCodec a -> Value -> Parser a
parseJSONViaCodec c =
  runReaderT $ build parseJSONViaValueCodec c
 where
  parseJSONViaValueCodec :: ValueCodec ctx t -> ReaderT Value Parser t
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
      Array arr -> V.mapM (parseJSONViaCodec ca) arr
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

prettyCodec :: Codec ctx ValueCodec a -> PP.Doc ann
prettyCodec = prettyViaCodec prettyViaValueCodec
 where
  prettyViaCodec :: (forall b. e ctx b -> PP.Doc ann) -> Codec ctx e t -> PP.Doc ann
  prettyViaCodec fn = \case
    Broken ->
      ">broken<"
    Sum order diag ->
      "any"
        PP.<+> (PP.line <> PP.vcat (diagramFold order (\a -> ["+ " <> PP.nest 2 (prettyViaCodec fn a)]) diag))
    Product order diag ->
      "all"
        PP.<+> (PP.line <> PP.vcat (diagramFold order (\a -> ["* " <> PP.nest 2 (prettyViaCodec fn a)]) diag))
    Documentation s c ->
      "-- " <> PP.pretty s <> PP.line <> prettyViaCodec fn c
    Reference _ ->
      undefined
    Dimap _ _ c ->
      prettyViaCodec fn c
    Element c ->
      fn c

  prettyViaValueCodec :: ValueCodec e t -> PP.Doc ann
  prettyViaValueCodec = \case
    ManyOfCodec a ->
      "manyOf" PP.<+> prettyViaCodec prettyViaValueCodec a
    StringCodec ->
      "<string>"
    NumberCodec ->
      "<number>"
    NullCodec ->
      "null"
    BoolCodec ->
      "<bool>"
    ArrayCodec a ->
      "array" PP.<+> prettyViaCodec prettyViaArrayCodec a
    ObjectCodec a ->
      "object" PP.<+> prettyViaCodec prettyViaObjectCodec a

  prettyViaObjectCodec :: ObjectCodec e b -> PP.Doc ann
  prettyViaObjectCodec = \case
    EmptyObjectCodec -> "<empty>"
    FieldCodec k cd ->
      PP.hsep
        [PP.pretty (Aeson.toString k), ":", PP.nest 2 (prettyViaCodec prettyViaValueCodec cd)]

  prettyViaArrayCodec :: ArrayCodec e b -> PP.Doc ann
  prettyViaArrayCodec = \case
    EmptyArrayCodec -> "<empty>"
    SingleCodec cd ->
      prettyViaCodec prettyViaValueCodec cd

debugCodec :: Codec ctx ValueCodec a -> IO ()
debugCodec c = do
  putStrLn "------"
  PP.putDoc $ prettyCodec c
  putStrLn ""
  putStrLn "------"
