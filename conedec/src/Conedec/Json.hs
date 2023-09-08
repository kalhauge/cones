{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
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
{-# LANGUAGE TupleSections #-}

module Conedec.Json (
  ValueC (..),
  ArrayC (..),
  ObjectC (..),
  toJSONViaCodec,
  parseJSONViaCodec,
  toEncodingViaCodec,
  -- Error handeling
  WithError (..),
  withError,
) where

-- base
import Control.Applicative
import Data.Foldable
import Data.String

-- mtl
import Control.Monad.Reader
import Control.Monad.State

-- aeson
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Encoding as Aeson
import qualified Data.Aeson.Encoding as Aseon
import qualified Data.Aeson.KeyMap as Aeson
import qualified Data.Aeson.Types as Aeson

-- scientific
import Data.Scientific

-- text
import qualified Data.Text as Text

-- vector
import qualified Data.Vector as V

-- condec
import Conedec.Codec

data ValueC ctx ann a where
  StringCodec :: ValueC ctx ann Text.Text
  BoolCodec :: ValueC ctx ann Bool
  NumberCodec :: ValueC ctx ann Scientific
  ManyOfCodec :: Codec ValueC ctx ann a -> ValueC ctx ann (V.Vector a)
  MapOfCodec :: Codec ValueC ctx ann a -> ValueC ctx ann [(Aeson.Key, a)]
  ArrayCodec :: Codec ArrayC ctx ann a -> ValueC ctx ann a
  ObjectCodec :: Codec ObjectC ctx ann a -> ValueC ctx ann a
  ExactValueCodec :: Aeson.Value -> ValueC ctx ann ()

data ObjectC ctx ann a where
  EmptyObjectCodec :: ObjectC ctx ann ()
  FieldCodec
    :: Aeson.Key
    -> Codec ValueC ctx ann a
    -> ObjectC ctx ann a

data ArrayC ctx ann a where
  EmptyArrayCodec :: ArrayC ctx ann ()
  SingleCodec
    :: Codec ValueC ctx ann a
    -> ArrayC ctx ann a

toJSONViaCodec
  :: forall ctx ann m a
   . MonadFail m
  => Codec ValueC ctx ann a
  -> a
  -> m Aeson.Value
toJSONViaCodec c a = do
  expectOne $ destroy (\e t -> One <$> toJSONViaValueC e t) c a
 where
  toJSONViaValueC :: ValueC ctx ann t -> t -> m Aeson.Value
  toJSONViaValueC = \case
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
    MapOfCodec oc ->
      fmap (Aeson.Object . Aeson.fromList) . mapM (\(key, x) -> (key,) <$> toJSONViaCodec oc x)
    ArrayCodec oc ->
      fmap Aeson.Array . destroy toJSONViaArrayCodec oc
    ExactValueCodec e ->
      const $ pure e

  toJSONViaObjectCodec :: ObjectC ctx ann t -> t -> m [Aeson.Pair]
  toJSONViaObjectCodec = \case
    EmptyObjectCodec -> \_ ->
      pure []
    FieldCodec name ca -> \a' ->
      pure $ (name,) <$> toJSONViaCodec ca a'

  toJSONViaArrayCodec :: ArrayC ctx ann t -> t -> m Aeson.Array
  toJSONViaArrayCodec = \case
    EmptyArrayCodec -> \_ ->
      pure mempty
    SingleCodec ca ->
      fmap V.singleton . toJSONViaCodec ca

toEncodingViaCodec
  :: forall ctx ann m a
   . MonadFail m
  => Codec ValueC ctx ann a
  -> a
  -> m Aeson.Encoding
toEncodingViaCodec c a = do
  expectOne $ destroy (\e t -> One <$> toEncodingViaValueC e t) c a
 where
  toEncodingViaValueC :: ValueC ctx ann t -> t -> m Aeson.Encoding
  toEncodingViaValueC = \case
    StringCodec ->
      pure . Aeson.text
    BoolCodec ->
      pure . Aeson.bool
    NumberCodec ->
      pure . Aeson.scientific
    ObjectCodec oc ->
      fmap Aeson.pairs . destroy toEncodingViaObjectCodec oc
    ManyOfCodec oc -> \lst -> do
      es <- V.mapM (toEncodingViaCodec oc) lst
      pure (Aeson.list id (V.toList es))
    MapOfCodec oc ->
      fmap (Aeson.pairs . fold) . mapM (\(key, x) -> Aeson.pair key <$> toEncodingViaCodec oc x)
    ArrayCodec oc ->
      fmap (Aeson.list id) . destroy toEncodingViaArrayCodec oc
    ExactValueCodec e ->
      const $ pure (Aeson.toEncoding e)

  toEncodingViaObjectCodec :: ObjectC ctx ann t -> t -> m Aeson.Series
  toEncodingViaObjectCodec = \case
    EmptyObjectCodec -> \_ ->
      pure mempty
    FieldCodec name ca ->
      fmap (Aeson.pair name) . toEncodingViaCodec ca

  -- todo: this could be implemented faster if needed
  toEncodingViaArrayCodec :: ArrayC ctx ann t -> t -> m [Aseon.Encoding]
  toEncodingViaArrayCodec = \case
    EmptyArrayCodec -> \_ ->
      pure mempty
    SingleCodec ca ->
      fmap pure . toEncodingViaCodec ca

parseJSONViaCodec
  :: forall ctx ann a
   . Codec ValueC ctx ann a
  -> Aeson.Value
  -> Aeson.Parser a
parseJSONViaCodec c =
  runReaderT $ build parseJSONViaValueC c
 where
  parseJSONViaValueC
    :: forall t
     . ValueC ctx ann t
    -> ReaderT Aeson.Value Aeson.Parser t
  parseJSONViaValueC cd = ReaderT $ case cd of
    NumberCodec -> \case
      Aeson.Number s -> pure s
      a -> Aeson.typeMismatch "Number" a
    StringCodec -> \case
      Aeson.String txt -> pure txt
      v -> Aeson.typeMismatch "String" v
    BoolCodec -> \case
      Aeson.Bool b -> pure b
      v -> Aeson.typeMismatch "Bool" v
    ManyOfCodec ca -> \case
      Aeson.Array arr -> V.mapM (runReaderT $ build parseJSONViaValueC ca) arr
      v -> Aeson.typeMismatch "Array" v
    MapOfCodec ca -> \case
      Aeson.Object mp -> mapM (\(k, v) -> (k,) <$> runReaderT (build parseJSONViaValueC ca) v) $ Aeson.toList mp
      v -> Aeson.typeMismatch "Object" v
    ArrayCodec ca ->
      runArrayParser "no-name" (build parseJSONViaArrayCodec ca)
    ObjectCodec ca ->
      runObjectParser "no-name" (build parseJSONViaObjectCodec ca)
    ExactValueCodec expected -> \actual ->
      unless (expected == actual) do
        fail $ "expected " ++ show expected ++ ", but encountered " ++ show actual

  parseJSONViaObjectCodec :: ObjectC ctx ann t -> ObjectParser t
  parseJSONViaObjectCodec = \case
    EmptyObjectCodec ->
      pure ()
    FieldCodec name ca ->
      mkObjectParser (parseJSONViaCodec ca) name

  parseJSONViaArrayCodec :: ArrayC ctx ann t -> ArrayParser t
  parseJSONViaArrayCodec = \case
    EmptyArrayCodec ->
      pure ()
    SingleCodec ca ->
      mkArrayParser (parseJSONViaCodec ca)

instance IsString (Codec ValueC ctx ann ()) where
  fromString = ElementCodec . ExactValueCodec . fromString

newtype ObjectParser a = ObjectParser (Aeson.Object -> Aeson.Parser a)
  deriving (Functor)
  deriving (Applicative, Alternative, Monad, MonadFail) via (ReaderT Aeson.Object Aeson.Parser)

runObjectParser :: String -> ObjectParser t -> Aeson.Value -> Aeson.Parser t
runObjectParser n (ObjectParser f) = Aeson.withObject n f

mkObjectParser :: (Aeson.Value -> Aeson.Parser t) -> Aeson.Key -> ObjectParser t
mkObjectParser fn key = ObjectParser \obj ->
  case Aeson.lookup key obj of
    Just val -> fn val Aeson.<?> Aeson.Key key
    Nothing -> fail "not could not find element" Aeson.<?> Aeson.Key key
newtype ArrayParser a = ArrayParser (Aeson.Array -> Int -> Aeson.Parser (a, Int))
  deriving (Functor)
  deriving (Applicative, Alternative, Monad, MonadFail) via (ReaderT Aeson.Array (StateT Int Aeson.Parser))

mkArrayParser :: (Aeson.Value -> Aeson.Parser t) -> ArrayParser t
mkArrayParser fn = ArrayParser \arr i ->
  case arr V.!? i of
    Just val -> (,i + 1) <$> (fn val Aeson.<?> Aeson.Index i)
    Nothing -> fail "not enough elements in the array"

runArrayParser :: String -> ArrayParser t -> Aeson.Value -> Aeson.Parser t
runArrayParser n (ArrayParser f) = Aeson.withArray n \arr ->
  fst <$> f arr 0

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

newtype WithError a = WithError {runWithError :: Either String a}
  deriving newtype (Functor, Applicative, Alternative, MonadPlus, Monad)

instance MonadFail WithError where
  fail = WithError . Left

withError :: (String -> a) -> WithError a -> a
withError hdl = either hdl id . runWithError
