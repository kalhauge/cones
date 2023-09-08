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
{-# LANGUAGE TypeApplications #-}

module Conedec.Json (
  ValueC (..),
  ArrayC (..),
  ObjectC (..),
  toJSONViaCodec,
  parseJSONViaCodec,
  toEncodingViaCodec,
  debugCodec,
  Doc,
  -- Error handeling
  WithError (..),
  withError,
) where

-- base
import Control.Applicative
import Data.Foldable
import Data.Proxy
import Data.String
import Data.Void
import GHC.TypeLits

-- mtl
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

-- aeson
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Encoding as Aeson
import qualified Data.Aeson.Encoding as Aseon
import qualified Data.Aeson.Key as Aeson
import qualified Data.Aeson.KeyMap as Aeson
import qualified Data.Aeson.Types as Aeson

-- cone
import Data.Cone

-- scientific
import Data.Scientific

-- text
import qualified Data.Text as Text
import qualified Data.Text.Lazy.Encoding as Text

-- vector
import qualified Data.Vector as V

-- prettyprinter
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

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

newtype PrettyM a = PrettyM {runPrettyM :: ReaderT (Aeson.KeyMap ()) (Writer [(Aeson.Key, Pretty)]) a}
  deriving newtype (Functor, Applicative, Monad, MonadWriter [(Aeson.Key, Pretty)], MonadReader (Aeson.KeyMap ()))

newtype WithError a = WithError {runWithError :: Either String a}
  deriving newtype (Functor, Applicative, Alternative, MonadPlus, Monad)

instance MonadFail WithError where
  fail = WithError . Left

withError :: (String -> a) -> WithError a -> a
withError hdl = either hdl id . runWithError

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
