{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
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
  Doc,
  cunfold,
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

  -- helpers
  WithError (..),
  withError,
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
import Data.String
import qualified Data.Text.Lazy.Encoding as Text
import GHC.TypeLits
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

data Ref (s :: Symbol) = KnownSymbol s => Ref

class Def (s :: Symbol) e ctx a | ctx s -> e a where
  unref :: Codec e ctx a

type Doc = PP.Doc Void

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
  DimapCodec
    :: (b -> Either String a)
    -> (a -> Either String b)
    -> Codec e ctx a
    -> Codec e ctx b
  -- | The reference codec.
  -- The trick here is to ensure that there exist only one Codec per context and name.
  ReferenceCodec
    :: (Def s e' ctx a)
    => Ref s
    -> (Codec e' ctx a -> Codec e ctx a)
    -> Codec e ctx a
  ElementCodec
    :: e ctx a
    -> Codec e ctx a
  -- | Adding a line of documentation to the codec.
  DocumentationCodec
    :: Doc
    -> Codec e ctx a
    -> Codec e ctx a
  ExampleCodec
    :: a
    -> (a -> Doc)
    -> Codec e ctx a
    -> Codec e ctx a

cunfold :: (forall b. e ctx b -> Codec e' ctx b) -> Codec e ctx a -> Codec e' ctx a
cunfold fn = \case
  BrokenCodec -> BrokenCodec
  SumCodec order diag ->
    SumCodec order (bmap (cunfold fn) diag)
  ProductCodec order diag ->
    ProductCodec
      order
      (bmap (cunfold fn) diag)
  DimapCodec to from c ->
    DimapCodec to from (cunfold fn c)
  ReferenceCodec r f ->
    ReferenceCodec r (cunfold fn . f)
  ElementCodec c -> fn c
  DocumentationCodec dc c ->
    DocumentationCodec dc (cunfold fn c)
  ExampleCodec e tdoc c ->
    ExampleCodec e tdoc (cunfold fn c)

data ValueCodec ctx a where
  StringCodec :: ValueCodec ctx Text.Text
  BoolCodec :: ValueCodec ctx Bool
  NumberCodec :: ValueCodec ctx Scientific
  ManyOfCodec :: Codec ValueCodec ctx a -> ValueCodec ctx (V.Vector a)
  MapOfCodec :: Codec ValueCodec ctx a -> ValueCodec ctx [(Key, a)]
  ArrayCodec :: Codec ArrayCodec ctx a -> ValueCodec ctx a
  ObjectCodec :: Codec ObjectCodec ctx a -> ValueCodec ctx a
  ExactValueCodec :: Value -> ValueCodec ctx ()

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
  ReferenceCodec (Ref :: Ref s) f ->
    destroy fn (f (unref @s))
  ElementCodec c ->
    fn c
  DocumentationCodec _ c ->
    destroy fn c
  ExampleCodec _ _ c ->
    destroy fn c

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
  ReferenceCodec (Ref :: Ref s) f ->
    build fn (f (unref @s))
  ElementCodec c ->
    fn c
  DocumentationCodec _ c ->
    build fn c
  ExampleCodec _ _ c ->
    build fn c

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
    MapOfCodec ca -> \case
      Object mp -> mapM (\(k, v) -> (k,) <$> runReaderT (build parseJSONViaValueCodec ca) v) $ Aeson.toList mp
      v -> typeMismatch "Object" v
    ArrayCodec ca ->
      runArrayParser "no-name" (build parseJSONViaArrayCodec ca)
    ObjectCodec ca ->
      runObjectParser "no-name" (build parseJSONViaObjectCodec ca)
    ExactValueCodec expected -> \actual ->
      unless (expected == actual) do
        fail $ "expected " ++ show expected ++ ", but encountered " ++ show actual

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

instance IsString (Codec ValueCodec ctx ()) where
  fromString = ElementCodec . ExactValueCodec . fromString

newtype PrettyM a = PrettyM {runPrettyM :: ReaderT (Aeson.KeyMap ()) (Writer [(Key, Pretty)]) a}
  deriving newtype (Functor, Applicative, Monad, MonadWriter [(Key, Pretty)], MonadReader (Aeson.KeyMap ()))

newtype WithError a = WithError {runWithError :: Either String a}
  deriving newtype (Functor, Applicative, Alternative, MonadPlus, Monad)

instance MonadFail WithError where
  fail = WithError . Left

withError :: (String -> a) -> WithError a -> a
withError hdl = either hdl id . runWithError

type Pretty = PrettyM SmartDoc

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
      let ca = f (unref @s)
      alreadyMember <- asks (Aeson.member k)
      unless alreadyMember do
        tell [(k, prettyViaCodec fn ca)]
      pure . Doc $ "<" <> PP.pretty n <> ">"
    DimapCodec _ _ c ->
      prettyViaCodec fn c
    ElementCodec c ->
      fn c
    DocumentationCodec s c -> do
      res <- prettyViaCodec fn c
      pure . Doc $ renderSmartDoc res <> PP.line <> "-- " <> s
    ExampleCodec a f c -> do
      res <- prettyViaCodec fn c
      pure . Doc $ renderSmartDoc res <> PP.line <> "! " <> f a

  prettyViaValueCodec :: forall t. ValueCodec ctx t -> Pretty
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

  prettyViaObjectCodec :: forall t. ObjectCodec ctx t -> Pretty
  prettyViaObjectCodec = \case
    EmptyObjectCodec -> pure "<empty>"
    FieldCodec k cd -> do
      res <- prettyViaCodec prettyViaValueCodec cd
      doc $ PP.hsep [PP.pretty (Aeson.toString k), ":", renderSmartDoc res]

  prettyViaArrayCodec :: forall t. ArrayCodec ctx t -> Pretty
  prettyViaArrayCodec = \case
    EmptyArrayCodec -> pure "<empty>"
    SingleCodec cd ->
      prettyViaCodec prettyViaValueCodec cd

debugCodec :: Codec ValueCodec ctx a -> IO ()
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
