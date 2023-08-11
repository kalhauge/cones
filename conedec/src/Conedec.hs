{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- |

Stability: experimental

A cone based Codec implementation.

Remaining things:

- [ ] Adding references and declarations
- [ ] Add ease of life improvements, autonaming fields and stuff.
- [ ] Adding documentation
-}
module Conedec where

-- base
import Control.Applicative
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Monoid

-- aeson
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Key as Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types hiding (object)

-- vector
import qualified Data.Vector as V

-- barbies
import Barbies

-- mtl
import Control.Monad.Reader

-- text
import qualified Data.Text as Text

-- cones
import Data.Cone

-- scientific
import Data.Scientific hiding (scientific)

-- prettyprinter

import Control.Monad.State.Strict (StateT (..))
import Control.Monad.Writer
import Data.Coerce
import Data.Functor.Compose
import Data.Kind
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP
import Prelude hiding (all)

type ErrorMsg = String

-- | The codec, used to implement `toJSON`, `fromJSON`, and `toEncoding`
data Codec t where
  -- | A codec that consumes everything and produces nothing.
  -- Should not be used in production
  BrokenCodec
    :: Codec t
  -- | A codec that only parses and produces @null@.
  NullCodec
    :: Codec ()
  -- | A codec that can be written as a string
  StringCodec
    :: Codec Text.Text
  -- | A codec that can be written as a bool
  BoolCodec
    :: Codec Bool
  -- | A codec of a sum of types.
  AnyOfCodec
    :: (IsColimit a)
    => DiagramOrder a
    -> Diagram a Codec
    -> Codec a
  -- | A codec that parses a an array of the same type
  ManyOfCodec
    :: Codec a
    -> Codec (V.Vector a)
  NumberCodec
    :: Codec Scientific
  -- | A codec that parses a product of types, as an fixed length array.
  ArrayCodec
    :: ArrayCodec a
    -> Codec a
  -- | A codec that parses an object.
  ObjectCodec
    :: ObjectCodec a
    -> Codec a
  DimapCodec
    :: (b -> Either ErrorMsg a)
    -> (a -> Either ErrorMsg b)
    -> Codec a
    -> Codec b
  DocCodec
    :: Text.Text
    -> Codec a
    -> Codec a

data ArrayCodec a where
  AllOfArrayCodec
    :: (IsLimit a)
    => DiagramOrder a
    -> Diagram a ArrayCodec
    -> ArrayCodec a
  AnyOfArrayCodec
    :: (IsColimit a)
    => DiagramOrder a
    -> Diagram a ArrayCodec
    -> ArrayCodec a
  DocArrayCodec
    :: Text.Text
    -> ArrayCodec a
    -> ArrayCodec a
  DimapArrayCodec
    :: (a -> Either ErrorMsg b)
    -> (b -> Either ErrorMsg a)
    -> ArrayCodec b
    -> ArrayCodec a
  ElementCodec
    :: Codec a
    -> ArrayCodec a
  EmptyArrayCodec
    :: ArrayCodec ()

data ObjectCodec a where
  AllOfObjectCodec
    :: (IsLimit a)
    => DiagramOrder a
    -> Diagram a ObjectCodec
    -> ObjectCodec a
  AnyOfObjectCodec
    :: (IsColimit a)
    => DiagramOrder a
    -> Diagram a ObjectCodec
    -> ObjectCodec a
  FieldCodec
    :: Key
    -> Codec a
    -> ObjectCodec a
  EmptyObjectCodec
    :: ObjectCodec ()
  BrokenObjectCodec
    :: ObjectCodec a
  DocObjectCodec
    :: Text.Text
    -> ObjectCodec a
    -> ObjectCodec a

toJSONViaCodec :: MonadFail m => Codec t -> t -> m Value
toJSONViaCodec = \case
  AnyOfCodec _ diag ->
    cofactor (bmap (Op . toJSONViaCodec) diag)
  ManyOfCodec c ->
    fmap Array . mapM (toJSONViaCodec c)
  ArrayCodec a ->
    fmap Array . toJSONArrayViaCodec a
  ObjectCodec oc ->
    fmap Aeson.object . toJSONObjectViaCodec oc
  NumberCodec ->
    pure . Aeson.Number
  DimapCodec to _ c ->
    either fail pure . to >=> toJSONViaCodec c
  BrokenCodec -> \_ ->
    fail "empty codec"
  NullCodec -> \case
    () -> pure Null
  StringCodec ->
    pure . String
  BoolCodec ->
    pure . Bool
  DocCodec _ c ->
    toJSONViaCodec c

toJSONArrayViaCodec :: MonadFail m => ArrayCodec t -> t -> m Array
toJSONArrayViaCodec = \case
  AllOfArrayCodec order diag ->
    getAp . foldOfLimit order (\o -> Ap . toJSONArrayViaCodec o) diag
  AnyOfArrayCodec _ diag ->
    cofactor . bmap (Op . toJSONArrayViaCodec) $ diag
  DocArrayCodec _ c ->
    toJSONArrayViaCodec c
  EmptyArrayCodec ->
    const (pure mempty)
  DimapArrayCodec to _ c ->
    either fail pure . to >=> toJSONArrayViaCodec c
  ElementCodec cd ->
    fmap V.singleton . toJSONViaCodec cd

toJSONObjectViaCodec :: MonadFail m => ObjectCodec t -> t -> m [Pair]
toJSONObjectViaCodec = \case
  AllOfObjectCodec order diag ->
    getAp . foldOfLimit order (\o -> Ap . toJSONObjectViaCodec o) diag
  AnyOfObjectCodec _ diag ->
    cofactor . bmap (Op . toJSONObjectViaCodec) $ diag
  FieldCodec name cd -> \t ->
    pure $ (name,) <$> toJSONViaCodec cd t
  DocObjectCodec _ cd ->
    toJSONObjectViaCodec cd
  EmptyObjectCodec ->
    const $ pure []
  BrokenObjectCodec ->
    const $ fail "broken codec"

parseJSONViaCodec :: forall t. Codec t -> Value -> Parser t
parseJSONViaCodec = \case
  AnyOfCodec order diag -> \v ->
    altOfColimit order . bmap (`parseJSONViaCodec` v) $ diag
  ManyOfCodec cd -> \case
    Array arr -> V.mapM (parseJSONViaCodec cd) arr
    v -> typeMismatch "Array" v
  ArrayCodec ad ->
    runArrayParser "no-name" (parseJSONArrayViaCodec ad)
  ObjectCodec ad ->
    runObjectParser "no-name" (parseJSONObjectViaCodec ad)
  BrokenCodec -> \_ ->
    fail "empty codec"
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
  DimapCodec _ from c ->
    either fail pure . from <=< parseJSONViaCodec c
  DocCodec _ c ->
    parseJSONViaCodec c

parseJSONObjectViaCodec :: ObjectCodec t -> ObjectParser t
parseJSONObjectViaCodec = \case
  AnyOfObjectCodec order diag ->
    altOfColimit order . bmap parseJSONObjectViaCodec $ diag
  AllOfObjectCodec order diag ->
    apOfLimit order . bmap parseJSONObjectViaCodec $ diag
  DocObjectCodec _ c ->
    parseJSONObjectViaCodec c
  EmptyObjectCodec ->
    pure ()
  BrokenObjectCodec ->
    fail "broken codec"
  FieldCodec k c ->
    mkObjectParser (parseJSONViaCodec c) k

newtype ObjectParser a = ObjectParser {unObjectParser :: Object -> Parser a}
  deriving (Functor)
  deriving (Applicative, Alternative, Monad, MonadFail) via (ReaderT Object Parser)

runObjectParser :: String -> ObjectParser t -> Value -> Parser t
runObjectParser n (ObjectParser f) = withObject n f

mkObjectParser :: (Value -> Parser t) -> Key -> ObjectParser t
mkObjectParser fn key = ObjectParser \obj ->
  case KM.lookup key obj of
    Just val -> fn val Aeson.<?> Key key
    Nothing -> fail "not could not find element" Aeson.<?> Key key

parseJSONArrayViaCodec :: ArrayCodec t -> ArrayParser t
parseJSONArrayViaCodec = \case
  AllOfArrayCodec order diag ->
    apOfLimit order . bmap parseJSONArrayViaCodec $ diag
  AnyOfArrayCodec order diag ->
    altOfColimit order . bmap parseJSONArrayViaCodec $ diag
  DocArrayCodec _ c ->
    parseJSONArrayViaCodec c
  ElementCodec cd ->
    mkArrayParser (parseJSONViaCodec cd)
  EmptyArrayCodec ->
    pure ()
  DimapArrayCodec _ from c ->
    either fail pure . from =<< parseJSONArrayViaCodec c

newtype ArrayParser a = ArrayParser {unArrayParser :: Array -> Int -> Parser (a, Int)}
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

prettyCodec :: Codec a -> PP.Doc ann
prettyCodec = \case
  ObjectCodec o ->
    "object" PP.<+> PP.nest 2 (prettyObjectCodec o)
  ArrayCodec a ->
    "array" PP.<+> PP.nest 2 (prettyArrayCodec a)
  AnyOfCodec order diag ->
    prettyAnyOf prettyCodec order diag
  ManyOfCodec a ->
    "manyOf" PP.<+> prettyCodec a
  BrokenCodec ->
    ">broken<"
  StringCodec ->
    "<string>"
  NumberCodec ->
    "<number>"
  NullCodec ->
    "null"
  BoolCodec ->
    "<bool>"
  DocCodec s c ->
    "-- " <> PP.pretty s <> PP.line <> prettyCodec c
  DimapCodec _ _ c ->
    prettyCodec c
 where
  prettyObjectCodec :: ObjectCodec b -> PP.Doc ann
  prettyObjectCodec = \case
    AllOfObjectCodec order diag ->
      prettyAllOf prettyObjectCodec order diag
    AnyOfObjectCodec order diag ->
      prettyAnyOf prettyObjectCodec order diag
    DocObjectCodec s c ->
      "-- " <> PP.pretty s <> PP.line <> prettyObjectCodec c
    EmptyObjectCodec ->
      "<empty>"
    BrokenObjectCodec ->
      ">broken<"
    FieldCodec k v ->
      PP.hsep
        [PP.pretty (Aeson.toString k), ":", PP.nest 2 (prettyCodec v)]

  prettyArrayCodec :: ArrayCodec b -> PP.Doc ann
  prettyArrayCodec = \case
    AllOfArrayCodec order diag ->
      prettyAllOf prettyArrayCodec order diag
    AnyOfArrayCodec order diag ->
      prettyAnyOf prettyArrayCodec order diag
    DocArrayCodec s c ->
      "-- " <> PP.pretty s <> PP.line <> prettyArrayCodec c
    DimapArrayCodec _ _ c ->
      prettyArrayCodec c
    EmptyArrayCodec ->
      "<empty>"
    ElementCodec v ->
      prettyCodec v

prettyAnyOf :: (forall b. f b -> PP.Doc ann) -> DiagramOrder a -> Diagram a f -> PP.Doc ann
prettyAnyOf fn order diag =
  "anyOf"
    PP.<+> (PP.line <> PP.vcat (diagramFold order (\a -> ["+ " <> PP.nest 2 (fn a)]) diag))

prettyAllOf :: (forall b. f b -> PP.Doc ann) -> DiagramOrder a -> Diagram a f -> PP.Doc ann
prettyAllOf fn order diag =
  "allOf"
    PP.<+> (PP.line <> PP.vcat (diagramFold order (\a -> ["* " <> PP.nest 2 (fn a)]) diag))

debugCodec :: Codec a -> IO ()
debugCodec c = do
  putStrLn "------"
  PP.putDoc $ prettyCodec c
  putStrLn ""
  putStrLn "------"

{- $builders
These are the builders:
-}

broken :: Codec t
broken = BrokenCodec

null :: Codec ()
null = NullCodec

object :: ObjectCodec t -> Codec t
object = ObjectCodec

class HasCodec c t where
  object' :: (forall m. CodecSpecMonad ObjectCodec t m => m ()) -> c t

array :: ArrayCodec t -> Codec t
array = ArrayCodec

boundIntegral :: forall i c. (HasDimap c, HasPrimitives c, Integral i, Bounded i) => c i
boundIntegral =
  dimap
    (pure . fromIntegral)
    (maybe (Left "out of bounds") Right . toBoundedInteger)
    scientific

infix 6 <?>

class HasDoc c where
  (<?>) :: c a -> Text.Text -> c a

instance HasDoc Codec where
  (<?>) = flip DocCodec

instance HasDoc ArrayCodec where
  (<?>) = flip DocArrayCodec

instance HasDoc ObjectCodec where
  (<?>) = flip DocObjectCodec

class HasDimap c where
  dimap :: (b -> Either String a) -> (a -> Either String b) -> c a -> c b

instance HasDimap Codec where
  dimap = DimapCodec

instance HasDimap ArrayCodec where
  dimap = DimapArrayCodec

class HasPrimitives c where
  text :: c Text.Text
  bool :: c Bool
  scientific :: c Scientific

instance HasPrimitives Codec where
  text = StringCodec
  bool = BoolCodec
  scientific = NumberCodec

instance HasPrimitives ArrayCodec where
  text = ElementCodec StringCodec
  bool = ElementCodec BoolCodec
  scientific = ElementCodec NumberCodec

infix 7 .:

(.:) :: Key -> Codec c -> ObjectCodec c
(.:) = FieldCodec

class HasDefaultDiagram c where
  def :: ApplicativeB (Diagram a) => Diagram a c

instance HasDefaultDiagram ObjectCodec where
  def = bpure BrokenObjectCodec

class Monad m => CodecSpecMonad c t m | m -> c t where
  specCodec :: (forall f. LensB (Diagram t) f a) -> c a -> m ()

(<::)
  :: (LensesB (Diagram t), CodecSpecMonad c t m)
  => (forall f. Diagram t f -> f a)
  -> c a
  -> m ()
fn <:: ca = getBLens (fn blenses) `specCodec` ca

newtype OrderM m (c :: Type -> Type) t g a = OrderM {getOrderM :: Diagram t (m `Compose` g) -> Writer (Ap m (Endo (Diagram t g))) a}
  deriving (Functor, Applicative, Monad) via (ReaderT (Diagram t (m `Compose` g)) (Writer (Ap m (Endo (Diagram t g)))))

instance forall m c t g. Applicative m => CodecSpecMonad c t (OrderM m c t g) where
  specCodec :: forall a. (forall f. LensB (Diagram t) f a) -> c a -> OrderM m c t g ()
  specCodec l _ = OrderM \diag -> do
    tell (Ap (Endo . setter <$> getter diag))
   where
    setter ga = coerce . l (\_ -> Identity ga)
    getter = coerce . l Const
  {-# INLINE specCodec #-}

runOrderM
  :: (Applicative m, ApplicativeB (Diagram t))
  => OrderM m c t g ()
  -> (forall a. f a -> m (g a))
  -> Diagram t f
  -> m (Diagram t g)
runOrderM (OrderM m) fn x =
  let dt = bmap (Compose . fn) x
   in fmap (\e -> appEndo e (bpure undefined)) . coerce $ execWriter (m dt)
{-# INLINE runOrderM #-}

newtype CodecM (c :: Type -> Type) t a = CodecM {getCodecM :: Writer (Endo (Diagram t c)) a}
  deriving (Functor, Applicative, Monad) via (Writer (Endo (Diagram t c)))

instance forall c t. CodecSpecMonad c t (CodecM c t) where
  specCodec :: forall a. (forall f. LensB (Diagram t) f a) -> c a -> CodecM c t ()
  specCodec l ca = CodecM do
    tell (Endo $ setter ca)
   where
    setter ga = coerce . l (\_ -> Identity ga)
  {-# INLINE specCodec #-}

runCodecM
  :: (ApplicativeB (Diagram t))
  => CodecM c t ()
  -> Diagram t c
runCodecM (CodecM m) = appEndo (execWriter m) (bpure undefined)
{-# INLINE runCodecM #-}

infix 0 <::

any
  :: (HasAnyOfCodec c, IsColimit t)
  => (forall m. CodecSpecMonad c t m => m ())
  -> c t
any o = anyOfWithOrder (runOrderM o) (runCodecM o)
{-# INLINE any #-}

all
  :: (HasAllOfCodec c, IsLimit t)
  => (forall m. CodecSpecMonad c t m => m ())
  -> c t
all o = allOfWithOrder (runOrderM o) (runCodecM o)
{-# INLINE all #-}

arrayAll
  :: IsLimit t
  => (forall m. CodecSpecMonad ArrayCodec t m => m ())
  -> Codec t
arrayAll = array . all

objectAll
  :: IsLimit t
  => (forall m. CodecSpecMonad ObjectCodec t m => m ())
  -> Codec t
objectAll = object . all

allOf :: (HasAllOfCodec c, IsLimit a, TraversableB (Diagram a)) => Diagram a c -> c a
allOf = allOfWithOrder defaultDiagramOrder

class HasAllOfCodec c where
  allOfWithOrder :: IsLimit a => DiagramOrder a -> Diagram a c -> c a

anyOf :: (HasAnyOfCodec c, IsColimit a, TraversableB (Diagram a)) => Diagram a c -> c a
anyOf = anyOfWithOrder defaultDiagramOrder

class HasAnyOfCodec c where
  anyOfWithOrder :: IsColimit a => DiagramOrder a -> Diagram a c -> c a

instance HasAllOfCodec ObjectCodec where
  allOfWithOrder = AllOfObjectCodec

instance HasAnyOfCodec ObjectCodec where
  anyOfWithOrder = AnyOfObjectCodec

instance HasAnyOfCodec Codec where
  anyOfWithOrder = AnyOfCodec

instance HasAllOfCodec ArrayCodec where
  allOfWithOrder = AllOfArrayCodec

instance HasAnyOfCodec ArrayCodec where
  anyOfWithOrder = AnyOfArrayCodec
