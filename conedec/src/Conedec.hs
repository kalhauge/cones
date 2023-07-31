{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

{- |

Stability: experimental

A cone based Codec implementation.
-}
module Conedec where

-- base
import Control.Applicative
import Data.Bifunctor
import Data.Functor.Contravariant

-- aeson
import Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types

-- vector
import qualified Data.Vector as V

-- barbies
import Barbies

-- text
import qualified Data.Text as Text

-- cones
import Data.Cone

-- prettyprinter

import qualified Data.Aeson.Key as Aeson
import Data.Scientific
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

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
  ElementCodec
    :: Codec a
    -> ArrayCodec a

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
    :: ObjectCodec a

toJSONViaCodec :: Codec t -> t -> Value
toJSONViaCodec = \case
  AnyOfCodec _ diag ->
    cofactor (bmap (Op . toJSONViaCodec) diag)
  ManyOfCodec c ->
    Array . fmap (toJSONViaCodec c)
  ArrayCodec a ->
    Array . toJSONArrayViaCodec a
  ObjectCodec oc ->
    Aeson.object . toJSONObjectViaCodec oc
  NumberCodec ->
    Aeson.Number
  BrokenCodec -> \_ -> error "empty codec"
  NullCodec -> \case
    () -> Null
  StringCodec ->
    String
  BoolCodec ->
    Bool

toJSONArrayViaCodec :: ArrayCodec t -> t -> Array
toJSONArrayViaCodec = \case
  AllOfArrayCodec order diag ->
    foldOfLimit order toJSONArrayViaCodec diag
  AnyOfArrayCodec _ diag ->
    cofactor . bmap (Op . toJSONArrayViaCodec) $ diag
  ElementCodec cd ->
    V.singleton . toJSONViaCodec cd

toJSONObjectViaCodec :: ObjectCodec t -> t -> [Pair]
toJSONObjectViaCodec = \case
  AllOfObjectCodec order diag ->
    foldOfLimit order toJSONObjectViaCodec diag
  AnyOfObjectCodec _ diag ->
    cofactor . bmap (Op . toJSONObjectViaCodec) $ diag
  FieldCodec name cd -> \t ->
    pure (name, toJSONViaCodec cd t)
  EmptyObjectCodec ->
    const []

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
    error "empty codec"
  NullCodec -> \case
    Null -> pure ()
    a -> typeMismatch "null" a
  NumberCodec -> \case
    Number s -> pure s
    a -> typeMismatch "number" a
  StringCodec -> \case
    String txt -> pure txt
    v -> typeMismatch "String" v
  BoolCodec -> \case
    Bool b -> pure b
    v -> typeMismatch "Bool" v

parseJSONObjectViaCodec :: ObjectCodec t -> ObjectParser t
parseJSONObjectViaCodec = undefined

newtype ObjectParser a = ObjectParser {unObjectParser :: Object -> Parser a}
  deriving (Functor)

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
    appOfLimit order . bmap parseJSONArrayViaCodec $ diag
  AnyOfArrayCodec order diag ->
    altOfColimit order . bmap parseJSONArrayViaCodec $ diag
  ElementCodec cd ->
    mkArrayParser (parseJSONViaCodec cd)

newtype ArrayParser a = ArrayParser {unArrayParser :: Array -> Int -> Parser (a, Int)}
  deriving (Functor)

mkArrayParser :: (Value -> Parser t) -> ArrayParser t
mkArrayParser fn = ArrayParser \arr i ->
  case arr V.!? i of
    Just val -> (,i + 1) <$> (fn val Aeson.<?> Index i)
    Nothing -> fail "not enough elements in the array"

runArrayParser :: String -> ArrayParser t -> Value -> Parser t
runArrayParser n (ArrayParser f) = withArray n \arr ->
  fst <$> f arr 0

instance Applicative ArrayParser where
  pure a = ArrayParser (\_ n -> pure (a, n))
  ArrayParser f <*> ArrayParser g = ArrayParser \a n -> do
    (b, n') <- f a n
    first b <$> g a n'

instance Alternative ArrayParser where
  empty = ArrayParser (\_ _ -> empty)
  ArrayParser f <|> ArrayParser g = ArrayParser \a n ->
    f a n <|> g a n

{- $prettyprinter
Here:
-}

prettyCodec :: Codec a -> PP.Doc ann
prettyCodec = \case
  ObjectCodec o ->
    "object" PP.<+> prettyObjectCodec o
  ArrayCodec a ->
    "array" PP.<+> prettyArrayCodec a
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
 where
  prettyObjectCodec :: ObjectCodec b -> PP.Doc ann
  prettyObjectCodec = \case
    AllOfObjectCodec order diag ->
      prettyAllOf prettyObjectCodec order diag
    AnyOfObjectCodec order diag ->
      prettyAnyOf prettyObjectCodec order diag
    EmptyObjectCodec ->
      "<empty>"
    FieldCodec k v ->
      PP.hsep
        [PP.pretty (Aeson.toString k), ":", PP.nest 2 (prettyCodec v)]

  prettyArrayCodec :: ArrayCodec b -> PP.Doc ann
  prettyArrayCodec = \case
    AllOfArrayCodec order diag ->
      prettyAllOf prettyArrayCodec order diag
    AnyOfArrayCodec order diag ->
      prettyAnyOf prettyArrayCodec order diag
    ElementCodec v ->
      prettyCodec v

prettyAnyOf :: (forall b. f b -> PP.Doc ann) -> DiagramOrder a -> Diagram a f -> PP.Doc ann
prettyAnyOf fn order diag =
  "anyOf"
    PP.<+> PP.nest
      2
      (PP.line <> PP.vcat (diagramFold order (\a -> ["+ " <> fn a]) diag))

prettyAllOf :: (forall b. f b -> PP.Doc ann) -> DiagramOrder a -> Diagram a f -> PP.Doc ann
prettyAllOf fn order diag =
  "allOf"
    PP.<+> PP.nest
      2
      (PP.line <> PP.vcat (diagramFold order (\a -> ["* " <> fn a]) diag))

debugCodec :: Codec a -> IO ()
debugCodec c = do
  putStrLn "------"
  PP.putDoc $ prettyCodec c
  putStrLn ""
  putStrLn "------"

{- $builders
These are the buidlers:
-}

broken :: Codec t
broken = BrokenCodec

null :: Codec ()
null = NullCodec

object :: ObjectCodec t -> Codec t
object = ObjectCodec

array :: ArrayCodec t -> Codec t
array = ArrayCodec

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

(.:) :: Key -> Codec c -> ObjectCodec c
(.:) = FieldCodec

class HasEmptyDiagram c where
  def :: ApplicativeB (Diagram a) => Diagram a c

instance HasEmptyDiagram ObjectCodec where
  def = bpure EmptyObjectCodec

class HasAllOfCodec c where
  allOf :: (IsLimit a, TraversableB (Diagram a)) => Diagram a c -> c a

class HasAnyOfCodec c where
  anyOf :: (IsColimit a, TraversableB (Diagram a)) => Diagram a c -> c a

instance HasAllOfCodec ObjectCodec where
  allOf = AllOfObjectCodec defaultDiagramOrder

instance HasAnyOfCodec ObjectCodec where
  anyOf = AnyOfObjectCodec defaultDiagramOrder

instance HasAllOfCodec ArrayCodec where
  allOf = AllOfArrayCodec defaultDiagramOrder

instance HasAnyOfCodec ArrayCodec where
  anyOf = AnyOfArrayCodec defaultDiagramOrder
