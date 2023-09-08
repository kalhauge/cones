{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Conedec.Codec (
  Codec (..),
  Ref (..),
  Def (..),
  cunfold,
  destroy,
  build,
) where

-- base
import Control.Applicative
import Data.Functor.Contravariant
import Data.Kind
import Data.Monoid hiding (Product, Sum)
import GHC.TypeLits

-- barbies
import Barbies hiding (Void)

-- mtl
import Control.Monad.Reader

-- cones
import Data.Cone

data Ref (s :: Symbol) = KnownSymbol s => Ref

class Def (s :: Symbol) (e :: Type -> Type -> Type -> Type) ctx ann a | ctx s -> a e where
  def :: Codec e ctx ann a

{- | A redesign of the codec.

The codec contains of four type variables encoder @e@, context @ctx@, annotations @ann@ and type @a@.
-}
data Codec e ctx ann a where
  -- | All codecs can be created in a broken state, to ease development.
  -- This is easy to check for though.
  BrokenCodec
    :: Codec e ctx ann a
  -- | A Sum of different codec, choosing the first matching when parsing.
  SumCodec
    :: (IsColimit a)
    => DiagramOrder a
    -> Diagram a (Codec e ctx ann)
    -> Codec e ctx ann a
  -- | A Product of different codec, where the order of the elements is decided by the order.
  ProductCodec
    :: (IsLimit a)
    => DiagramOrder a
    -> Diagram a (Codec e ctx ann)
    -> Codec e ctx ann a
  DimapCodec
    :: (b -> Either String a)
    -> (a -> Either String b)
    -> Codec e ctx ann a
    -> Codec e ctx ann b
  -- | The reference codec.
  -- The trick here is to ensure that there exist only one Codec per context and name.
  ReferenceCodec
    :: (Def s e' ctx ann a)
    => Ref s
    -> (Codec e' ctx ann a -> Codec e ctx ann a)
    -> Codec e ctx ann a
  ElementCodec
    :: e ctx ann a
    -> Codec e ctx ann a
  -- | Adding a line of documentation to the codec.
  AnnotateCodec
    :: ann
    -> Codec e ctx ann a
    -> Codec e ctx ann a

cunfold :: (forall b. e ctx ann b -> Codec e' ctx ann b) -> Codec e ctx ann a -> Codec e' ctx ann a
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
  AnnotateCodec dc c ->
    AnnotateCodec dc (cunfold fn c)

-- | Fold over a $a$ producing a value x or a string error
destroy
  :: forall ctx ann e a m x
   . (MonadFail m, Monoid x)
  => (forall t. e ctx ann t -> t -> m x)
  -> Codec e ctx ann a
  -> a
  -> m x
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
    destroy fn (f (def @s))
  ElementCodec c ->
    fn c
  AnnotateCodec _ c ->
    destroy fn c

-- | Create an $a$ or an string error.
build
  :: forall ctx ann e m a
   . (Alternative m, MonadFail m)
  => (forall t. e ctx ann t -> m t)
  -> Codec e ctx ann a
  -> m a
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
    build fn (f (def @s))
  ElementCodec c ->
    fn c
  AnnotateCodec _ c ->
    build fn c
