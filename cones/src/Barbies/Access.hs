{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-
   Missing accessors for barbie instances.
-}
module Barbies.Access (
  -- * lenses
  LensB,
  ALensB (..),
  LensesB (..),

  -- * labeled
  Label (..),
  LabeledB (..),
  HasB (..),
  get,

  -- * indexed
  Index (..),
  IndexedB (..),
  IxB (..),
  pos,
  --
) where

import Data.Functor.Const
import GHC.TypeLits

data Label (l :: Symbol) = Label

class LabeledB b where
  blabeled :: b (Const String)

{- | A labeled b can also be accessed using that label:
 laws:
 @
 >>> getConst $ bfrom (Label : Label "<something>") blabeled
 ... "<something>"
 @
-}
class LabeledB b => HasB b l a | b l -> a where
  bfrom :: forall f. Label l -> b f -> f a

get :: forall l b f a. HasB b l a => b f -> f a
get = bfrom (Label :: Label l)

data Index (n :: Natural) = Index

class IndexedB b where
  bindexed :: b (Const Natural)

class IxB b n a | b n -> a where
  bix :: forall f. Index n -> b f -> f a

pos :: forall n b f a. IxB b n a => b f -> f a
pos = bix (Index :: Index n)

type LensB b f a = forall m. Functor m => (f a -> m (f a)) -> (b f -> m (b f))

-- | Diagram Lenses
newtype ALensB b f a = ALensB
  { getLensB :: LensB b f a
  }

class LensesB b where
  blenses :: b (ALensB b f)
