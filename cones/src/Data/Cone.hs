{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

{- |
Module: Data.Cone

This is the primary module of the 'cones' library.
-}
module Data.Cone (
  -- * Diagram
  -- $diagrams
  Diagram (..),

  -- * Cones and Limits
  -- $cones
  Cone,
  IsLimit (..),
  eject,
  limitIdentity,

  -- * Cocones and Colimits
  -- $cocones
  Cocone,
  IsColimit (..),
  coeject,
  colimitIdentity,

  -- * Ordering
  -- $ordering
  DiagramOrder,
  defaultDiagramOrder,
  diagramFold,
  appOfLimit,
  foldOfLimit,
  altOfColimit,
) where

-- base

import Barbies
import Control.Applicative
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Kind
import Data.Monoid
import GHC.Generics (Generic)

{- $diagrams
The intuition behind a diagram, *in this setting*, is that
it is a container for functions used to create or tear apart data structures.

For example the diagram for the product '(a, b)' is the collection of the two functions 'fst' and 'snd'.

@
data ProductDiagram a b = ProductDiagram
  { getFst :: (a, b) -> a
  , getSnd :: (a, b) -> b
  }
@

Actually, this is in fact the 'Cone' defining '(a, b)'.

We also have the diagram for the coproduct 'Either a b', which is the collection of the two constructors 'Left' and 'Right'

@
data CoproductDiagram a b = CoproductDiagram
  { ifLeft :: a -> Either a b
  , ifRight :: b -> Either a b
  }
@

Actually, this is in fact the 'Cocone' defining 'Either a b'.

The actual definition in this module, is abstract enough to cover both kinds of diagrams definitions, and many other
use cases.
-}

{- | Every ADT have a corresponding diagram, but for programming reasons, it is nice to have this defined as a unique datatype.
*I'm terrible sorry that the data family rendering is not especially good.*
-}
data family Diagram a :: (Type -> Type) -> Type

-- | The diagram for the coproduct
data instance Diagram (Either a b) f = EitherD
  { ifLeft :: f a
  , ifRight :: f b
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

-- | The diagram for the product
data instance Diagram (a, b) f = D2
  { getFstOf2 :: f a
  , getSndOf2 :: f b
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

-- | The diagram for the 3 tuple
data instance Diagram (a, b, c) f = D3
  { getFstOf3 :: f a
  , getSndOf3 :: f b
  , getTrdOf3 :: f c
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

-- | The diagram for the 4 tuple
data instance Diagram (a, b, c, d) f = D4
  { getFstOf4 :: f a
  , getSndOf4 :: f b
  , getTrdOf4 :: f c
  , getFthOf4 :: f d
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

{- $cones

Cones and limits
-}

-- | A @Cone@ is a digram over the functor (->) b
type Cone a b = Diagram a ((->) b)

{- |

Laws:
@
factor cone = id
@
-}
class ApplicativeB (Diagram a) => IsLimit a where
  -- | @a@ has a cone.
  cone :: Cone a a

  -- | Given any other code, we can find a unique morphism from the top of the cone @b@ to our limit.
  factor :: Cone a b -> b -> a

  -- | Uniquely for the cone, the diagram on the Identity functor is also an apex of a cone.
  identityCone :: Cone a (Diagram a Identity)

instance IsLimit (a, b) where
  cone = D2{getFstOf2 = fst, getSndOf2 = snd}
  factor D2{..} b = (getFstOf2 b, getSndOf2 b)
  identityCone =
    D2
      { getFstOf2 = runIdentity . getFstOf2
      , getSndOf2 = runIdentity . getSndOf2
      }

{- | Use the limit ability to extract an application of the
    contravariant functor @g@ on the limit for each element in the diagram.
-}
eject
  :: (IsLimit a, Contravariant g)
  => Diagram a g
  -> Diagram a (Const (g a))
eject = bzipWith (\fn cd -> Const $ fn >$< cd) cone

{- | Used to calculate the identity using a limit, only really usefull for
testing that limits are created correctly.

__Examples:__

@
prop_isLimit :: (Int, Bool) -> Property
prop_isLimit a = a === limitIdentity a
@
-}
limitIdentity :: IsLimit a => a -> a
limitIdentity = factor cone

{- $cocones

Cocones and colimits.
-}

-- | A @Cocone@ is a digram over the covariate functor (<-) a
type Cocone a b = Diagram a (Op b)

{- |

Laws:

@
cofactor cocone = id
@
-}
class ApplicativeB (Diagram a) => IsColimit a where
  -- | @a@ has a cocone.
  cocone :: Cocone a a

  -- | Given any other cone, we can find a unique morphism from our limit to the from the top of the cone @b@.
  cofactor :: Cocone a b -> a -> b

{- | Used to calculate the identity using a limit, only really usefull for
testing that limits are created correctly.

__Examples:__

@
prop_isColimit :: Eihter Int Bool -> Property
prop_isColimit a = a === colimitIdentity a
@
-}
colimitIdentity :: IsColimit a => a -> a
colimitIdentity = cofactor cocone

instance IsColimit (Either a b) where
  cocone = EitherD{ifLeft = Op Left, ifRight = Op Right}
  cofactor EitherD{..} = \case
    Left a -> getOp ifLeft a
    Right a -> getOp ifRight a

{- | Use the colimit ability to extract an application of the functor
 @g@ on the colimit for each element in the diagram.
-}
coeject
  :: (IsColimit a, Functor g)
  => Diagram a g
  -> Diagram a (Const (g a))
coeject = bzipWith (\(Op fn) cd -> Const $ fn <$> cd) cocone

{- $ordering

The ordering of effects over diagrams.
-}

-- | Ordering of a diagram
type DiagramOrder a =
  forall m f g
   . Applicative m
  => (forall t. f t -> m (g t))
  -> Diagram a f
  -> m (Diagram a g)

defaultDiagramOrder :: TraversableB (Diagram a) => DiagramOrder a
defaultDiagramOrder = btraverse

-- | A fold over a diagram.
diagramFold :: Monoid m => DiagramOrder a -> (forall t. f t -> m) -> Diagram a f -> m
diagramFold order fn = getConst . order (Const . fn)

altOfColimit :: forall a f. (IsColimit a, Alternative f) => DiagramOrder a -> Diagram a f -> f a
altOfColimit order diag =
  let pre :: Diagram a (Const (f a)) = coeject diag
   in getAlt . diagramFold order (\(Const a) -> Alt a) $ pre

-- | Compute the applicative fold over the
appOfLimit :: forall a f. (IsLimit a, Applicative f) => DiagramOrder a -> Diagram a f -> f a
appOfLimit order diag =
  factor identityCone <$> order (Identity <$>) diag

foldOfLimit :: forall a m f. (IsLimit a, Monoid m) => DiagramOrder a -> (forall t. f t -> t -> m) -> Diagram a f -> a -> m
foldOfLimit order f diag a =
  let pre :: Diagram a (Const (Op m a)) = eject . bmap (Op . f) $ diag
   in diagramFold order (\(Const (Op f')) -> f' a) pre
