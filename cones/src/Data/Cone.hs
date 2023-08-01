{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
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
  identityCone,

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
  foldOfColimit,
) where

-- base
import Control.Applicative
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Kind
import Data.Monoid
import Data.Void
import GHC.Generics (Generic)

-- barbies
import Barbies hiding (Void)

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

{- | An index is a single element in the diagram, this is esentially the choosing one of
 the elements in the diagram.
-}
data family Index a :: (Type -> Type) -> Type

data instance Index (Either a b) f
  = EitherLeftI (f a)
  | EitherRightI (f b)
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, TraversableB)

data instance Index (a, b) f
  = I2Fst (f a)
  | I2Snd (f b)
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, TraversableB)

{- $cones

Cones and limits
-}

-- | A @Cone@ is a digram over the functor (->) b
type Cone a b = Diagram a ((->) b)

type Coscoop a b = Index a (Op b)

test :: t ~ (a, b) => Diagram t (Const (t -> Coscoop t t))
test =
  D2
    { getFstOf2 = Const (\t -> I2Fst $ Op (,snd t))
    , getSndOf2 = Const (\t -> I2Snd $ Op (fst t,))
    }

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

  coscoop :: Coscoop a b -> a -> b

  -- | Uniquely for the cone, the diagram on the Identity functor is also an apex of a cone.
  coneCone :: Cone a (Cone a ())

instance IsLimit (a, b) where
  cone = D2{getFstOf2 = fst, getSndOf2 = snd}
  factor D2{..} b = (getFstOf2 b, getSndOf2 b)
  coneCone =
    D2
      { getFstOf2 = (`getFstOf2` ())
      , getSndOf2 = (`getSndOf2` ())
      }

  coscoop = \case
    I2Fst (Op fa) -> fa . fst
    I2Snd (Op fa) -> fa . snd

-- coneCone :: IsLimit a => Cone a (Cone a ())
-- coneCone = cone

identityCone :: forall a. IsLimit a => Cone a (Diagram a Identity)
identityCone = bmap (. identityDiagramToCone) coneCone

identityDiagramToCone :: IsLimit a => Diagram a Identity -> Cone a ()
identityDiagramToCone = bmap (const . runIdentity)

unitConeToDiagram :: IsLimit a => Cone a () -> Diagram a Identity
unitConeToDiagram = bmap (\a -> Identity $ a ())

voidCone :: IsLimit a => Cone a Void
voidCone = bmap (const absurd) cone

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

type Scoop a b = Index a ((->) b)

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

  scoop :: Scoop a b -> b -> a

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
  scoop = \case
    EitherLeftI fa -> Left . fa
    EitherRightI fb -> Right . fb

{- | Use the colimit ability to extract an application of the functor
 @g@ on the colimit for each element in the diagram.
-}
coeject
  :: (IsColimit a, Functor g)
  => Diagram a g
  -> Diagram a (Const (g a))
coeject = bzipWith (\(Op fn) cd -> Const $ fn <$> cd) cocone

unitCocone :: IsColimit a => Cocone a ()
unitCocone = bmap (const . Op $ const ()) cocone

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
altOfColimit order =
  getAlt . foldOfColimit order Alt

foldOfColimit
  :: forall a m f
   . (IsColimit a, Monoid m, Functor f)
  => DiagramOrder a
  -> (f a -> m)
  -> Diagram a f
  -> m
foldOfColimit order f diag =
  diagramFold order (\(Const a) -> f a) $ coeject diag

-- | Compute the applicative fold over the
appOfLimit :: forall a f. (IsLimit a, Applicative f) => DiagramOrder a -> Diagram a f -> f a
appOfLimit order diag =
  factor identityCone <$> order (Identity <$>) diag

foldOfLimit :: forall a m f. (IsLimit a, Monoid m) => DiagramOrder a -> (forall t. f t -> t -> m) -> Diagram a f -> a -> m
foldOfLimit order f diag a =
  let pre :: Diagram a (Const (Op m a)) = eject . bmap (Op . f) $ diag
   in diagramFold order (\(Const (Op f')) -> f' a) pre
