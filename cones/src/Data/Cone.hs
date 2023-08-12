{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

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
  apOfLimit,
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
import GHC.Generics (Generic)

-- barbies
import Barbies hiding (Void)

-- cones
import Barbies.Access

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
data family Diagram t :: (Type -> Type) -> Type

-- | The diagram for the coproduct
data instance Diagram (Either a b) f = EitherD
  { ifLeft :: f a
  , ifRight :: f b
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

instance IndexedB (Diagram (Either a b)) where bindexed = EitherD (Const 0) (Const 1)

instance IxB (Diagram (Either a b)) 0 a where bix Index = ifLeft
instance IxB (Diagram (Either a b)) 1 b where bix Index = ifRight

instance LabeledB (Diagram (Either a b)) where blabeled = EitherD (Const "Left") (Const "Right")

instance HasB (Diagram (Either a b)) "Left" a where bfrom Label = ifLeft
instance HasB (Diagram (Either a b)) "Right" b where bfrom Label = ifRight

-- | The diagram for the product
data instance Diagram (a, b) f = Two (f a) (f b)
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

instance IndexedB (Diagram (a, b)) where bindexed = Two (Const 0) (Const 1)

instance IxB (Diagram (a, b)) 0 a where bix Index (Two a _) = a
instance IxB (Diagram (a, b)) 1 b where bix Index (Two _ b) = b

instance LensesB (Diagram (a, b)) where
  blenses =
    Two
      (ALensB \fn (Two a b) -> (`Two` b) <$> fn a)
      (ALensB \fn (Two a b) -> Two a <$> fn b)

-- -- | The diagram for the 3 tuple
-- newtype instance Diagram (a, b, c) f = Three (f a, f b, f c)
--   deriving stock (Show, Eq, Generic)
--   deriving anyclass (FunctorB, ApplicativeB, TraversableB)
--
-- -- | The diagram for the 4 tuple
-- newtype instance Diagram (a, b, c, d) f = Four (f a, f b, f c, f d)
--   deriving stock (Show, Eq, Generic)
--   deriving anyclass (FunctorB, ApplicativeB, TraversableB)

{- $cones

Cones and limits
-}

-- | A @Cone@ is a digram over the functor (->) b
type Cone t b = Diagram t ((->) b)

{- |

Laws:
@
factor cone = id
@
-}
class ApplicativeB (Diagram t) => IsLimit t where
  -- | @a@ has a cone.
  cone :: Cone t t

  -- | Given any other code, we can find a unique morphism from the top of the cone @b@ to our limit.
  factor :: Cone t b -> b -> t

  -- | Uniquely for the cone, the diagram on the Identity functor is also an apex of t cone.
  coneCone :: Cone t (Cone t ())

instance IsLimit (a, b) where
  cone = Two fst snd
  factor (Two fst' snd') b = (fst' b, snd' b)
  coneCone =
    Two
      (\(Two fst' _) -> fst' ())
      (\(Two _ snd') -> snd' ())

-- coneCone :: IsLimit a => Cone a (Cone a ())
-- coneCone = cone

identityCone :: forall t. IsLimit t => Cone t (Diagram t Identity)
identityCone = bmap (. identityDiagramToCone) coneCone

identityDiagramToCone :: IsLimit t => Diagram t Identity -> Cone t ()
identityDiagramToCone = bmap (const . runIdentity)

-- unitConeToDiagram :: IsLimit t => Cone t () -> Diagram t Identity
-- unitConeToDiagram = bmap (\a -> Identity $ a ())
--
-- voidCone :: IsLimit t => Cone t Void
-- voidCone = bmap (const absurd) cone

{- | Use the limit ability to extract an application of the
    contravariant functor @g@ on the limit for each element in the diagram.
-}
eject
  :: (IsLimit t, Contravariant g)
  => Diagram t g
  -> Diagram t (Const (g t))
eject = bzipWith (\fn cd -> Const $ fn >$< cd) cone

{- | Used to calculate the identity using a limit, only really usefull for
testing that limits are created correctly.

__Examples:__

@
prop_isLimit :: (Int, Bool) -> Property
prop_isLimit a = a === limitIdentity a
@
-}
limitIdentity :: IsLimit t => t -> t
limitIdentity = factor cone

{- $cocones

Cocones and colimits.
-}

-- | A @Cocone@ is a digram over the covariate functor (<-) a
type Cocone t b = Diagram t (Op b)

{- |

Laws:

@
cofactor cocone = id
@
-}
class ApplicativeB (Diagram t) => IsColimit t where
  -- | @a@ has a cocone.
  cocone :: Cocone t t

  -- | Given any other cone, we can find a unique morphism from our limit to the from the top of the cone @b@.
  cofactor :: Cocone t b -> t -> b

{- | Used to calculate the identity using a limit, only really usefull for
testing that limits are created correctly.

__Examples:__

@
prop_isColimit :: Eihter Int Bool -> Property
prop_isColimit a = a === colimitIdentity a
@
-}
colimitIdentity :: IsColimit t => t -> t
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
  :: (IsColimit t, Functor g)
  => Diagram t g
  -> Diagram t (Const (g t))
coeject = bzipWith (\(Op fn) cd -> Const $ fn <$> cd) cocone

-- unitCocone :: IsColimit t => Cocone t ()
-- unitCocone = bmap (const . Op $ const ()) cocone

{- $ordering

The ordering of effects over diagrams.
-}

-- | Ordering of a diagram
type DiagramOrder t =
  forall m f g
   . Applicative m
  => (forall a. f a -> m (g a))
  -> Diagram t f
  -> m (Diagram t g)

defaultDiagramOrder :: TraversableB (Diagram t) => DiagramOrder t
defaultDiagramOrder = btraverse

-- | A fold over a diagram.
diagramFold :: Monoid m => DiagramOrder t -> (forall a. f a -> m) -> Diagram t f -> m
diagramFold order fn = getConst . order (Const . fn)

altOfColimit :: forall t f. (IsColimit t, Alternative f) => DiagramOrder t -> Diagram t f -> f t
altOfColimit order =
  getAlt . foldOfColimit order Alt

foldOfColimit
  :: forall t m f
   . (IsColimit t, Monoid m, Functor f)
  => DiagramOrder t
  -> (f t -> m)
  -> Diagram t f
  -> m
foldOfColimit order f diag =
  diagramFold order (\(Const t) -> f t) $ coeject diag

-- | Compute the applicative fold over the
apOfLimit :: forall t f. (IsLimit t, Applicative f) => DiagramOrder t -> Diagram t f -> f t
apOfLimit order diag =
  factor identityCone <$> order (Identity <$>) diag

foldOfLimit :: forall t m f. (IsLimit t, Monoid m) => DiagramOrder t -> (forall a. f a -> a -> m) -> Diagram t f -> t -> m
foldOfLimit order f diag t =
  let pre :: Diagram t (Const (Op m t)) = eject . bmap (Op . f) $ diag
   in diagramFold order (\(Const (Op f')) -> f' t) pre
