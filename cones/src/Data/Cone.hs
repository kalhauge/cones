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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Avoid lambda" #-}

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

data instance Diagram Bool f = BoolD
  { ifFalse :: f ()
  , ifTrue :: f ()
  }
  deriving stock (Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

instance IndexedB (Diagram Bool) where bindexed = BoolD (Const 0) (Const 1)

instance IxB (Diagram Bool) 0 () where bix Index = ifFalse
instance IxB (Diagram Bool) 1 () where bix Index = ifTrue

instance LabeledB (Diagram Bool) where blabeled = BoolD (Const "ifFalse") (Const "ifTrue")

instance HasB (Diagram Bool) "ifFalse" () where bfrom Label = ifFalse
instance HasB (Diagram Bool) "ifTrue" () where bfrom Label = ifTrue

instance LensesB (Diagram Bool) where
  blenses = BoolD (ALensB \fn (BoolD a b) -> (`BoolD` b) <$> fn a) (ALensB \fn (BoolD a b) -> BoolD a <$> fn b)

-- | The diagram for the coproduct
data instance Diagram (Maybe a) f = MaybeD
  { ifNothing :: f ()
  , ifJust :: f a
  }
  deriving stock (Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

instance IndexedB (Diagram (Maybe a)) where bindexed = MaybeD (Const 0) (Const 1)

instance IxB (Diagram (Maybe a)) 0 () where bix Index = ifNothing
instance IxB (Diagram (Maybe a)) 1 a where bix Index = ifJust

instance LabeledB (Diagram (Maybe a)) where blabeled = MaybeD (Const "ifNothing") (Const "ifJust")

instance HasB (Diagram (Maybe a)) "ifNothing" () where bfrom Label = ifNothing
instance HasB (Diagram (Maybe a)) "ifJust" a where bfrom Label = ifJust

instance LensesB (Diagram (Maybe a)) where
  blenses = MaybeD (ALensB \fn (MaybeD a b) -> (`MaybeD` b) <$> fn a) (ALensB \fn (MaybeD a b) -> MaybeD a <$> fn b)

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

instance LabeledB (Diagram (Either a b)) where blabeled = EitherD (Const "ifLeft") (Const "ifRight")

instance HasB (Diagram (Either a b)) "ifLeft" a where bfrom Label = ifLeft
instance HasB (Diagram (Either a b)) "ifRight" b where bfrom Label = ifRight

instance LensesB (Diagram (Either a b)) where
  blenses = EitherD (ALensB \fn (EitherD a b) -> (`EitherD` b) <$> fn a) (ALensB \fn (EitherD a b) -> EitherD a <$> fn b)

-- | The diagram for the product
data instance Diagram (a, b) f = Two (f a) (f b)
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

instance IndexedB (Diagram (a, b)) where bindexed = Two (Const 0) (Const 1)

instance IxB (Diagram (a, b)) 0 a where bix Index (Two a _) = a
instance IxB (Diagram (a, b)) 1 b where bix Index (Two _ b) = b

instance LabeledB (Diagram (a, b)) where blabeled = Two (Const "fst") (Const "snd")

instance HasB (Diagram (a, b)) "fst" a where bfrom Label (Two a _) = a
instance HasB (Diagram (a, b)) "snd" b where bfrom Label (Two _ b) = b

instance LensesB (Diagram (a, b)) where
  blenses =
    Two
      (ALensB \fn (Two a b) -> (`Two` b) <$> fn a)
      (ALensB \fn (Two a b) -> Two a <$> fn b)

-- | The diagram for the product
data instance Diagram (a, b, c) f = Three (f a) (f b) (f c)
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FunctorB, ApplicativeB, TraversableB)

instance IndexedB (Diagram (a, b, c)) where bindexed = Three (Const 0) (Const 1) (Const 2)

instance IxB (Diagram (a, b, c)) 0 a where bix Index (Three a _ _) = a
instance IxB (Diagram (a, b, c)) 1 b where bix Index (Three _ b _) = b
instance IxB (Diagram (a, b, c)) 2 c where bix Index (Three _ _ c) = c

instance LabeledB (Diagram (a, b, c)) where blabeled = Three (Const "fst") (Const "snd") (Const "trd")

instance HasB (Diagram (a, b, c)) "fst" a where bfrom Label (Three a _ _) = a
instance HasB (Diagram (a, b, c)) "snd" b where bfrom Label (Three _ b _) = b
instance HasB (Diagram (a, b, c)) "trd" c where bfrom Label (Three _ _ c) = c

instance LensesB (Diagram (a, b, c)) where
  blenses =
    Three
      (ALensB \fn (Three a b c) -> (\x -> Three x b c) <$> fn a)
      (ALensB \fn (Three a b c) -> (\x -> Three a x c) <$> fn b)
      (ALensB \fn (Three a b c) -> (\x -> Three a b x) <$> fn c)

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

instance IsLimit (a, b, c) where
  cone = Three (\(a, _, _) -> a) (\(_, b, _) -> b) (\(_, _, c) -> c)
  factor (Three fst' snd' trd') b = (fst' b, snd' b, trd' b)
  coneCone =
    Three
      (\(Three fst' _ _) -> fst' ())
      (\(Three _ snd' _) -> snd' ())
      (\(Three _ _ trd') -> trd' ())

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

instance IsColimit (Maybe a) where
  cocone = MaybeD{ifNothing = Op (const Nothing), ifJust = Op Just}
  cofactor MaybeD{..} = \case
    Nothing -> getOp ifNothing ()
    Just a -> getOp ifJust a

instance IsColimit Bool where
  cocone = BoolD{ifFalse = Op (const False), ifTrue = Op (const True)}
  cofactor BoolD{..} = \case
    True -> getOp ifTrue ()
    False -> getOp ifFalse ()

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
