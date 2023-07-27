{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
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
  limitIdentity,

  -- * Cocones and Colimits
  -- $cocones
  Cocone,
  IsColimit (..),
  colimitIdentity,
) where

-- base
import Data.Functor.Contravariant
import Data.Kind
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
  deriving (Show, Eq, Generic)

-- | The diagram for the product
data instance Diagram (a, b) f = D2
  { getFstOf2 :: f a
  , getSndOf2 :: f b
  }
  deriving (Show, Eq, Generic)

-- | The diagram for the 3 tuple
data instance Diagram (a, b, c) f = D3
  { getFstOf3 :: f a
  , getSndOf3 :: f b
  , getTrdOf3 :: f c
  }
  deriving (Show, Eq, Generic)

-- | The diagram for the 4 tuple
data instance Diagram (a, b, c, d) f = D4
  { getFstOf4 :: f a
  , getSndOf4 :: f b
  , getTrdOf4 :: f c
  , getFthOf4 :: f d
  }
  deriving (Show, Eq, Generic)

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
class IsLimit a where
  -- | @a@ has a cone.
  cone :: Cone a a

  -- | Given any other code, we can find a unique morphism from the top of the cone @b@ to our limit.
  factor :: Cone a b -> b -> a

instance IsLimit (a, b) where
  cone = D2{getFstOf2 = fst, getSndOf2 = snd}
  factor D2{..} b = (getFstOf2 b, getSndOf2 b)

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
class IsColimit a where
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
