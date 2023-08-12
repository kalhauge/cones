{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- |

Stability: experimental

A cone based Codec implementation.

Remaining things:

- [ ] Adding references and declarations
- [ ] Adding documentation
-}
module Conedec.Builder where

-- base
import Control.Applicative
import Data.Coerce
import Data.Functor.Identity
import Data.Monoid

-- aeson
import qualified Data.Aeson.Key as Aeson

-- barbies
import Barbies

-- mtl
import Control.Monad.Reader
import Control.Monad.Writer

-- text
import qualified Data.Text as Text

-- cones
import Barbies.Access hiding (Index)
import Data.Cone

-- scientific
import Data.Scientific hiding (scientific)

import Data.Functor.Compose
import Data.Kind
import GHC.OverloadedLabels (IsLabel, fromLabel)
import Prelude hiding (all)

-- conedec
import Conedec.Codec

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

(.:) :: Aeson.Key -> Codec c -> ObjectCodec c
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
fn <:: ca = getLensB (fn blenses) `specCodec` ca

infix 0 <::

newtype CodecAccess t a = CodecAccess {getCodecAccess :: forall f. Diagram t f -> f a}

instance HasB (Diagram t) l a => IsLabel l (CodecAccess t a) where
  fromLabel = CodecAccess $ get @l

at :: forall n t a. IxB (Diagram t) n a => CodecAccess t a
at = CodecAccess $ pos @n

(-::)
  :: (LensesB (Diagram t), CodecSpecMonad c t m)
  => CodecAccess t a
  -> c a
  -> m ()
fn -:: ca = getLensB (getCodecAccess fn blenses) `specCodec` ca

infix 0 -::

newtype CodecFieldAccess t a = CodecFieldAccess {getCodecFieldAccess :: (CodecAccess t a, String)}

instance (HasB (Diagram t) l a, LabeledB (Diagram t)) => IsLabel l (CodecFieldAccess t a) where
  fromLabel = CodecFieldAccess (a, getConst $ access blabeled)
   where
    a@(CodecAccess access) = fromLabel @l

(.::)
  :: (LensesB (Diagram t), CodecSpecMonad ObjectCodec t m)
  => CodecFieldAccess t a
  -> Codec a
  -> m ()
(CodecFieldAccess (CodecAccess fn, nm)) .:: ca =
  getLensB (fn blenses)
    `specCodec` (Aeson.fromString nm .: ca)

infix 0 .::

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
