{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- |

Stability: experimental

Builders
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
import GHC.OverloadedLabels (IsLabel, fromLabel)
import Prelude hiding (all, any, null)

-- conedec
import Conedec.Codec
import Data.Kind
import Data.Proxy (Proxy (..))
import qualified Data.Vector as V
import GHC.TypeLits (KnownSymbol, symbolVal)

{- $builders
These are the builders:
-}

any
  :: (IsColimit t)
  => (forall m. CodecSpecMonad t e ctx m => m ())
  -> Codec e ctx t
any o = SumCodec (runOrderM o) (runCodecM o)
{-# INLINE any #-}

all
  :: (IsLimit t)
  => (forall m. CodecSpecMonad t e ctx m => m ())
  -> Codec e ctx t
all o = ProductCodec (runOrderM o) (runCodecM o)
{-# INLINE all #-}

dimap
  :: (b -> Either String a)
  -> (a -> Either String b)
  -> Codec e ctx a
  -> Codec e ctx b
dimap = DimapCodec
{-# INLINE dimap #-}

bimap
  :: (b -> a)
  -> (a -> b)
  -> Codec e ctx a
  -> Codec e ctx b
bimap fa fb = dimap (pure . fa) (pure . fb)
{-# INLINE bimap #-}

arrayAll
  :: (IsLimit t)
  => (forall m. CodecSpecMonad t ArrayCodec ctx m => m ())
  -> Codec ValueCodec ctx t
arrayAll = array . all
{-# INLINE arrayAll #-}

objectAll
  :: (IsLimit t)
  => (forall m. CodecSpecMonad t ObjectCodec ctx m => m ())
  -> Codec ValueCodec ctx t
objectAll = object . all
{-# INLINE objectAll #-}

arrayAny :: IsColimit t => (forall m. CodecSpecMonad t ArrayCodec ctx m => m ()) -> Codec ValueCodec ctx t
arrayAny = array . any
{-# INLINE arrayAny #-}

objectAny :: IsColimit t => (forall m. CodecSpecMonad t ObjectCodec ctx m => m ()) -> Codec ValueCodec ctx t
objectAny = object . any
{-# INLINE objectAny #-}

(<?>) :: Codec e ctx a -> Text.Text -> Codec e ctx a
(<?>) = flip DocumentationCodec
infixl 6 <?>

ref :: forall s ctx e a. (KnownSymbol s, Def s e ctx a) => Codec e ctx a
ref = ReferenceCodec (Ref @s)

-- \$values

text :: Codec ValueCodec ctx Text.Text
text = ElementCodec StringCodec
{-# INLINE text #-}

null :: Codec ValueCodec ctx ()
null = ElementCodec NullCodec
{-# INLINE null #-}

scientific :: Codec ValueCodec ctx Scientific
scientific = ElementCodec NumberCodec
{-# INLINE scientific #-}

bool :: Codec ValueCodec ctx Bool
bool = ElementCodec BoolCodec
{-# INLINE bool #-}

object :: Codec ObjectCodec ctx a -> Codec ValueCodec ctx a
object = ElementCodec . ObjectCodec
{-# INLINE object #-}

array :: Codec ArrayCodec ctx a -> Codec ValueCodec ctx a
array = ElementCodec . ArrayCodec
{-# INLINE array #-}

manyOf
  :: Codec ValueCodec ctx a
  -> Codec ValueCodec ctx (V.Vector a)
manyOf = ElementCodec . ManyOfCodec
{-# INLINE manyOf #-}

manyOfList
  :: Codec ValueCodec ctx a
  -> Codec ValueCodec ctx [a]
manyOfList = bimap V.fromList V.toList . manyOf
{-# INLINE manyOfList #-}

class HasIgnore e where
  ignore :: Codec e ctx ()

emptyArray :: Codec ArrayCodec ctx ()
emptyArray = ElementCodec EmptyArrayCodec

emptyObject :: Codec ObjectCodec ctx ()
emptyObject = ElementCodec EmptyObjectCodec

instance HasIgnore ValueCodec where ignore = null
instance HasIgnore ArrayCodec where ignore = emptyArray
instance HasIgnore ObjectCodec where ignore = emptyObject

boundIntegral :: (Integral i, Bounded i) => Codec ValueCodec ctx i
boundIntegral =
  dimap
    (pure . fromIntegral)
    (maybe (Left "out of bounds") Right . toBoundedInteger)
    scientific
{-# INLINE boundIntegral #-}

-- infix 7 .:
--
-- (.:) :: Aeson.Key -> Codec ValueCodec ctx c -> Codec ObjectCodec ctx c
-- (.:) k v = ElementCodec $ FieldCodec k v

class Monad m => CodecSpecMonad t e ctx m | m -> e t ctx where
  specCodec :: (forall f. LensB (Diagram t) f a) -> Codec e ctx a -> m ()

newtype Access t a = Access {getAccess :: forall f. LensB (Diagram t) f a}

infix 0 =:
infix 0 <:

(=:) :: CodecSpecMonad t e ctx m => Access t a -> Codec e ctx a -> m ()
(=:) (Access fn) = specCodec fn

class SubValueCodec e where
  type SubAccess e t a
  (<:) :: CodecSpecMonad t e ctx m => SubAccess e t a -> Codec ValueCodec ctx a -> m ()

instance SubValueCodec ArrayCodec where
  type SubAccess ArrayCodec t a = Access t a
  (<:) (Access fn) ca = specCodec fn (ElementCodec . SingleCodec $ ca)

data NamedAccess t a = NamedAccess (Access t a) Aeson.Key

(~) :: Access t a -> Aeson.Key -> NamedAccess t a
a ~ k = NamedAccess a k
{-# INLINE (~) #-}

instance SubValueCodec ObjectCodec where
  type SubAccess ObjectCodec t a = NamedAccess t a
  (<:) (NamedAccess (Access fn) k) ca = specCodec fn (ElementCodec . FieldCodec k $ ca)

instance (HasB (Diagram t) l a, LensesB (Diagram t)) => IsLabel l (Access t a) where
  fromLabel = given (get @l)

instance (HasB (Diagram t) l a, KnownSymbol l, LensesB (Diagram t)) => IsLabel l (NamedAccess t a) where
  fromLabel = NamedAccess (fromLabel @l) (Aeson.fromString (symbolVal (Proxy :: Proxy l)))

given :: forall t a. LensesB (Diagram t) => (forall f. Diagram t f -> f a) -> Access t a
given fn = Access $ getLensB (fn blenses)

at :: forall n t a. (IxB (Diagram t) n a, LensesB (Diagram t)) => Access t a
at = given (pos @n)

newtype OrderB b m g = OrderB (b (m `Compose` g) -> Ap m (Endo (b g)))
  deriving (Semigroup, Monoid) via (b (m `Compose` g) -> Ap m (Endo (b g)))

newtype CodecB b e ctx = CodecB (Endo (b (Codec e ctx)))
  deriving (Semigroup, Monoid) via Endo (b (Codec e ctx))

data Order t e ctx = forall a.
  OrderSpec
  { accessor :: forall f. LensB (Diagram t) f a
  , codec :: Codec e ctx a
  }

instance CodecSpecMonad t e ctx (Writer [Order t e ctx]) where
  specCodec fn a = tell [OrderSpec fn a]

-- newtype CompleteM t (e :: Type -> Type -> Type) ctx m g a = CompleteM {getCompleteM :: Writer (Diagram t ExactlyOnce) a}
--   deriving (Functor, Applicative, Monad) via (ReaderT (Diagram t (m `Compose` g)) (Writer (Ap m (Endo (Diagram t g)))))

newtype OrderM t (e :: Type -> Type -> Type) ctx m g a = OrderM {getOrderM :: Diagram t (m `Compose` g) -> Writer (Ap m (Endo (Diagram t g))) a}
  deriving (Functor, Applicative, Monad) via (ReaderT (Diagram t (m `Compose` g)) (Writer (Ap m (Endo (Diagram t g)))))

instance Applicative m => CodecSpecMonad t e ctx (OrderM t e ctx m g) where
  specCodec :: (forall f. LensB (Diagram t) f a) -> Codec e ctx a -> OrderM t e ctx m g ()
  specCodec l _ = OrderM \diag -> do
    tell (Ap (Endo . setter <$> getter diag))
   where
    setter ga = coerce . l (\_ -> Identity ga)
    getter = coerce . l Const
  {-# INLINE specCodec #-}

runOrderM
  :: (Applicative m, ApplicativeB (Diagram t))
  => OrderM t e ctx m g ()
  -> (forall a. f a -> m (g a))
  -> Diagram t f
  -> m (Diagram t g)
runOrderM (OrderM m) fn x =
  let dt = bmap (Compose . fn) x
   in fmap (\e -> appEndo e (bpure undefined)) . coerce $ execWriter (m dt)
{-# INLINE runOrderM #-}

newtype CodecM t e ctx a = CodecM {getCodecM :: Writer (Endo (Diagram t (Codec e ctx))) a}
  deriving (Functor, Applicative, Monad) via (Writer (Endo (Diagram t (Codec e ctx))))

instance CodecSpecMonad t e ctx (CodecM t e ctx) where
  specCodec :: (forall f. LensB (Diagram t) f a) -> Codec e ctx a -> CodecM t e ctx ()
  specCodec l ca = CodecM do
    tell (Endo $ setter ca)
   where
    setter ga = coerce . l (\_ -> Identity ga)
  {-# INLINE specCodec #-}

runCodecM
  :: (ApplicativeB (Diagram t))
  => CodecM t e ctx ()
  -> Diagram t (Codec e ctx)
runCodecM (CodecM m) = appEndo (execWriter m) (bpure undefined)
{-# INLINE runCodecM #-}
