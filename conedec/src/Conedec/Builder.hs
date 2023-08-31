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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
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
import qualified Data.Text.Lazy.Encoding as Text

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
import qualified Data.Aeson as Aeson
import Data.Functor.Product
import Data.Kind
import Data.Proxy (Proxy (..))
import Data.String
import qualified Data.Vector as V
import GHC.TypeLits (KnownSymbol, symbolVal)
import qualified Prettyprinter as PP

{- $builders
These are the builders:
-}

any
  :: (IsColimit t, TraversableB (Diagram t), LabeledB (Diagram t))
  => (forall m. CodecSpecMonad t e ctx m => m ())
  -> Codec e ctx t
any o = annotateMistakes o $ SumCodec (runOrderM o) (runCodecM o)
{-# INLINE any #-}

all
  :: (IsLimit t, TraversableB (Diagram t), LabeledB (Diagram t))
  => (forall m. CodecSpecMonad t e ctx m => m ())
  -> Codec e ctx t
all o = annotateMistakes o $ ProductCodec (runOrderM o) (runCodecM o)
{-# INLINE all #-}

annotateMistakes
  :: ( TraversableB (Diagram t)
     , ApplicativeB (Diagram t)
     , LabeledB (Diagram t)
     )
  => (forall m. CodecSpecMonad t e' ctx m => m ())
  -> Codec e ctx a
  -> Codec e ctx a
annotateMistakes o c' = fixMistakes c' mistakes
 where
  mistakes = bfoldMap (\(Pair (Const s) (Const (Sum a))) -> [(s, a) | a /= 1]) (bzip blabeled (runCountM o))
  fixMistakes c = \case
    [] -> c
    (k, v) : ks ->
      fixMistakes
        ( c <?> ("warning: " <> fromString k <> " set " <> fromString (show v) <> " times")
        )
        ks
{-# INLINE annotateMistakes #-}

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

data TaggedObjectCodec ctx t where
  Tagged :: Aeson.Value -> Codec ObjectCodec ctx t -> TaggedObjectCodec ctx t

untup :: Codec e ctx ((), b) -> Codec e ctx b
untup = bimap ((),) snd

tagged
  :: forall t ctx
   . (IsColimit t, TraversableB (Diagram t), LabeledB (Diagram t))
  => Aeson.Key
  -> (forall m. CodecSpecMonad t TaggedObjectCodec ctx m => m ())
  -> Codec ObjectCodec ctx t
tagged tagfield o =
  annotateMistakes o $
    let
      codec' :: Diagram t (Codec TaggedObjectCodec ctx)
      codec' = runCodecM o

      xcodec :: Diagram t (Codec ObjectCodec ctx)
      xcodec =
        bmap
          ( cunfold
              ( \(Tagged tag c) ->
                  let t = Two (ElementCodec $ FieldCodec tagfield (exact tag)) c
                   in untup . ProductCodec btraverse $ t
              )
          )
          codec'
     in
      SumCodec (runOrderM o) xcodec

(//) :: Aeson.Value -> Codec ObjectCodec ctx t -> Codec TaggedObjectCodec ctx t
(//) k v = ElementCodec $ Tagged k v

(~:) :: Aeson.Key -> Codec ValueCodec ctx t -> Codec ObjectCodec ctx t
(~:) k v = ElementCodec $ FieldCodec k v

arrayAll
  :: (IsLimit t, TraversableB (Diagram t), LabeledB (Diagram t))
  => (forall m. CodecSpecMonad t ArrayCodec ctx m => m ())
  -> Codec ValueCodec ctx t
arrayAll = array . all
{-# INLINE arrayAll #-}

objectAll
  :: (IsLimit t, TraversableB (Diagram t), LabeledB (Diagram t))
  => (forall m. CodecSpecMonad t ObjectCodec ctx m => m ())
  -> Codec ValueCodec ctx t
objectAll = object . all
{-# INLINE objectAll #-}

arrayAny :: (IsColimit t, TraversableB (Diagram t), LabeledB (Diagram t)) => (forall m. CodecSpecMonad t ArrayCodec ctx m => m ()) -> Codec ValueCodec ctx t
arrayAny = array . any
{-# INLINE arrayAny #-}

objectAny :: (IsColimit t, TraversableB (Diagram t), LabeledB (Diagram t)) => (forall m. CodecSpecMonad t ObjectCodec ctx m => m ()) -> Codec ValueCodec ctx t
objectAny = object . any
{-# INLINE objectAny #-}

(<?>) :: Codec e ctx a -> Doc -> Codec e ctx a
(<?>) = flip DocumentationCodec
infixl 6 <?>

(<!>) :: Codec ValueCodec ctx a -> a -> Codec ValueCodec ctx a
c <!> a =
  ExampleCodec
    a
    ( \a' ->
        withError
          (\msg -> "could not encode example: " <> fromString msg)
          (PP.pretty . Text.decodeUtf8 . Aeson.encode <$> toJSONViaCodec c a')
    )
    c
infixl 6 <!>

exact :: Aeson.Value -> Codec ValueCodec ctx ()
exact = ElementCodec . ExactValueCodec

ref :: forall s ctx e a. (KnownSymbol s, Def s e ctx a) => Codec e ctx a
ref = ReferenceCodec (Ref @s) id

-- \$values

text :: Codec ValueCodec ctx Text.Text
text = ElementCodec StringCodec
{-# INLINE text #-}

null :: Codec ValueCodec ctx ()
null = exact Aeson.Null
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

broken :: Codec e ctx a
broken = BrokenCodec

simply :: Coercible a b => Codec e ctx a -> Codec e ctx b
simply = bimap coerce coerce

optional :: Codec ValueCodec ctx a -> Codec ValueCodec ctx (Maybe a)
optional ca = SumCodec btraverse (MaybeD{ifNothing = null, ifJust = ca})

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

newtype CountM t (e :: Type -> Type -> Type) ctx a = CountM {getCountM :: Writer (Endo (Diagram t (Const (Sum Int)))) a}
  deriving (Functor, Applicative, Monad) via (Writer (Endo (Diagram t (Const (Sum Int)))))

instance CodecSpecMonad t e ctx (CountM t e ctx) where
  specCodec l _ = CountM do
    tell (Endo incr)
   where
    incr = coerce . l (\a -> Identity (a <> Const (Sum 1)))
  {-# INLINE specCodec #-}

runCountM
  :: (ApplicativeB (Diagram t))
  => CountM t e ctx ()
  -> Diagram t (Const (Sum Int))
runCountM (CountM m) = appEndo (execWriter m) (bpure mempty)
{-# INLINE runCountM #-}
