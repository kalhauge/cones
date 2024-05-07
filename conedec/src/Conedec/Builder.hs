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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
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
import Data.Bifunctor (first)
import Data.Coerce
import Data.Functor.Identity
import Data.Kind
import Data.Monoid
import Data.Proxy (Proxy (..))
import Data.String
import GHC.TypeLits (KnownSymbol, symbolVal)

-- aeson
import qualified Data.Aeson.Key as Aeson

-- barbies
import Barbies

-- mtl
import Control.Monad.Reader
import Control.Monad.Writer

-- text
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text

-- cones
import Barbies.Access hiding (Index)
import Data.Cone

-- scientific
import Data.Scientific hiding (scientific)

import Data.Functor.Compose
import GHC.OverloadedLabels (IsLabel, fromLabel)
import Prelude hiding (all, any, null)

-- aeson
import qualified Data.Aeson as Aeson

-- bytestring
import qualified Data.ByteString as BS

-- text
import qualified Data.Text.Lazy.Encoding as TextLazy

-- vector
import qualified Data.Vector as V

-- prettyprinter
import qualified Prettyprinter as PP

-- conedec
import Conedec.Codec
import Conedec.Json
import Conedec.Json.Doc

{- $builders
These are the builders:
-}

any
  :: (IsColimit t, TraversableB (Diagram t))
  => (forall m. (CodecSpecMonad t e ctx ann m) => m ())
  -> Codec e ctx ann t
any o = SumCodec (runOrderM o) (runCodecM o)
{-# INLINE any #-}

all
  :: (IsLimit t, TraversableB (Diagram t))
  => (forall m. (CodecSpecMonad t e ctx ann m) => m ())
  -> Codec e ctx ann t
all o = ProductCodec (runOrderM o) (runCodecM o)
{-# INLINE all #-}

-- annotateMistakes
--   :: ( TraversableB (Diagram t)
--      , ApplicativeB (Diagram t)
--      , LabeledB (Diagram t)
--      )
--   => (forall m. CodecSpecMonad t e' ctx ann m => m ())
--   -> Codec e ctx ann a
--   -> Codec e ctx ann a
-- annotateMistakes o c' = fixMistakes c' mistakes
--  where
--   mistakes = bfoldMap (\(Pair (Const s) (Const (Sum a))) -> [(s, a) | a /= 1]) (bzip blabeled (runCountM o))
--   fixMistakes c = \case
--     [] -> c
--     (k, v) : ks ->
--       fixMistakes
--         ( c <?> ("warning: " <> fromString k <> " set " <> fromString (show v) <> " times")
--         )
--         ks
-- {-# INLINE annotateMistakes #-}

dimap
  :: (b -> Either String a)
  -> (a -> Either String b)
  -> Codec e ctx ann a
  -> Codec e ctx ann b
dimap = DimapCodec
{-# INLINE dimap #-}

bimap
  :: (b -> a)
  -> (a -> b)
  -> Codec e ctx ann a
  -> Codec e ctx ann b
bimap fa fb = dimap (pure . fa) (pure . fb)
{-# INLINE bimap #-}

untup :: Codec e ctx ann ((), b) -> Codec e ctx ann b
untup = bimap ((),) snd

data Tagged e ctx ann t where
  Tagged :: Aeson.Value -> Codec e ctx ann t -> Tagged e ctx ann t

tagged
  :: forall t ctx ann
   . (IsColimit t, TraversableB (Diagram t))
  => Aeson.Key
  -> (forall m. (CodecSpecMonad t (Tagged ObjectC) ctx ann m) => m ())
  -> Codec ObjectC ctx ann t
tagged tagfield o =
  let
    codec' :: Diagram t (Codec (Tagged ObjectC) ctx ann)
    codec' = runCodecM o

    xcodec :: Diagram t (Codec ObjectC ctx ann)
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

taggedInto
  :: forall t ctx ann
   . (IsColimit t, TraversableB (Diagram t))
  => Aeson.Key
  -> Aeson.Key
  -> (forall m. (CodecSpecMonad t (Tagged ValueC) ctx ann m) => m ())
  -> Codec ObjectC ctx ann t
taggedInto tagfield valuefield o =
  let
    codec' :: Diagram t (Codec (Tagged ValueC) ctx ann)
    codec' = runCodecM o

    xcodec :: Diagram t (Codec ObjectC ctx ann)
    xcodec =
      bmap
        ( cunfold
            ( \(Tagged tag c) ->
                let t = Two (ElementCodec $ FieldCodec tagfield (exact tag)) (ElementCodec $ FieldCodec valuefield c)
                 in untup . ProductCodec btraverse $ t
            )
        )
        codec'
   in
    SumCodec (runOrderM o) xcodec

(//) :: Aeson.Value -> Codec e ctx ann t -> Codec (Tagged e) ctx ann t
(//) k v = ElementCodec $ Tagged k v

infix 1 //

(~:) :: Aeson.Key -> Codec ValueC ctx ann t -> Codec ObjectC ctx ann t
(~:) k v = ElementCodec $ FieldCodec k v

infix 2 ~:

arrayAll
  :: (IsLimit t, TraversableB (Diagram t), LabeledB (Diagram t))
  => (forall m. (CodecSpecMonad t ArrayC ctx ann m) => m ())
  -> Codec ValueC ctx ann t
arrayAll fn = array (all fn)
{-# INLINE arrayAll #-}

objectAll
  :: (IsLimit t, TraversableB (Diagram t), LabeledB (Diagram t))
  => (forall m. (CodecSpecMonad t ObjectC ctx ann m) => m ())
  -> Codec ValueC ctx ann t
objectAll fn = object (all fn)
{-# INLINE objectAll #-}

arrayAny
  :: (IsColimit t, TraversableB (Diagram t), LabeledB (Diagram t))
  => (forall m. (CodecSpecMonad t ArrayC ctx ann m) => m ())
  -> Codec ValueC ctx ann t
arrayAny fn = array (any fn)
{-# INLINE arrayAny #-}

objectAny
  :: (IsColimit t, TraversableB (Diagram t), LabeledB (Diagram t))
  => (forall m. (CodecSpecMonad t ObjectC ctx ann m) => m ())
  -> Codec ValueC ctx ann t
objectAny fn = object (any fn)
{-# INLINE objectAny #-}

(<?>) :: Codec e ctx ann a -> ann -> Codec e ctx ann a
(<?>) = flip AnnotateCodec
infixl 6 <?>

infixl 6 <!>

class FromExample e ann where
  (<!>) :: Codec e ctx ann a -> a -> Codec e ctx ann a

instance FromExample ValueC Doc where
  c <!> a =
    AnnotateCodec
      ( withError
          (\msg -> "could not encode example: " <> fromString (unlines msg))
          $ PP.pretty . TextLazy.decodeUtf8 . Aeson.encode <$> toJSONViaCodec c a
      )
      c

exact :: Aeson.Value -> Codec ValueC ctx ann ()
exact = ElementCodec . ExactValueCodec

ref :: forall s ctx ann e a. (KnownSymbol s, Def s e ctx ann a) => Codec e ctx ann a
ref = ReferenceCodec (Ref @s) id

-- \$values

text :: Codec ValueC ctx ann Text.Text
text = ElementCodec StringCodec
{-# INLINE text #-}

null :: Codec ValueC ctx ann ()
null = exact Aeson.Null
{-# INLINE null #-}

scientific :: Codec ValueC ctx ann Scientific
scientific = ElementCodec NumberCodec
{-# INLINE scientific #-}

bool :: Codec ValueC ctx ann Bool
bool = ElementCodec BoolCodec
{-# INLINE bool #-}

object :: Codec ObjectC ctx ann a -> Codec ValueC ctx ann a
object = ElementCodec . ObjectCodec
{-# INLINE object #-}

array :: Codec ArrayC ctx ann a -> Codec ValueC ctx ann a
array = ElementCodec . ArrayCodec
{-# INLINE array #-}

manyOf
  :: Codec ValueC ctx ann a
  -> Codec ValueC ctx ann (V.Vector a)
manyOf = ElementCodec . ManyOfCodec
{-# INLINE manyOf #-}

mapOf
  :: Codec ValueC ctx ann a
  -> Codec ValueC ctx ann [(Aeson.Key, a)]
mapOf = ElementCodec . MapOfCodec
{-# INLINE mapOf #-}

manyOfList
  :: Codec ValueC ctx ann a
  -> Codec ValueC ctx ann [a]
manyOfList = bimap V.fromList V.toList . manyOf
{-# INLINE manyOfList #-}

broken :: Codec e ctx ann a
broken = BrokenCodec

simply :: (Coercible a b) => Codec e ctx ann a -> Codec e ctx ann b
simply = bimap coerce coerce

optional :: Codec ValueC ctx ann a -> Codec ValueC ctx ann (Maybe a)
optional ca = SumCodec btraverse (MaybeD{ifNothing = null, ifJust = ca})

class HasIgnore e where
  ignore :: Codec e ctx ann ()

emptyArray :: Codec ArrayC ctx ann ()
emptyArray = ElementCodec EmptyArrayCodec

emptyObject :: Codec ObjectC ctx ann ()
emptyObject = ElementCodec EmptyObjectCodec

instance HasIgnore ValueC where ignore = null
instance HasIgnore ArrayC where ignore = emptyArray
instance HasIgnore ObjectC where ignore = emptyObject

boundIntegral :: (Integral i, Bounded i) => Codec ValueC ctx ann i
boundIntegral =
  dimap
    (pure . fromIntegral)
    (maybe (Left "out of bounds") Right . toBoundedInteger)
    scientific
{-# INLINE boundIntegral #-}

realFloat :: (RealFloat i) => Codec ValueC ctx ann i
realFloat =
  bimap
    fromFloatDigits
    toRealFloat
    scientific
{-# INLINE realFloat #-}

-- | Might not work for all bytestrings
byteStringUtf8 :: Codec ValueC ctx ann BS.ByteString
byteStringUtf8 =
  dimap
    (first show . Text.decodeUtf8')
    (Right . Text.encodeUtf8)
    text

-- infix 7 .:
--
-- (.:) :: Aeson.Key -> Codec ValueC ctx ann c -> Codec ObjectC ctx c
-- (.:) k v = ElementCodec $ FieldCodec k v

class (Monad m) => CodecSpecMonad t e ctx ann m | m -> e t ctx ann where
  specCodec :: (forall f. LensB (Diagram t) f a) -> Codec e ctx ann a -> m ()

newtype Access t a = Access {getAccess :: forall f. LensB (Diagram t) f a}

infix 0 =:
infix 0 <:

(=:) :: (CodecSpecMonad t e ctx ann m) => Access t a -> Codec e ctx ann a -> m ()
(=:) (Access fn) = specCodec fn

class SubValueCodec e where
  type SubAccess e t a
  (<:) :: (CodecSpecMonad t e ctx ann m) => SubAccess e t a -> Codec ValueC ctx ann a -> m ()

instance SubValueCodec ArrayC where
  type SubAccess ArrayC t a = Access t a
  (<:) (Access fn) ca = specCodec fn (ElementCodec . SingleCodec $ ca)

data NamedAccess t a = NamedAccess (Access t a) Aeson.Key

(~) :: Access t a -> Aeson.Key -> NamedAccess t a
a ~ k = NamedAccess a k
{-# INLINE (~) #-}

instance SubValueCodec ObjectC where
  type SubAccess ObjectC t a = NamedAccess t a
  (<:) (NamedAccess (Access fn) k) ca = specCodec fn (ElementCodec . FieldCodec k $ ca)

instance (HasB (Diagram t) l a, LensesB (Diagram t)) => IsLabel l (Access t a) where
  fromLabel = given (get @l)

instance (HasB (Diagram t) l a, KnownSymbol l, LensesB (Diagram t)) => IsLabel l (NamedAccess t a) where
  fromLabel = NamedAccess (fromLabel @l) (Aeson.fromString (symbolVal (Proxy :: Proxy l)))

given :: forall t a. (LensesB (Diagram t)) => (forall f. Diagram t f -> f a) -> Access t a
given fn = Access $ getLensB (fn blenses)

at :: forall n t a. (IxB (Diagram t) n a, LensesB (Diagram t)) => Access t a
at = given (pos @n)

newtype OrderB b m g = OrderB (b (m `Compose` g) -> Ap m (Endo (b g)))
  deriving (Semigroup, Monoid) via (b (m `Compose` g) -> Ap m (Endo (b g)))

newtype CodecB b e ctx ann = CodecB (Endo (b (Codec e ctx)))
  deriving (Semigroup, Monoid) via Endo (b (Codec e ctx))

data Order t e ctx ann = forall a.
  OrderSpec
  { accessor :: forall f. LensB (Diagram t) f a
  , codec :: Codec e ctx ann a
  }

instance CodecSpecMonad t e ctx ann (Writer [Order t e ctx ann]) where
  specCodec fn a = tell [OrderSpec fn a]

newtype OrderM t (e :: Type -> Type -> Type -> Type) ctx ann m g a = OrderM
  { getOrderM
      :: Diagram t (m `Compose` g)
      -> Writer (Ap m (Endo (Diagram t g))) a
  }
  deriving (Functor, Applicative, Monad) via (ReaderT (Diagram t (m `Compose` g)) (Writer (Ap m (Endo (Diagram t g)))))

instance (Applicative m) => CodecSpecMonad t e ctx ann (OrderM t e ctx ann m g) where
  specCodec :: (forall f. LensB (Diagram t) f a) -> Codec e ctx ann a -> OrderM t e ctx ann m g ()
  specCodec l _ = OrderM \diag -> do
    tell (Ap (Endo . setter <$> getter diag))
   where
    setter ga = coerce . l (\_ -> Identity ga)
    getter = coerce . l Const
  {-# INLINE specCodec #-}

runOrderM
  :: (Applicative m, ApplicativeB (Diagram t))
  => OrderM t e ctx ann m g ()
  -> (forall a. f a -> m (g a))
  -> Diagram t f
  -> m (Diagram t g)
runOrderM (OrderM m) fn x =
  let dt = bmap (Compose . fn) x
   in fmap (\e -> appEndo e (bpure undefined)) . coerce $ execWriter (m dt)
{-# INLINE runOrderM #-}

newtype CodecM t e ctx ann a = CodecM {getCodecM :: Writer (Endo (Diagram t (Codec e ctx ann))) a}
  deriving (Functor, Applicative, Monad) via (Writer (Endo (Diagram t (Codec e ctx ann))))

instance CodecSpecMonad t e ctx ann (CodecM t e ctx ann) where
  specCodec :: (forall f. LensB (Diagram t) f a) -> Codec e ctx ann a -> CodecM t e ctx ann ()
  specCodec l ca = CodecM do
    tell (Endo $ setter ca)
   where
    setter ga = coerce . l (\_ -> Identity ga)
  {-# INLINE specCodec #-}

runCodecM
  :: (ApplicativeB (Diagram t))
  => CodecM t e ctx ann ()
  -> Diagram t (Codec e ctx ann)
runCodecM (CodecM m) = appEndo (execWriter m) (bpure undefined)
{-# INLINE runCodecM #-}

newtype CountM t (e :: Type -> Type -> Type -> Type) ctx ann a = CountM {getCountM :: Writer (Endo (Diagram t (Const (Sum Int)))) a}
  deriving (Functor, Applicative, Monad) via (Writer (Endo (Diagram t (Const (Sum Int)))))

instance CodecSpecMonad t e ctx ann (CountM t e ctx ann) where
  specCodec l _ = CountM do
    tell (Endo incr)
   where
    incr = coerce . l (\a -> Identity (a <> Const (Sum 1)))
  {-# INLINE specCodec #-}

runCountM
  :: (ApplicativeB (Diagram t))
  => CountM t e ctx ann ()
  -> Diagram t (Const (Sum Int))
runCountM (CountM m) = appEndo (execWriter m) (bpure mempty)
{-# INLINE runCountM #-}
