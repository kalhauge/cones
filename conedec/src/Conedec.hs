{- |

A cone based Codec implementation.
-}
module Conedec where

import Data.Scientific

-- text
import qualified Data.Text as Text

-- | The codec, used to implement `toJSON`, `fromJSON`, and `toEncoding`
data Codec t where
  EmptyCodec
    :: Codec t
    -- ^ A codec that consumes everything and produces nothing.
    -- Should not be used in production
  ObjectCodec
    :: ObjectCodec t
    -> Codec t
  ArrayCodec
    :: Codec t
    -> Codec [t]
  NullableCodec
    :: Codec t
    -> Codec (Maybe t)
  ScientificCodec
    :: Codec Scientific
  TextCodec
    :: Codec Text.Text
  BoolCodec
    :: Codec Bool

data ObjectCodec t
