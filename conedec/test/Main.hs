{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Cone
import Data.Cone.TH

import Conedec
import qualified Data.Text as Text
import Prelude hiding (product)

data Contact
  = NoContact
  | Email String
  | Phone Int String

data User = User
  { name :: Text.Text
  , -- , age :: Int
    contact :: Contact
  }

$(makeDiagram ''Contact)
$(makeDiagram ''User)

codecUser =
  object $
    product $
      def
        { getName = text
        }

main :: IO ()
main = putStrLn "Hello"
