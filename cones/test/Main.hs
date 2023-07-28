{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Data.Cone.TH
import Language.Haskell.TH

data Contact
  = NoContact
  | Email String
  | Phone Int String

data CornerCase f g h
  = NoCorners

data User = User
  { name :: String
  , age :: Int
  , contact :: Contact
  }

$(makeDiagram ''Maybe)
$(makeDiagram ''CornerCase)
$(makeDiagram ''Contact)
$(makeDiagram ''User)

main :: IO ()
main = do
  print ""