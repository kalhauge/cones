{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Data.Cone.TH

data Contact
  = NoContact
  | Email String
  | Phone Int String

data CornerCase f g h
  = NoCorners

data CornerCase2 x
  = NoCorners2 x

data User = User
  { name :: String
  , age :: Int
  , contact :: Contact
  }

-- $(makeDiagram ''Maybe)

-- $(makeDiagram ''CornerCase)

type CornerCase3 = CornerCase2 Int
$(makeDiagram ''CornerCase3)

$(makeDiagram ''Contact)
$(makeDiagram ''User)

main :: IO ()
main = do
  print ""
