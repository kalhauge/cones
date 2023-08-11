{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Cone
import Data.Cone.TH

import Conedec
import qualified Data.Text as Text
import Prelude hiding (all, any, product)

-- aeson
import Data.Aeson (encode)

-- bytestring

import Data.Aeson.Types (parse)
import qualified Data.ByteString.Lazy.Char8 as BS

data Contact
  = NoContact
  | Email Text.Text
  | Phone Int Text.Text
  deriving (Show)

data User = User
  { name :: Text.Text
  , age :: Int
  , contact :: Contact
  }
  deriving (Show)

$(makeDiagram ''Contact)
$(makeDiagram ''User)

codecName :: Codec Text.Text
codecName = text <?> "Given and last name"

codecUser :: Codec User
codecUser =
  object $ all do
    getName
      <:: "name"
      .: codecName
      <?> "The name of the user"
    getAge
      <:: "age"
      .: boundIntegral
    getContact
      <:: any do
        ifEmail
          <:: "email"
          .: text
        ifPhone
          <:: "phone"
          .: arrayAll do
            getFstOf2 <:: boundIntegral
            getSndOf2 <:: text
        ifNoContact
          <:: EmptyObjectCodec
          <?> "Leave empty for no contact"

main :: IO ()
main = do
  debugCodec codecUser
  value <- toJSONViaCodec codecUser $ User "Peter" 20 (Phone 21 "23244123")
  BS.putStrLn $ encode value
  print $ parse (parseJSONViaCodec codecUser) value
