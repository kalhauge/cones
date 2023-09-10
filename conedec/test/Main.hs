{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Cone.TH

import Conedec
import Conedec.Json
import Conedec.Json.Doc (debugCodec)
import Data.String
import qualified Data.Text as Text
import Prelude hiding (all, any, product)

data Color
  = Blue
  | Red
  | Yellow
  deriving (Show, Bounded)

data Contact
  = NoContact
  | Email Text.Text
  | Phone Int Text.Text
  deriving (Show)

data User = User
  { name :: Text.Text
  , age :: Int
  , favoriteColor :: Maybe Color
  , contact :: Contact
  , friends :: [User]
  }
  deriving (Show)

$(makeDiagram ''Contact)
$(makeDiagram ''Color)
$(makeDiagram ''User)

data V1

instance (IsString ann, FromExample ValueC ann) => Def "name" ValueC V1 ann Text.Text where
  def =
    text
      <?> "Given and last name"
        <!> "Jasper Christopher"

instance Def "color" ValueC V1 ann Color where
  def = any do
    #ifBlue =: "blue"
    #ifRed =: "red"
    #ifYellow =: "yellow"

instance (IsString ann, FromExample ValueC ann) => Def "user" ValueC V1 ann User where
  def = codecUser

-- codecContact2
--   :: Codec ValueC ctx Doc Contact
-- codecContact2 = object $ tagged "type" $ do
--   #ifEmail =: "email" // do
--     "email" ~: text
--   #ifPhone =: "phone" // all do
--     at @0 ~ "contry" <: boundIntegral
--     at @1 ~ "phone" <: text
--   #ifNoContact
--     =: "no-contact"
--     // emptyObject
--     <?> "Leave empty for no contact"

codecUser
  :: ( IsString ann
     , FromExample ValueC ann
     , Def "name" ValueC ctx ann Text.Text
     , Def "user" ValueC ctx ann User
     , Def "color" ValueC ctx ann Color
     )
  => Codec ValueC ctx ann User
codecUser =
  object
    ( all do
        #name <: ref @"name" <?> "The name of the user"
        #age <: boundIntegral
        #favoriteColor <: optional (ref @"color")
        #contact =: any do
          #ifEmail ~ "email" <: text
          #ifPhone ~ "phone" <: arrayAll do
            at @0 <: boundIntegral
            at @1 <: text
          #ifNoContact
            =: emptyObject
            <?> "Leave empty for no contact"
        #friends
          <: manyOfList (ref @"user")
    )
    <?> "A user of the system"
      <!> User
        { name = "Jon Doe"
        , age = 23
        , favoriteColor = Nothing
        , contact = Email "jon@doe.com"
        , friends = []
        }

main :: IO ()
main = do
  debugCodec @V1 (ref @"user")
