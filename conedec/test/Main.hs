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
import qualified Data.Text as Text
import Prelude hiding (all, any, product)

data Contact
  = NoContact
  | Email Text.Text
  | Phone Int Text.Text
  deriving (Show)

data User = User
  { name :: Text.Text
  , age :: Int
  , contact :: Contact
  , friends :: [User]
  }
  deriving (Show)

$(makeDiagram ''Contact)
$(makeDiagram ''User)

data V1

instance Def "name" ValueCodec V1 Text.Text where unref = codecName
instance Def "user" ValueCodec V1 User where unref = codecUser

codecName :: Codec ValueCodec ctx Text.Text
codecName =
  text
    <?> "Given and last name"
      <!> "Jasper Christopher"

codecUser
  :: ( Def "name" ValueCodec ctx Text.Text
     , Def "user" ValueCodec ctx User
     )
  => Codec ValueCodec ctx User
codecUser =
  object
    ( all do
        #name <: ref @"name" <?> "The name of the user"
        #age <: boundIntegral
        #contact =: any do
          given ifEmail ~ "email" <: text
          given ifPhone ~ "phone" <: arrayAll do
            at @0 <: boundIntegral
            at @1 <: text
          given ifNoContact
            =: emptyObject
            <?> "Leave empty for no contact"
        #friends
          <: manyOfList (ref @"user")
    )
    <?> "A user of the system"
      <!> User
        { name = "Jon Doe"
        , age = 23
        , contact = Email "jon@doe.com"
        , friends = []
        }

main :: IO ()
main = do
  debugCodec @V1 (ref @"user")
