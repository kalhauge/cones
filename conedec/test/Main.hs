{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Cone
import Data.Cone.TH

import Conedec
import Data.Scientific (Scientific)
import qualified Data.Text as Text
import Prelude hiding (product)

-- aeson
import Data.Aeson (encode)

-- bytestring
import qualified Data.ByteString.Lazy.Char8 as BS

data Contact
  = NoContact
  | Email Text.Text
  | Phone Scientific Text.Text

data User = User
  { name :: Text.Text
  , age :: Int
  , contact :: Contact
  }

$(makeDiagram ''Contact)
$(makeDiagram ''User)

codecUser :: Codec User
codecUser =
  object $
    allOf $
      UserD
        { getName =
            "name"
              .: (text <?> "Given and last name")
              <?> "The name of the user"
        , getAge =
            "age" .: boundIntegral
        , getContact =
            anyOf $
              ContactD
                { ifNoContact = EmptyObjectCodec <?> "Leave empty for no contact"
                , ifEmail = "email" .: text
                , ifPhone =
                    "phone"
                      .: ( array
                            . allOf
                            $ D2
                              { getFstOf2 = scientific
                              , getSndOf2 = text
                              }
                         )
                }
        }

main :: IO ()
main = do
  debugCodec codecUser
  BS.putStrLn $ encode (toJSONViaCodec codecUser $ User "Peter" 20 (Phone 21 "23244123"))
