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

data Contact
  = NoContact
  | Email Text.Text
  | Phone Scientific Text.Text

data User = User
  { name :: Text.Text
  , -- , age :: Int
    contact :: Contact
  }

$(makeDiagram ''Contact)
$(makeDiagram ''User)

codecUser :: Codec User
codecUser =
  object $
    allOf $
      UserD
        { getName = "name" .: text
        , getContact =
            anyOf $
              ContactD
                { ifNoContact = EmptyObjectCodec
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
main = debugCodec codecUser
