module Main where

data Contact
  = Phone String
  | Email String

data User = User
  { name :: String
  , age :: Int
  , contact :: Contact
  }

main :: IO ()
main = do
  putStrLn "Success"
