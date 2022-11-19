{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Network.Wai.Handler.Warp (run)
import Web.Twain
import Data.Aeson

import Lib

main :: IO ()
main = do
  run 3002 $
    foldr ($)
      (notFound missing)
      [ get "/" index
      , post "echo:name" echo
      , post "json-matcher-1" jsonMatcher1
      ]

index :: ResponderM a
index = send $ html "Hello World!"

echo :: ResponderM a
echo = do
  name <- param "name"
  send $ html $ "Hello, " <> name

jsonMatcher1 :: ResponderM a
jsonMatcher1 = do
  send $ Web.Twain.json $ Null

missing :: ResponderM a
missing = send $ html "Not found..."
