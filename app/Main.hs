{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Network.Wai.Handler.Warp (run)
import Web.Twain

import Lib

main :: IO ()
main = do
  run 3002 $
    foldr ($)
      (notFound missing)
      [ get "/" index
      , post "echo:name" echo
      ]

index :: ResponderM a
index = send $ html "Hello World!"

echo :: ResponderM a
echo = do
  name <- param "name"
  send $ html $ "Hello, " <> name

missing :: ResponderM a
missing = send $ html "Not found..."
