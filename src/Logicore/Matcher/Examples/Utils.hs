module Logicore.Matcher.Examples.Utils where

import Data.ByteString.Lazy       as BL
import Data.Aeson

--getD :: IO (Maybe Value)
getD a = do
  fileData <- BL.readFile a
  return $ decode fileData
