{-# LANGUAGE DeriveGeneric #-}

module Lib
    ( someFunc
    ) where

import Data.Aeson
import GHC.Generics
import qualified Data.ByteString            as B
import qualified Data.ByteString.Lazy       as BL
import qualified Data.Text                  as T
import qualified Data.Text.Encoding         as T
import qualified Data.Text.IO               as T
import qualified Data.Text.Lazy             as TL
import qualified Data.Text.Lazy.Encoding    as TL
import qualified Data.Text.Lazy.IO          as TL
import Prelude                    as P

someFunc :: IO ()
someFunc = P.putStrLn "someFunc"

type Text = String

data Person = Person {
      name :: T.Text
    , age  :: Int
    } deriving (Generic, Eq, Show)

instance ToJSON Person where
    -- No need to provide a toJSON implementation.

    -- For efficiency, we write a simple toEncoding implementation, as
    -- the default version uses toJSON.
    toEncoding = genericToEncoding defaultOptions

instance FromJSON Person
    -- No need to provide a parseJSON implementation.

--decode "{\"foo\":1,\"bar\":2}" :: Maybe (Map String Int)
--
-- x1 = fmap (\x -> Data.Aeson.KeyMap.lookup (Data.Aeson.Key.fromString "body") ((Data.Map.elems x) !! 0)) (decode input :: Maybe (Map String Object))

main :: IO ()
main = P.print $ (decode (TL.encodeUtf8 . TL.pack $ "{\"name\":\"Joe\",\"age\":12}") :: Maybe Person)
