{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib
    ( someFunc
    ) where

import Data.List                  as L
import GHC.Generics
import Data.Aeson
import Data.ByteString            as B
import Data.ByteString.Lazy       as BL
import Data.Text                  as T
import Data.Text.Encoding         as T
import Data.Text.IO               as T
import Data.Text.Lazy             as TL
import Data.Text.Lazy.Encoding    as TL
import Data.Text.Lazy.IO          as TL
--import Data.Map                   as M
import Data.Aeson.KeyMap          as KM
import Data.Aeson.Key             as K
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

getData1 :: IO (Maybe Value)
getData1 = do
  fileData <- BL.readFile "/home/andrey/Work/lc/pyparts1.json"
  return $ decode fileData

getData :: IO (Maybe Value)
getData = do
  fileData <- BL.readFile "/home/andrey/Work/lc/pyparts.json"
  return $ decode fileData

t1 a = [show a]

main :: IO ()
--main = P.print $ (decode (TL.encodeUtf8 . TL.pack $ "{\"name\":\"Joe\",\"age\":12}") :: Maybe Person)
main = do
  fileData <- getData
  P.putStrLn $ case fileData of
       Nothing -> "error reading file"
       Just a -> "yess: " -- ++ show (KM.lookup (K.fromString "SimpleWhitespace") a)

isSubMapOf :: Object -> Value -> Bool
isSubMapOf e (Object a) = (P.all f . KM.toList) e where f (k, v) = KM.lookup k a == (Just v)
isSubMapOf _ _ = False

gather :: (Value -> Bool) -> Value -> [Value]
gather pred x = if (pred x) then [x] else case x :: Value of
            Object a -> P.concat (fmap (gather pred) $ KM.elems a)
            Array a -> P.concat (fmap (gather pred) a)
            _ -> []

-- x1 = (fmap . fmap) (gather (\x -> case x of Object a -> (KM.lookup (K.fromString "type") a) == Just (String "SimpleStatementLine"); _ -> False)) getData
-- (fmap . fmap) ((fmap (\x -> case x of Object a -> KM.lookup (K.fromString "annotation") a; _ -> error "woo")) . (gather (isSubMapOf (KM.fromList [((K.fromString "type"), String "AnnAssign")])))) getData
--
asKeyMap :: Value -> Object
asKeyMap (Object a) = a
asKeyMap _ = error "not a keymap"

-- fmap (>>= (\x -> case x of Object a -> Just a; _ -> Nothing)) getData
find1 b = Nothing

f1 :: IO (Maybe Value) -> IO ()
f1 theData = do
  d <- theData
  let r = do
            x <- d
            x <- case x of Object a -> Just (KM.toList a); _ -> Nothing
            x <- L.foldl' (\a (k, v) -> (\p -> (++[(k, p)])) <$> (find1 v) <*> a) (Just ([] :: [(Key, Value)])) x
            return $ P.concat $ fmap (\(k, v) -> (((++"\n") . K.toString) k) ++ ("\t" ++ show v ++ "\n") ++ "\n\n\n") x
  P.putStrLn $ case r of
       Just b -> b
       Nothing -> "Some error perhaps..."
