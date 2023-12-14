{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- Adapted from https://hackage.haskell.org/package/aeson-bson-0.3.0/docs/src/Data-Aeson-Bson.html

module Data.Aeson.Bson (
  toAeson, aesonifyValue,
  toBson, bsonifyValue
) where

import Data.Bson as BSON
import Data.Aeson.Types as AESON
import Data.Attoparsec.Number as Atto
import Data.Text as T hiding (map)
import Data.HashMap.Strict as Map (fromList, toList)
import Data.Vector as Vector (toList)
import Data.Aeson.KeyMap as KeyMap hiding (map)
import Data.Aeson.Key as Key
import Numeric
import qualified Data.Scientific as Sci
import qualified Data.Vector as V
import Data.Text             as T hiding (map)
import Data.Text.Encoding    as T

{-instance ToJSON BSON.Value where
  toJSON = aesonifyValue

instance ToJSON Document where
  toJSON = Object . toAeson-}

bsonifyValue :: AESON.Value -> BSON.Value
bsonifyValue (Object obj) = Doc $ toBson obj
bsonifyValue (AESON.Array array) = BSON.Array . map bsonifyValue . Vector.toList $ array
bsonifyValue (AESON.String str) = BSON.String str
bsonifyValue (Number n) = BSON.Float $ fromIntegral $ Sci.coefficient n
bsonifyValue (AESON.Bool b) = BSON.Bool b
bsonifyValue (AESON.Null) = BSON.Null

aesonifyValue :: BSON.Value -> AESON.Value
aesonifyValue (Float f) = toJSON f
aesonifyValue (BSON.String s) = toJSON s
aesonifyValue (Doc doc) = (Object . toAeson) doc
aesonifyValue (BSON.Array list) = AESON.Array $ V.fromList $ fmap aesonifyValue list
aesonifyValue (Bin (Binary binary)) = AESON.String $ T.decodeUtf8 binary
aesonifyValue (Fun (Function function)) = AESON.String $ T.decodeUtf8 function
aesonifyValue (Uuid (UUID uuid)) = AESON.String $ T.decodeUtf8 uuid
aesonifyValue (Md5 (MD5 md5)) = AESON.String $ T.decodeUtf8 md5
--aesonifyValue (UserDef (UserDefined userdef)) = toJSON userdef
aesonifyValue (ObjId (Oid w32 w64)) = toJSON $ showHex w32 (showHex w64 "")
aesonifyValue (BSON.Bool bool) = toJSON bool
aesonifyValue (UTC utc) = toJSON utc
aesonifyValue (BSON.Null) = AESON.Null
aesonifyValue (RegEx (Regex pattern mods)) = toJSON $
                                           '/' : T.unpack pattern ++
                                           '/' : T.unpack mods
--aesonifyValue (JavaScr (Javascript env code)) = toJSON . Map.fromList $
--                                              [ (T.pack "environment", toJSON env)
--                                              , (T.pack "code", toJSON code)]
aesonifyValue (Sym (Symbol sym)) = toJSON sym
aesonifyValue (Int32 int32) = toJSON int32
aesonifyValue (Int64 int64) = toJSON int64
aesonifyValue (Stamp (MongoStamp int64)) = toJSON int64
aesonifyValue (MinMax mm) = case mm of { MinKey -> toJSON (-1 :: Int)
                                       ; MaxKey -> toJSON (1 :: Int)}


toBson :: AESON.Object -> BSON.Document
toBson = map (\(t, v) -> ((Key.toText t) := bsonifyValue v)) . KeyMap.toList

toAeson :: BSON.Document -> AESON.Object
toAeson = KeyMap.fromList . map (\(l := v) -> (Key.fromText l, aesonifyValue v))
