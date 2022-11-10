{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib
    ( someFunc
    ) where

import qualified Data.Vector.Generic
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
import qualified Data.Scientific as Sci
import qualified Data.Vector as V
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
asKeyMap :: Value -> Maybe Object
asKeyMap (Object a) = Just a
asKeyMap _ = Nothing

asArray :: Value -> Maybe [Value]
asArray (Array a) = Just $ Data.Vector.Generic.toList a
asArray _ = Nothing

mHead (x:_) = Just x
mHead _ = Nothing

ff a = do
  a <- asKeyMap a
  a <- KM.lookup (K.fromString "body") a
  a <- asArray a
  return $ P.filter (isSubMapOf (KM.fromList [((K.fromString "type"), String "AnnAssign")])) a

-- fmap (>>= (\x -> case x of Object a -> Just a; _ -> Nothing)) getData
find1 x = do
  x <- asKeyMap x
  x <- KM.lookup (K.fromString "body") x
  x <- asKeyMap x
  x <- KM.lookup (K.fromString "body") x
  x <- asArray x
  --x <- return $ P.concat $ fmap (\x -> if (isSubMapOf (KM.fromList [((K.fromString "type"), String "SimpleStatementLine")])) then x) x
  x <- return $ P.filter (isSubMapOf (KM.fromList [((K.fromString "type"), String "SimpleStatementLine")])) x
  (fmap . fmap) encode $ fmap P.concat $ P.traverse ff x

f1 :: IO (Maybe Value) -> IO ()
f1 theData = do
  d <- theData
  let r = do
            x <- d
            x <- case x of Object a -> Just (KM.toList a); _ -> Nothing
            x <- L.foldl' (\a (k, v) -> (\p -> (++[(k, p)])) <$> (find1 v) <*> a) (Just mempty) x
            return $ P.concat $ fmap (\(k, v) -> (((++"\n") . K.toString) k) ++ ("\t" ++ show v ++ "\n") ++ "\n\n\n") x
  P.putStrLn $ case r of
       Just b -> b
       Nothing -> "Some error perhaps..."

-- | A JSON \"object\" (key\/value map).
type MatchObject = KeyMap MatchPattern

-- | A JSON \"array\" (sequence).
type MatchArray = V.Vector MatchPattern -- TODO just use list?

data MatchPattern = MatchObject !MatchObject -- literal
                  -- | MatchArray !MatchArray -- literal
                  | MatchString !T.Text
                  | MatchNumber !Sci.Scientific
                  | MatchBool !Bool
                  | MatchNull
                  | MatchLiteral
                  | MatchAny
                  | MatchAnyResult !Value
                  | MatchAnyResultU
                  | MatchObjectPartial !MatchObject -- specific
                  | MatchObjectPartialResult Value !MatchObject -- specific
                  | MatchObjectPartialResultU !MatchObject -- specific
                  -- | MatchArrayAll !MatchPattern -- specific
                  | MatchArraySome !MatchPattern -- specific
                  | MatchArraySomeResult [(Int, Value)] [(Int, MatchPattern)] -- specific
                  | MatchArraySomeResultU [(Int, MatchPattern)] -- specific
                    deriving (Eq, Show)

-- pattern -> value -> result
matchPattern :: MatchPattern -> Value -> Maybe MatchPattern
matchPattern (MatchObject m) (Object a) = if keys m /= keys a then Nothing else fmap (MatchObject . KM.fromList) $ L.foldl' f (Just []) (keys m)
  where f acc k = do
          acc' <- acc
          m' <- KM.lookup k m
          a' <- KM.lookup k a
          p <- matchPattern m' a'
          return $ acc' ++ [(k, p)]

matchPattern (MatchObjectPartial m) (Object a) = fmap (MatchObjectPartialResult leftOver) $ L.foldl' f (Just mempty) (keys m)
  where leftOver = Object $ KM.difference a m
        f acc k = do
          acc' <- acc
          m' <- KM.lookup k m
          a' <- KM.lookup k a
          p <- matchPattern m' a'
          return $ KM.insert k p acc'

matchPattern (MatchArraySome m) (Array a) = do
  let f acc (idx, e) = do
          (a1, a2) <- acc
          return $ case matchPattern m e of
                      Nothing -> (a1 ++ [(idx, e)], a2)
                      Just r -> (a1, a2 ++ [(idx, r)])
  (a1, a2) <- L.foldl' f (Just (mempty, mempty)) $ P.zip [0..] (V.toList a)
  --(a1, a2) <- if P.length a2 == 0 then Nothing else Just (a1, a2)
  return $ MatchArraySomeResult a1 a2

--matchPattern (MatchArray m) (Array a) = Nothing
matchPattern MatchAny a = Just $ MatchAnyResult a
-- valueless
matchPattern (MatchString m) (String a) = if m == a then Just MatchLiteral else Nothing
matchPattern (MatchNumber m) (Number a) = if m == a then Just MatchLiteral else Nothing
matchPattern (MatchBool m) (Bool a) = if m == a then Just MatchLiteral else Nothing
matchPattern MatchNull Null = Just MatchLiteral
-- valued
matchPattern MatchLiteral (String a) = Just $ MatchString a
matchPattern MatchLiteral (Number a) = Just $ MatchNumber a
matchPattern MatchLiteral (Bool a) = Just $ MatchBool a
matchPattern MatchLiteral Null = Just $ MatchNull
-- default case
matchPattern _ _ = Nothing

-- matchPattern (MatchString $ T.pack "abcd") (String $ T.pack "abcd")
-- matchPattern (MatchNumber 11.0) (Number 11.0)
-- matchPattern (MatchBool True) (Bool True)
-- matchPattern MatchNull Null

-- pattern -> result -> Either String Value
applyPattern :: MatchPattern -> MatchPattern -> Either String Value
applyPattern (MatchObjectPartial m) (MatchObjectPartialResult m1 m2) = do
  -- <- KM.union m1 (Object a)
  let f a b = a
  mm <- if keys m /= keys m2 then Left "Keys mismatch" else Right $ L.foldl' f (KM.empty) (keys m)
  let m2e err x = case x of
                   Nothing -> Left err
                   Just a -> Right a
  m1' <- (m2e "Map mismatch") $ asKeyMap $ m1
  return $ Object $ KM.union m1' mm

applyPattern (MatchArraySome m) (MatchArraySomeResult a1 a2) = do
  let f a idx = do
          a' <- a
          x <- case P.lookup idx a1 of
                    Just v -> Right v
                    Nothing -> case P.lookup idx a2 of
                                    Nothing -> Left "Index not found"
                                    Just r -> applyPattern m r
          return $ a' ++ [x]
  xx <- (L.foldl' f (Right []) [0..(P.length a1 + P.length a2 - 1)])
  xx <- if P.length xx > 0 then Right xx else Left "..."
  return $ (Array . V.fromList) xx

-- valueless
applyPattern (MatchString m) MatchLiteral = Right (String m)
applyPattern (MatchNumber m) MatchLiteral = Right (Number m)
applyPattern (MatchBool m) MatchLiteral = Right (Bool m)
applyPattern MatchNull MatchLiteral = Right Null

-- valued
applyPattern MatchLiteral (MatchString m) = Right (String m)
applyPattern MatchLiteral (MatchNumber m) = Right (Number m)
applyPattern MatchLiteral (MatchBool m) = Right (Bool m)
applyPattern MatchLiteral MatchNull = Right Null
-- ...
applyPattern _ _ = Left "Unknown error"

resetUnsignificant (MatchObjectPartialResult _ a) = MatchObjectPartialResultU (fmap resetUnsignificant a)
resetUnsignificant (MatchArraySomeResult _ a) = MatchArraySomeResultU ((fmap . fmap) resetUnsignificant a)
resetUnsignificant (MatchAnyResult _) = MatchAnyResultU
resetUnsignificant a = a

matchToValueMinimal :: MatchPattern -> Maybe Value
matchToValueMinimal (MatchObjectPartialResultU m) = fmap Object $ ifNotEmpty =<< L.foldl' f (Just mempty) (keys m)
  where
    ifNotEmpty m = if KM.null m then Nothing else Just m
    f acc k = do
          acc' <- acc
          v <- KM.lookup k m
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> KM.insert k x acc'
matchToValueMinimal (MatchArraySomeResultU m) = fmap Array $ ifNotEmpty =<< L.foldl' f (Just (V.empty :: V.Vector Value)) arr
  where
    arr = V.fromList $ fmap snd m
    ifNotEmpty m = if V.null m then Nothing else Just m
    f acc v = do
          acc' <- acc
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> V.snoc acc' x
matchToValueMinimal (MatchString m) = Just (String m)
matchToValueMinimal (MatchNumber m) = Just (Number m)
matchToValueMinimal (MatchBool m) = Just (Bool m)
matchToValueMinimal MatchNull = Just Null
--matchToValueMinimal (MatchAny a) = Nothing
matchToValueMinimal _ = Nothing

p1 theData = do
  d <- theData
  let v = do
        d' <- d
        d'' <- asKeyMap d'
        let f vv = do
              r <- matchPattern (MatchObjectPartial
                                (fromList [
                                  (fromString "type", MatchString $ T.pack "ClassDef"),
                                  (fromString "body", (MatchObjectPartial
                                                      (fromList [
                                                        (fromString "type", MatchString $ T.pack "IndentedBlock"),
                                                        (fromString "body", MatchArraySome (MatchObjectPartial (fromList [
                                                          (fromString "type", MatchString $ T.pack "SimpleStatementLine"),
                                                          (fromString "body", MatchArraySome (MatchObjectPartial (fromList [
                                                              (fromString "type", MatchString $ T.pack "AnnAssign"),
                                                              (fromString "target", (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name"),
                                                                                                                   (fromString "value", MatchLiteral)])))
                                                            ])))
  
                                                            --(fromString "annotation", )
                                                        ])))
                                                      ])))
                              ])) vv
              r <- return $ resetUnsignificant r
              return r
        return $ fmap f (elems d'')
  return v

--data MatchResult = ...

{-
MatchPartialMap
Match...
-}

--match1 = Object (fromList [("body", Object (fromList [("body", v)]))])
--f2 (Object a) = 
