{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}


module Lib where

import qualified Data.Vector.Generic
import qualified Data.Set
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
import Control.Monad
import qualified Data.ByteString.UTF8       as BLU
import Data.Fix

data MatchResult a = MatchSuccess a
                 | MatchFailure String
                 | NoMatch String
                 deriving (Eq, Show)

instance Functor MatchResult where
  fmap f (MatchSuccess m) = MatchSuccess (f m)
  fmap _ (MatchFailure x) = MatchFailure x
  fmap _ (NoMatch x) = NoMatch x

instance Applicative MatchResult where
  (<*>) (MatchSuccess f) (MatchSuccess m) = MatchSuccess (f m)
  (<*>) _ (MatchFailure x) = (MatchFailure x)
  (<*>) (MatchFailure x) _ = (MatchFailure x)
  pure x = MatchSuccess x

instance Monad MatchResult where
  --join (MatchSuccess (MatchSuccess x)) = MatchSuccess x
  --join (MatchFailure (MatchFailure x)) = MatchFailure x
  --join NoMatch = NoMatch
  (>>=) (MatchSuccess m) f = f m
  (>>=) (MatchFailure m) _ = (MatchFailure m)
  (>>=) (NoMatch m) _ = (NoMatch m)

-- CF matcher

data ContextFreeGrammar a = SeqNode [(ContextFreeGrammar a)]
                          | StarNode [(ContextFreeGrammar a)]
                          | PlusNode [(ContextFreeGrammar a)]
                          | OrNode String (ContextFreeGrammar a)
                          | OptionalNodeValue (ContextFreeGrammar a)
                          | OptionalNodeEmpty
                          | CharNode a -- i.e. result node
                          | Char a
                          | Seq [(ContextFreeGrammar a)]
                          | Or [(String, (ContextFreeGrammar a))]
                          | Star (ContextFreeGrammar a)
                          | Plus (ContextFreeGrammar a)
                          | Optional (ContextFreeGrammar a)
                            deriving (Generic, Eq, Show)

instance ToJSON a => ToJSON (ContextFreeGrammar a) where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON a => FromJSON (ContextFreeGrammar a)

contextFreeMatch' :: (Eq a, Show a, Show b) => ContextFreeGrammar a -> [b] -> (a -> b -> MatchResult a) -> MatchResult ([b], ContextFreeGrammar a)
contextFreeMatch' (Char _) [] matchFn = NoMatch "can't read char"
contextFreeMatch' (Char a) (x:xs) matchFn =
  case matchFn a x of
       NoMatch s -> NoMatch ("no char match: " ++ s)
       MatchFailure s -> MatchFailure s
       MatchSuccess a -> MatchSuccess (xs, CharNode a)

contextFreeMatch' (Seq as) xs matchFn = (fmap . fmap) SeqNode $ L.foldl' f (MatchSuccess (xs, mempty)) as
  where f acc' a = do
          (xs, result) <- acc'
          (xs', result') <- contextFreeMatch' a xs matchFn
          return (xs', result ++ [result'])

contextFreeMatch' (Or as) xs matchFn = L.foldr f (NoMatch "or mismatch") as
  where f (opt, a) b = do
          case contextFreeMatch' a xs matchFn of
               NoMatch _ -> b
               MatchSuccess (xs', r) -> MatchSuccess (xs', OrNode opt r)

contextFreeMatch' (Star a) xs matchFn = (fmap . fmap) StarNode $ L.foldl' f (MatchSuccess (xs, mempty)) xs
  where f acc' b = do
          acc@(xs, result) <- acc'
          case contextFreeMatch' a xs matchFn of
               NoMatch _ -> MatchSuccess acc
               MatchSuccess (xs', result') -> MatchSuccess (xs', result ++ [result'])

contextFreeMatch' (Plus a) xs matchFn = do
  (xs', subresult) <- contextFreeMatch' (Seq [a, Star a]) xs matchFn
  rs' <- case subresult of
              (SeqNode [r, (StarNode rs)]) -> MatchSuccess (r:rs)
              _ -> NoMatch "impossible"
  return (xs', (PlusNode rs'))
  

contextFreeMatch' (Optional a) xs matchFn = do
  return $ case contextFreeMatch' a xs matchFn of
       NoMatch _ -> (xs, OptionalNodeEmpty)
       MatchSuccess (xs', subresult) -> (xs', OptionalNodeValue subresult)

contextFreeMatch' a xs matchFn = error ("no match for: " ++ (show a) ++ " " ++ (show xs))

--contextFreeMatch (Or a) xs = if a /= x then Left "char mismatch" else (xs, InputChar a)
{-
ghci> contextFreeMatch (Seq [Char 1, Optional (Char 2), Char 3, Char 4]) [1,2,3,4]

<interactive>:106:1: warning: [-Wtype-defaults]
    • Defaulting the following constraints to type ‘Integer’
        (Show a0) arising from a use of ‘print’ at <interactive>:106:1-76
        (Eq a0) arising from a use of ‘it’ at <interactive>:106:1-76
        (Num a0) arising from a use of ‘it’ at <interactive>:106:1-76
    • In a stmt of an interactive GHCi command: print it
Right ([],SeqNode [InputChar 1,OptionalNodeValue (InputChar 2),InputChar 3,InputChar 4])
-}

--contextFreeMatch :: (Eq a, Show a) => (ContextFreeGrammar a) -> [a] -> (a -> b -> MatchResult a) -> MatchResult (ContextFreeGrammar a)

contextFreeMatch a xs matchFn = do
  (rest, result) <- contextFreeMatch' a xs matchFn
  case P.length rest == 0 of
       False -> NoMatch ("rest left: " ++ show rest)
       True -> MatchSuccess result

-- helpers

m2e :: e -> Maybe a -> Either e a
m2e e m = case m of
               Nothing -> Left e
               Just x -> Right x

safeHead :: [a] -> Maybe a
safeHead (x:_) = Just x
safeHead _ = Nothing

catMaybes xs = L.foldl' f mempty xs
  where f a b = case b of
                     Nothing -> a
                     Just x -> a ++ [x]

asKeyMap :: Value -> Maybe Object
asKeyMap (Object a) = Just a
asKeyMap _ = Nothing

asArray :: Value -> Maybe [Value]
asArray (Array a) = Just $ Data.Vector.Generic.toList a
asArray _ = Nothing

asString (String x) = Just x
asString _ = Nothing

--- Match functions begin

-- | A JSON \"object\" (key\/value map).
type MatchObject = KeyMap MatchPattern

-- | A JSON \"array\" (sequence).
type MatchArray = V.Vector MatchPattern -- TODO just use list?

{-data MatchOp = MatchOp (MatchPattern -> MatchResult MatchPattern)
instance Show MatchOp where
  show _ = "MatchOp"

instance Eq MatchOp where
  (==) _ _ = False

instance Generic MatchOp where
  --

instance ToJSON MatchOp where
  --

instance FromJSON MatchOp
    -- No need to provide a parseJSON implementation.-}

                  -- queries
data MatchPattern = MatchObject !MatchObject -- literal
                  | MatchArray !MatchPattern -- literal
                  | MatchString !T.Text
                  | MatchStrict String !MatchPattern
                  | MatchAny
                  | MatchIgnore
                  | MatchFunnel
                  | MatchFunnelKeys
                  | MatchFunnelKeysU
                  | MatchSimpleOr [MatchPattern]
                  | MatchObjectPartial !MatchObject -- specific
                  | MatchArraySome !MatchPattern -- specific
                  | MatchArrayOne MatchPattern
                  | MatchArrayExact [MatchPattern] -- specific
                  | MatchArrayContextFree (ContextFreeGrammar MatchPattern)
                  | MatchIfThen MatchPattern MatchPattern String
                  -- special queries
                  -- | MatchApply MatchOp MatchPattern
                  | MatchMustHave MatchPattern
                  -- both
                  | MatchNumber !Sci.Scientific
                  | MatchBool !Bool
                  | MatchNull
                  | MatchLiteral
                  -- results
                  | MatchFunnelResult !Value
                  | MatchFunnelResultM !Value
                  | MatchAnyResult !Value
                  | MatchIgnoreResult
                  | MatchAnyResultU
                  | MatchSimpleOrResult MatchPattern
                  | MatchObjectPartialResult Value !MatchObject -- specific
                  | MatchObjectPartialResultU !MatchObject -- specific
                  | MatchArraySomeResult [(Int, Value)] [(Int, MatchPattern)] -- specific
                  | MatchArrayResult [MatchPattern]
                  | MatchArrayOneResult MatchPattern
                  | MatchArraySomeResultU [(Int, MatchPattern)] -- specific
                  | MatchArrayContextFreeResult (ContextFreeGrammar MatchPattern)
                    deriving (Generic, Eq, Show)

instance ToJSON MatchPattern where
    -- No need to provide a toJSON implementation.

    -- For efficiency, we write a simple toEncoding implementation, as
    -- the default version uses toJSON.
    toEncoding = genericToEncoding defaultOptions

instance FromJSON MatchPattern
    -- No need to provide a parseJSON implementation.

--gatherFunnel :: [Value] -> MatchPattern -> [Value]
gatherFunnel acc (MatchObjectPartialResult _ o) = L.foldl' gatherFunnel acc (KM.elems o)
gatherFunnel acc (MatchArraySomeResult _ o) = L.foldl' gatherFunnel acc (fmap snd o)
gatherFunnel acc (MatchArrayResult o) = L.foldl' gatherFunnel acc o
gatherFunnel acc (MatchArrayOneResult o) = gatherFunnel acc o
gatherFunnel acc (MatchSimpleOrResult o) = gatherFunnel acc o
gatherFunnel acc (MatchFunnelResult r) = r:acc
gatherFunnel acc (MatchFunnelResultM r) = case asArray r of
                                               Nothing -> error ("aaa: " ++ show acc)
                                               Just a -> L.nub $ a ++ acc
gatherFunnel acc MatchLiteral = acc
gatherFunnel acc (MatchAnyResult _) = acc
gatherFunnel acc MatchIgnoreResult = acc
gatherFunnel acc (MatchString _) = acc
gatherFunnel acc (MatchNumber _) = acc
gatherFunnel acc MatchNull = acc
gatherFunnel acc x = error (show x)
--gatherFunnel acc _ = acc

-- pattern -> value -> result
matchPattern :: MatchPattern -> Value -> MatchResult MatchPattern
--matchPattern (MatchMustHave m) v = case matchPattern m v of
--                                             Just x -> Just x
--                                             Nothing -> error "must have"
--
m2mp :: MatchResult a -> Maybe a -> MatchResult a
m2mp m v = case v of
              Just x -> MatchSuccess x
              Nothing -> m

matchPattern (MatchStrict s m) v = case matchPattern m v of
                                      NoMatch x -> MatchFailure s
                                      x -> x
matchPattern (MatchObject m) (Object a) = if keys m /= keys a then (MatchFailure "MatchObject keys mismatch") else fmap (MatchObject . KM.fromList) $ L.foldl' f (MatchSuccess []) (keys m)
  where f acc k = do
          acc' <- acc
          m' <- (m2mp $ NoMatch "object key mismatch") $ KM.lookup k m
          a' <- (m2mp $ NoMatch "object key mismatch") $ KM.lookup k a
          p <- matchPattern m' a'
          return $ acc' ++ [(k, p)]

matchPattern (MatchObjectPartial m) (Object a) = fmap (MatchObjectPartialResult leftOver) $ L.foldl' f (MatchSuccess mempty) (keys m)
  where leftOver = Object $ KM.difference a m
        f acc k = do
          acc' <- acc
          m' <- (m2mp $ NoMatch "object key mismatch") $ KM.lookup k m
          a' <- (m2mp $ NoMatch "object key mismatch") $ KM.lookup k a
          p <- matchPattern m' a'
          return $ KM.insert k p acc'

matchPattern (MatchArray m) (Array a) = do
  let vv = (V.toList a)
      f acc e = do
          acc' <- acc
          case matchPattern m e of
             MatchSuccess r -> MatchSuccess (acc' ++ [r])
             MatchFailure r -> MatchFailure r
             NoMatch _ -> MatchSuccess acc'
  acc <- L.foldl' f (MatchSuccess mempty) vv
  acc <- if P.length acc /= P.length vv then NoMatch "array length mismatch" else MatchSuccess acc
  return $ MatchArrayResult acc

matchPattern (MatchArrayOne m) (Array a) = do
  let vv = (V.toList a)
      f acc e = do
          acc' <- acc
          case matchPattern m e of
             MatchSuccess r -> MatchSuccess (acc' ++ [r])
             MatchFailure r -> MatchFailure r
             NoMatch _ -> MatchSuccess acc'
  acc <- L.foldl' f (MatchSuccess mempty) vv
  acc <- if P.length acc /= 1 then NoMatch "array length isn't 1" else MatchSuccess acc
  return $ MatchArrayOneResult (P.head acc)

matchPattern (MatchArrayExact m) (Array a) = if P.length m /= V.length a then MatchFailure "array exact match" else do
  let vv = (V.toList a)
      f acc (p, e) = do
          acc' <- acc
          case matchPattern p e of
             MatchSuccess r -> MatchSuccess (acc' ++ [r])
             MatchFailure r -> MatchFailure r
             NoMatch r -> NoMatch r
  acc <- L.foldl' f (MatchSuccess mempty) (P.zip m vv)
  return $ MatchArrayResult acc

{-
contextFreeMatch
  :: (Eq a1, Show a1, Show a2) =>
     ContextFreeGrammar a1
     -> [a2]
     -> (a1 -> a2 -> MatchResult a1)
     -> MatchResult (ContextFreeGrammar a1)
-}

matchPattern (MatchArrayContextFree m) (Array a) =
  case contextFreeMatch m (V.toList a) matchPattern of
       NoMatch e -> NoMatch ("context-free nomatch: " ++ e)
       MatchFailure s -> MatchFailure s
       MatchSuccess x ->  MatchSuccess (MatchArrayContextFreeResult x)

matchPattern MatchFunnel v = MatchSuccess $ MatchFunnelResult v

matchPattern MatchFunnelKeys (Object v) = MatchSuccess $ MatchFunnelResult $ Array $ V.fromList $ (fmap (String . K.toText)) $ KM.keys v
matchPattern MatchFunnelKeys _ = MatchFailure "MatchFunnelKeys met not a KeyMap"

matchPattern MatchFunnelKeysU (Object v) = MatchSuccess $ MatchFunnelResultM $ Array $ V.fromList $ (fmap (String . K.toText)) $ KM.keys v
matchPattern MatchFunnelKeysU _ = MatchFailure "MatchFunnelKeys met not a KeyMap"

matchPattern (MatchIfThen baseMatch match failMsg) v =
  case matchPattern baseMatch v of
       NoMatch x -> NoMatch x
       MatchFailure f -> MatchFailure f
       MatchSuccess s -> case matchPattern match v of
                            NoMatch x -> MatchFailure (failMsg ++ show x)
                            MatchFailure f -> MatchFailure f
                            MatchSuccess s -> MatchSuccess s

matchPattern (MatchArraySome m) (Array a) = do
  let f acc (idx, e) = do
          (a1, a2) <- acc
          case matchPattern m e of
             MatchSuccess r -> (MatchSuccess (a1, a2 ++ [(idx, r)]))
             MatchFailure r -> MatchFailure r
             NoMatch _ -> MatchSuccess (a1 ++ [(idx, e)], a2)
  (a1, a2) <- L.foldl' f (MatchSuccess (mempty, mempty)) $ P.zip [0..] (V.toList a)
  (a1, a2) <- if P.length a2 > 0 then MatchSuccess (a1, a2) else NoMatch "array mustn't be empty"
  return $ MatchArraySomeResult a1 a2

matchPattern MatchAny a = MatchSuccess $ MatchAnyResult a
matchPattern MatchIgnore a = MatchSuccess MatchIgnoreResult
matchPattern (MatchSimpleOr ms) v = fmap MatchSimpleOrResult $ P.foldr f (MatchFailure "or fail") ms
  where f a b = case matchPattern a v of
                     MatchSuccess x -> MatchSuccess x
                     MatchFailure f -> MatchFailure f
                     _ -> b

-- valueless
--matchPattern (MatchApply (MatchOp f) m) v = matchPattern m v >>= f
matchPattern (MatchString m) (String a) = if m == a then MatchSuccess MatchLiteral else NoMatch ("string mismatch: expected " ++ show m ++ " but found " ++ show a)
matchPattern (MatchNumber m) (Number a) = if m == a then MatchSuccess MatchLiteral else NoMatch ("number mismatch: expected " ++ show m ++ " but found " ++ show a)
matchPattern (MatchBool m) (Bool a) = if m == a then MatchSuccess MatchLiteral else NoMatch ("bool mismatch: expected " ++ show m ++ " but found " ++ show a)
matchPattern MatchNull Null = MatchSuccess MatchLiteral
-- valued
matchPattern MatchLiteral (String a) = MatchSuccess $ MatchString a
matchPattern MatchLiteral (Number a) = MatchSuccess $ MatchNumber a
matchPattern MatchLiteral (Bool a) = MatchSuccess $ MatchBool a
matchPattern MatchLiteral Null = MatchSuccess $ MatchNull
-- default case
matchPattern _ _ = NoMatch "bottom reached"

-- matchPattern (MatchString $ T.pack "abcd") (String $ T.pack "abcd")
-- matchPattern (MatchNumber 11.0) (Number 11.0)
-- matchPattern (MatchBool True) (Bool True)
-- matchPattern MatchNull Null

--matchOp = MatchApply . MatchOp

matchToValueMinimal :: MatchPattern -> Maybe Value
matchToValueMinimal (MatchObjectPartialResult _ m) = fmap Object $ L.foldl' f (Just mempty) (keys m) -- ifNotEmpty =<< 
  where
    ifNotEmpty m = if KM.null m then Nothing else Just m
    f acc k = do
          acc' <- acc
          v <- KM.lookup k m
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> KM.insert k x acc'
matchToValueMinimal (MatchObjectPartialResultU m) = fmap Object $ L.foldl' f (Just mempty) (keys m) -- ifNotEmpty =<< 
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
matchToValueMinimal (MatchSimpleOrResult m) = matchToValueMinimal m
matchToValueMinimal (MatchString m) = Just (String m)
matchToValueMinimal (MatchNumber m) = Just (Number m)
matchToValueMinimal (MatchBool m) = Just (Bool m)
matchToValueMinimal MatchNull = Just Null
matchToValueMinimal (MatchAnyResult a) = Just a
matchToValueMinimal MatchIgnoreResult = Nothing -- TODO
--matchToValueMinimal (MatchArrayResult a) = (Array $ V.fromList) $ catMaybes $ fmap matchToValueMinimal a
matchToValueMinimal (MatchArrayResult m) = fmap Array $ ifNotEmpty =<< L.foldl' f (Just (V.empty :: V.Vector Value)) arr
  where
    arr = V.fromList $ m
    ifNotEmpty m = if V.null m then Nothing else Just m
    f acc v = do
          acc' <- acc
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> V.snoc acc' x
matchToValueMinimal MatchLiteral = Just Null -- TODO
matchToValueMinimal (MatchFunnelResult v) = Just v
matchToValueMinimal (MatchFunnelResultM v) = Just v
matchToValueMinimal (MatchArrayOneResult a) = matchToValueMinimal a {-do
  v <- matchToValueMinimal a
  return $ Array $ V.fromList [v]-}
matchToValueMinimal x = error $ show x

matchToValueMinimal' x = (m2mp $ MatchFailure $ "matchToValueMinimal error " ++ show x) $ (matchToValueMinimal x)

resetUnsignificant (MatchObjectPartialResult _ a) = MatchObjectPartialResultU (fmap resetUnsignificant a)
resetUnsignificant (MatchArraySomeResult _ a) = MatchArraySomeResultU ((fmap . fmap) resetUnsignificant a)
--resetUnsignificant (MatchAnyResult _) = MatchAnyResultU
resetUnsignificant (MatchSimpleOrResult m) = resetUnsignificant m
resetUnsignificant a = a

-- Match functions end


someFunc :: IO ()
someFunc = P.putStrLn "someFunc"

getData1 :: IO (Maybe Value)
getData1 = do
  fileData <- BL.readFile "/home/andrey/Work/lc/pyparts1.json"
  return $ decode fileData

getData :: IO (Maybe Value)
getData = do
  fileData <- BL.readFile "/home/andrey/Work/lc/pyparts.json"
  return $ decode fileData

--getD :: IO (Maybe Value)
getD a = do
  fileData <- BL.readFile a
  return $ decode fileData

main_grammar = MatchObjectPartial (fromList [
    (fromString "type", MatchString $ T.pack "ClassDef"),
    (fromString "body", (MatchObjectPartial
                      (fromList [
                        --(fromString "type", MatchString $ T.pack "IndentedBlock"),
                        (fromString "type", MatchString $ T.pack "IndentedBlock"),
                        (fromString "body",
                         MatchArraySome (MatchObjectPartial (fromList [
                          (fromString "type", MatchString $ T.pack "SimpleStatementLine"),
                          (fromString "body",
                            (MatchIfThen
                              (MatchArraySome (MatchObjectPartial (fromList [
                                  (fromString "type", MatchString $ T.pack "AnnAssign")
                              
                                  --(fromString "target", (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name"),
                                  --                                                    (fromString "value", MatchLiteral)])))
                              
                              ])))
                              (MatchArraySome (MatchObjectPartial (fromList [
                                  (fromString "type", MatchString $ T.pack "AnnAssign") ,
                                  (fromString "target", (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name"),
                                                                                      (fromString "value", MatchLiteral)]))),
                                  (fromString "annotation",
                                   (MatchIfThen
                                    (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Annotation")]))
                                    (MatchObjectPartial (fromList [(fromString "annotation",
                                                                  (MatchSimpleOr
                                                                  [
                                                                    (MatchIfThen
                                                                      (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Subscript")]))
                                                                      {-(MatchObjectPartial (fromList [
                                                                                                      (fromString "type", MatchString $ T.pack "Subscript")
                                                                                                      , (fromString "value",
                                                                                                        (MatchObjectPartial (fromList [
                                                                                                          (fromString "type", MatchString $ T.pack "Name")
                                                                                                        , (fromString "value", MatchLiteral)
                                                                                                        ]))
                                                                                                      )
                                                                                                      --,(fromString "slice", MatchAny)
                                                                                                      ]))-}
                                                                      -- ["lbracket","lpar","rbracket","rpar","slice","type","value","whitespace_after_value"]
                                                                      -- lbracket, rbracket - only has whitespace
                                                                      (MatchObjectPartial (fromList [
                                                                        (fromString "value", (MatchObjectPartial (fromList [(fromString "value", MatchLiteral)]))),
                                                                        (fromString "slice",
                                                                          -- ["comma","slice","type" = SubscriptElement]
                                                                          -- comma:
                                                                          --    {"type":"Comma","whitespace_after":{"type":"SimpleWhitespace","value":" "},"whitespace_before":{"type":"SimpleWhitespace","value":""}}
                                                                          --    "MaybeSentinel.DEFAULT"
                                                                         MatchArray $ MatchObjectPartial (fromList [(fromString "slice",
                                                                          -- ["star"=null,"type"="Index","value","whitespace_after_star"=null]
                                                                          MatchObjectPartial (fromList [
                                                                            -- ...
                                                                            --(fromString "type", MatchString $ T.pack "Index"),
                                                                            -- ["lbracket","lpar","rbracket","rpar","slice","type","value","whitespace_after_value"]
                                                                            -- ["lpar","rpar","type","value"]

                                                                            (fromString "value",
                                                                             (MatchSimpleOr
                                                                             [
                                                                              (MatchIfThen
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "SimpleString")]))
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchLiteral), (fromString "value", MatchLiteral)]))
                                                                                "foo..."
                                                                              ),
                                                                              (MatchIfThen
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name")]))
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchLiteral), (fromString "value", MatchLiteral)]))
                                                                                "foo..."
                                                                              ),
                                                                              (MatchIfThen
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Subscript")]))



                                                                          (MatchObjectPartial (fromList [
                                                                            -- ...
                                                                            --(fromString "type", MatchString $ T.pack "Index"),
                                                                            -- ["lbracket","lpar","rbracket","rpar","slice","type","value","whitespace_after_value"]
                                                                            -- ["lpar","rpar","type","value"]

                                                                            (fromString "type", MatchLiteral),
                                                                            (fromString "value",
                                                                             (MatchSimpleOr
                                                                             [
                                                                               -- only Name here on 2nd level
                                                                              (MatchIfThen
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name")]))
                                                                                (MatchObjectPartial (fromList [(fromString "value", MatchLiteral)]))
                                                                                "foo..."
                                                                              )
                                                                              --(MatchObjectPartial (fromList [(fromString "type", MatchFunnel)]))
                                                                             ])
                                                                            
                                                                            )
                                                                          ]))




                                                                                "foo..."
                                                                              )


                                                                             ])
                                                                            
                                                                            )
                                                                          ])
                                                                         )]))
                                                                      ]))
                                                                      --(MatchObjectPartial (fromList [(fromString "value", MatchFunnel)]))

                                                                    "foo1"),
                                                                    (MatchIfThen
                                                                      (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name")]))
                                                                      (MatchObjectPartial (fromList [
                                                                                                    (fromString "type", MatchString $ T.pack "Name"),
                                                                                                    (fromString "value", MatchLiteral)
                                                                                                    ]))
                                                                    "foo2")
                                                                  ])
                                                                  )]))) "iii")
                                ])))
                            "annotation match fail"))

                            --(fromString "annotation", )
                        ]))
                        
                        
                        )
                      ])))
            ])

-- helpers begin

h3 :: [Value] -> [String]
h3 v = catMaybes $ fmap f v
  where f x = do
                x <- asKeyMap x
                x <- KM.lookup (fromString "body") x
                x <- asArray x
                x <- safeHead x
                x <- asKeyMap x
                k <- KM.lookup (fromString "target") x
                k <- asKeyMap k
                k <- KM.lookup (fromString "value") k
                k <- asString k
                -- ...
                v <- KM.lookup (fromString "annotation") x
                return $ T.unpack k ++ "\t\t\t" ++ (TL.unpack . TL.decodeUtf8 $ encode v)


h1 :: Value -> Maybe [Value]
h1 x = do
                x <- asKeyMap x
                x <- KM.lookup (fromString "body") x
                x <- asKeyMap x
                x <- KM.lookup (fromString "body") x
                x <- asArray x
                --k <- KM.lookup (fromString "target") x
                --k <- asKeyMap k
                --k <- KM.lookup (fromString "value") k
                --k <- asString k
                -- ...
                --v <- KM.lookup (fromString "annotation") x
                --return $ (fromText k, v)
                return x

asJust (Just x) = x

h2 (MatchSuccess s) = P.concat $ (fmap (\x -> x ++ "\n")) $ h3 $ asJust (h1 s)
h2 x = show x

catSuccesses xs = L.foldl' f mempty xs
  where f a b = case b of
                     MatchSuccess x -> a ++ [x]
                     _ -> a

-- helpers end


p1 :: IO (Maybe Value) -> IO ()
p1 theData = do
  -- d :: Maybe Value
  d <- theData
  let v = do
        -- d' :: Value
        d' <- d
        -- d'' :: Keymap Value
        d'' <- asKeyMap d'
        let f v = do
              r' <- matchPattern main_grammar v
              -- r' :: MatchResult MatchPattern
              r <- return $ resetUnsignificant r'
              -- r' :: MatchResult MatchPattern
              r <- matchToValueMinimal' r
              return (gatherFunnel [] r', r)
        --let j (k, (_, v)) = (K.toString k) ++ "\n" ++ "\n" ++ "\n" ++ v ++ "\n\n"
        let j (k, v) = (K.toString k) ++ "\n" ++ h2 v ++ "\n" ++ "\n"
        let s1 = (fmap . fmap) f (KM.toList d'')
        let s2 = (fmap . fmap . fmap) snd s1
        let s3 = P.concat $ L.intersperse "\n" $ fmap (TL.unpack . TL.decodeUtf8 . encode) $ (Data.Set.toList) $ (Data.Set.fromList) $ P.concat $ fmap fst $ catSuccesses $ fmap snd s1
        return $ (P.concat $ fmap j s2) ++ "\n\n" ++ s3
  P.putStrLn $ case v of
       Nothing -> "Nothing to see"
       Just a -> a

hh a = P.concat $ fmap f a
  where f x = (TL.unpack . TL.decodeUtf8 . encode) x ++ "\n"


grammar'1 = MatchIfThen (MatchObjectPartial (fromList [
    (fromString "body", MatchFunnelKeys)
  ])) (MatchObjectPartial (fromList [(fromString "orelse", MatchNull)])) "orelse fail"


-- x ["body","orelse"!,"test"]
-- x.test ["args","func","type"]

--  collapse utils begin
selectKey k (Object a) = KM.lookup k a
selectKey _ _ = Nothing

collapse' = selectKey (fromString "body")

doCollapse f v = case f v of
                     Nothing -> MatchFailure "collapse problem"
                     Just x -> MatchSuccess x

sList f (Array a) = case P.traverse f a of
                     MatchFailure x -> MatchFailure x
                     MatchSuccess x -> MatchSuccess $ Array x
sList _ s = error (show s)

sBody = doCollapse (selectKey (fromString "body"))
-- collapse utils end

simple_or_grammar = MatchObjectPartial (fromList [
    (fromString "type", MatchString $ T.pack "If"), -- top
    (fromString "orelse", MatchNull), -- bottom
    (fromString "test",
      MatchObjectPartial (fromList [ -- top
        (fromString "type", MatchString $ T.pack "Call"),
        (fromString "func", MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "Name"),
          (fromString "value", MatchString $ T.pack "__simpleor")
        ])),
        (fromString "args", MatchArrayOne $ MatchIgnore) -- TODO
      ])
    ),
    (fromString "body",
      MatchObjectPartial (fromList [ -- top
        (fromString "type", MatchString $ T.pack "IndentedBlock"),
        (fromString "body", MatchArray $ MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__option")
              ])),
              (fromString "args", MatchArrayOne $ MatchIgnore) -- TODO
            ])
          ),
          (fromString "body",
            MatchObjectPartial (fromList [
              (fromString "type", MatchString $ T.pack "IndentedBlock"),
              (fromString "body", MatchArrayOne $ MatchAny)
            ]))
        ]))
      ])
    )
  ])

simple_or_collapse = (sBody >=> sBody >=> (sList (sBody >=> sBody)))


or_grammar = MatchObjectPartial (fromList [
    (fromString "type", MatchString $ T.pack "If"), -- top
    (fromString "orelse", MatchNull), -- bottom
    (fromString "test",
      MatchObjectPartial (fromList [ -- top
        (fromString "type", MatchString $ T.pack "Call"),
        (fromString "func", MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "Name"),
          (fromString "value", MatchString $ T.pack "__or")
        ])),
        (fromString "args", MatchArrayOne $ MatchIgnore) -- TODO
      ])
    ),
    (fromString "body",
      MatchObjectPartial (fromList [ -- top
        (fromString "type", MatchString $ T.pack "IndentedBlock"),
        (fromString "body", MatchArray $ MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__option")
              ])),
              -- ["comma","equal","keyword","star","type","value","whitespace_after_arg","whitespace_after_star"]
              (fromString "args", MatchArrayOne $
                MatchObjectPartial (fromList [ -- top
                  (fromString "type", MatchString $ T.pack "Arg"),
                  (fromString "value", MatchObjectPartial (fromList [
                    (fromString "value", MatchLiteral)
                  ]))
                ])
              )
            ])
          ),
          (fromString "body",
            MatchObjectPartial (fromList [
              (fromString "type", MatchString $ T.pack "IndentedBlock"),
              (fromString "body", MatchArray $ MatchAny)
            ]))
        ]))
      ])
    )
  ])

{-
MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__option")
              ])),
              (fromString "args", MatchArrayOne $ MatchLiteral)
            ])
          ),
          (fromString "body",
            MatchObjectPartial (fromList [
              (fromString "type", MatchString $ T.pack "IndentedBlock"),
              (fromString "body", MatchArray $ MatchAny)
            ]))
        ])
-}

or_collapse = (sBody >=> sBody >=> (sList (sBody >=> sBody)))


star_grammar = MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__star")
              ])),
              (fromString "args", MatchArrayOne $ MatchIgnore) -- TODO
            ])
          ),
          (fromString "body",
            MatchObjectPartial (fromList [
              (fromString "type", MatchString $ T.pack "IndentedBlock"),
              (fromString "body", MatchArrayOne $ MatchAny)
            ]))
        ])

star_collapse = (sBody >=> sBody) -- :: MatchResult Value

ib_grammar = MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "IndentedBlock"),
          (fromString "body",
            MatchArray $ MatchAny
          )
        ])

any_grammar = MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__any")
              ])),
              (fromString "args", MatchArrayOne $ MatchIgnore) -- TODO
            ])
          )
        ])

any_collapse x = return x

matchAndCollapse :: MatchPattern -> (Value -> MatchResult Value) -> Value -> MatchResult ([Value], Value)
matchAndCollapse grammar collapse value = do
  r' <- matchPattern grammar value
  -- r' :: MatchResult MatchPattern
  r <- return $ resetUnsignificant r'
  -- r' :: MatchResult MatchPattern
  r <- matchToValueMinimal' r
  r'' <- collapse r
  return (gatherFunnel [] r', r'')

--p3 :: IO (Maybe Value) -> IO ()
p3 a grammar collapse = do
  -- d :: Maybe Value
  d <- getD a
  let v = do
        -- d' :: Value
        d' <- d
        let f v = do
              r' <- matchPattern grammar v
              -- r' :: MatchResult MatchPattern
              r <- return $ resetUnsignificant r'
              -- r' :: MatchResult MatchPattern
              r <- matchToValueMinimal' r
              r <- collapse r
              return $ "Result\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode) r ++ "\n\n\n" ++ "Funnel\n\n" ++ hh (gatherFunnel [] r')
              --return $ (r, gatherFunnel [] r')
        return $ f d'
  P.putStrLn $ case v of
       Nothing -> "Nothing to see"
       Just a -> case a of
                      NoMatch x -> "NoMatch " ++ x
                      MatchFailure s -> "MatchFailure " ++ s
                      MatchSuccess s -> "Success!!!\n\n\n" ++ s


-- cata stuff
data ListF a b = Nil | Cons a b deriving (Eq, Show, Functor)
type List a = Fix (ListF a)

l1 = Cons 1 $ Cons 2 $ Cons 3 Nil

pythonUnsignificantKeys :: [String]
pythonUnsignificantKeys = [
  "lpar",
  "rpar",
  "first_line",
  "empty_lines",
  "indent",
  "newline",
  "lpar",
  "rpar",
  "colon",
  "header",
  "footer",
  "leading_lines",
  "lines_after_decorators",
  "trailing_whitespace",
  "whitespace_before_equal",
  "whitespace_after_equal",
  "whitespace_before_test",
  "whitespace_after_test"]

simple_or_success (Array v) = fmap MatchSimpleOr $ P.traverse pythonMatchPattern (V.toList v)
simple_or_success _ = Left "wrong grammar"

pythonMatchContextFreePattern :: Value -> Either String MatchPattern
pythonMatchContextFreePattern (Array a) =  Left "foo" -- P.traverse f (V.toList a) where f x = Left "foo"
pythonMatchContextFreePattern _ = Left "pattern error"

pythonMapMatches = [
    (simple_or_grammar, simple_or_collapse, simple_or_success)
  , (any_grammar, any_collapse, const $ Right MatchAny)
  --, (ib_grammar, sBody, (pythonMatchContextFreePattern . snd))
  ] :: [(MatchPattern, Value -> MatchResult Value, Value -> Either String MatchPattern)]

pythonMatchPattern :: Value -> Either String MatchPattern
pythonMatchPattern (Array a) = fmap MatchArrayExact (L.foldl' f (Right mempty) (V.toList a))
  where f acc e = do
          acc' <- acc
          e' <- pythonMatchPattern e
          return $ acc' ++ [e']

pythonMatchPattern (Object a) = L.foldr f defaultMapMatch pythonMapMatches
  where x = Object a
        defaultMapMatch = fmap MatchObjectPartial $ P.traverse pythonMatchPattern a'
                            where a' = KM.filterWithKey (\k _ -> not ((toString k) `P.elem` pythonUnsignificantKeys)) a
        f (grammar, collapseFn, successFn) b = case matchAndCollapse grammar collapseFn x of
                                                    MatchFailure s -> Left s
                                                    MatchSuccess (_, s) -> successFn s
                                                    MatchSuccess _ -> Left "wrong grammar"
                                                    NoMatch _ -> b

pythonMatchPattern (String s) = Right $ MatchString s
pythonMatchPattern (Number s) = Right $ MatchNumber s
pythonMatchPattern (Bool s) = Right $ MatchBool s
pythonMatchPattern Null = Right $ MatchNull



so_grammar = MatchObjectPartial (fromList [("items", MatchArray $ MatchObjectPartial (fromList [("tags", MatchFunnel)]))])
so_collapse x = return x
