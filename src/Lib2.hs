{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFoldable #-}


module Lib2
    ( someFunc
    ) where

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
import Control.Monad (join)
import qualified Data.ByteString.UTF8       as BLU

-- helpers

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

data MatchOp = MatchOp (MatchPattern -> MatchResult MatchPattern)
instance Show MatchOp where
  show _ = "MatchOp"

instance Eq MatchOp where
  (==) _ _ = False

data MatchPattern = MatchObject !MatchObject -- literal
                  | MatchArray !MatchPattern -- literal
                  | MatchString !T.Text
                  | MatchStrict String !MatchPattern
                  | MatchNumber !Sci.Scientific
                  | MatchBool !Bool
                  | MatchNull
                  | MatchLiteral
                  | MatchAny
                  | MatchFunnel
                  | MatchFunnelKeys
                  | MatchFunnelKeysU
                  | MatchFunnelResult !Value
                  | MatchFunnelResultM !Value
                  | MatchAnyResult !Value
                  | MatchApply MatchOp MatchPattern
                  | MatchAnyResultU
                  | MatchMustHave MatchPattern
                  | MatchSimpleOr [MatchPattern]
                  | MatchSimpleOrResult MatchPattern
                  | MatchObjectPartial !MatchObject -- specific
                  | MatchObjectPartialResult Value !MatchObject -- specific
                  | MatchObjectPartialResultU !MatchObject -- specific
                  -- | MatchArrayAll !MatchPattern -- specific
                  | MatchArraySome !MatchPattern -- specific
                  | MatchArraySomeResult [(Int, Value)] [(Int, MatchPattern)] -- specific
                  | MatchArrayResult [MatchPattern]
                  | MatchArrayOne MatchPattern
                  | MatchIfThen MatchPattern MatchPattern String
                  | MatchArrayOneResult MatchPattern
                  | MatchArraySomeResultU [(Int, MatchPattern)] -- specific
                    deriving (Eq, Show)

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
gatherFunnel acc (MatchString _) = acc
gatherFunnel acc (MatchNumber _) = acc
gatherFunnel acc MatchNull = acc
gatherFunnel acc x = error (show x)
--gatherFunnel acc _ = acc

data MatchResult a = MatchSuccess a
                 | MatchFailure String
                 | NoMatch
                 deriving (Eq, Show)

instance Functor MatchResult where
  fmap f (MatchSuccess m) = MatchSuccess (f m)
  fmap _ (MatchFailure x) = MatchFailure x
  fmap _ NoMatch = NoMatch

instance Applicative MatchResult where
  (<*>) (MatchSuccess f) (MatchSuccess m) = MatchSuccess (f m)
  (<*>) _ (MatchFailure x) = (MatchFailure x)
  pure x = MatchSuccess x

instance Monad MatchResult where
  --join (MatchSuccess (MatchSuccess x)) = MatchSuccess x
  --join (MatchFailure (MatchFailure x)) = MatchFailure x
  --join NoMatch = NoMatch
  (>>=) (MatchSuccess m) f = f m
  (>>=) (MatchFailure m) _ = (MatchFailure m)
  (>>=) NoMatch _ = NoMatch

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
                                      NoMatch -> MatchFailure s
                                      x -> x
matchPattern (MatchObject m) (Object a) = if keys m /= keys a then (MatchFailure "MatchObject keys mismatch") else fmap (MatchObject . KM.fromList) $ L.foldl' f (MatchSuccess []) (keys m)
  where f acc k = do
          acc' <- acc
          m' <- (m2mp NoMatch) $ KM.lookup k m
          a' <- (m2mp NoMatch) $ KM.lookup k a
          p <- matchPattern m' a'
          return $ acc' ++ [(k, p)]

matchPattern (MatchObjectPartial m) (Object a) = fmap (MatchObjectPartialResult leftOver) $ L.foldl' f (MatchSuccess mempty) (keys m)
  where leftOver = Object $ KM.difference a m
        f acc k = do
          acc' <- acc
          m' <- (m2mp NoMatch) $ KM.lookup k m
          a' <- (m2mp NoMatch) $ KM.lookup k a
          p <- matchPattern m' a'
          return $ KM.insert k p acc'

matchPattern (MatchArray m) (Array a) = do
  let vv = (V.toList a)
      f acc e = do
          acc' <- acc
          case matchPattern m e of
             MatchSuccess r -> MatchSuccess (acc' ++ [r])
             MatchFailure r -> MatchFailure ("array" ++ r)
             NoMatch -> MatchSuccess acc'
  acc <- L.foldl' f (MatchSuccess mempty) vv
  acc <- if P.length acc /= P.length vv then NoMatch else MatchSuccess acc
  return $ MatchArrayResult acc

matchPattern (MatchArrayOne m) (Array a) = do
  let vv = (V.toList a)
      f acc e = do
          acc' <- acc
          case matchPattern m e of
             MatchSuccess r -> MatchSuccess (acc' ++ [r])
             MatchFailure r -> MatchFailure ("arrayone" ++ r)
             NoMatch -> MatchSuccess acc'
  acc <- L.foldl' f (MatchSuccess mempty) vv
  acc <- if P.length acc /= 1 then NoMatch else MatchSuccess acc
  return $ MatchArrayOneResult (P.head acc)


matchPattern MatchFunnel v = MatchSuccess $ MatchFunnelResult v

matchPattern MatchFunnelKeys (Object v) = MatchSuccess $ MatchFunnelResult $ Array $ V.fromList $ (fmap (String . K.toText)) $ KM.keys v
matchPattern MatchFunnelKeys _ = MatchFailure "MatchFunnelKeys met not a KeyMap"

matchPattern MatchFunnelKeysU (Object v) = MatchSuccess $ MatchFunnelResultM $ Array $ V.fromList $ (fmap (String . K.toText)) $ KM.keys v
matchPattern MatchFunnelKeysU _ = MatchFailure "MatchFunnelKeys met not a KeyMap"

matchPattern (MatchIfThen baseMatch match failMsg) v =
  case matchPattern baseMatch v of
       NoMatch -> NoMatch
       MatchFailure f -> MatchFailure f
       MatchSuccess s -> case matchPattern match v of
                            NoMatch -> MatchFailure  ("fail" ++ failMsg) --(failMsg ++ " " ++ show s)
                            MatchFailure f -> MatchFailure ("fail2" ++ f)
                            MatchSuccess s -> MatchSuccess s

matchPattern (MatchArraySome m) (Array a) = do
  let f acc (idx, e) = do
          (a1, a2) <- acc
          case matchPattern m e of
             MatchSuccess r -> (MatchSuccess (a1, a2 ++ [(idx, r)]))
             MatchFailure r -> MatchFailure ("some" ++ r)
             NoMatch -> MatchSuccess (a1 ++ [(idx, e)], a2)
  (a1, a2) <- L.foldl' f (MatchSuccess (mempty, mempty)) $ P.zip [0..] (V.toList a)
  (a1, a2) <- if P.length a2 > 0 then MatchSuccess (a1, a2) else NoMatch -- at lease 1
  return $ MatchArraySomeResult a1 a2

matchPattern MatchAny a = MatchSuccess $ MatchAnyResult a
matchPattern (MatchSimpleOr ms) v = fmap MatchSimpleOrResult $ P.foldr f (MatchFailure "or fail") ms
  where f a b = case matchPattern a v of
                     MatchSuccess x -> MatchSuccess x
                     MatchFailure f -> MatchFailure f
                     _ -> b

-- valueless
matchPattern (MatchApply (MatchOp f) m) v = matchPattern m v >>= f
matchPattern (MatchString m) (String a) = if m == a then MatchSuccess MatchLiteral else NoMatch
matchPattern (MatchNumber m) (Number a) = if m == a then MatchSuccess MatchLiteral else NoMatch
matchPattern (MatchBool m) (Bool a) = if m == a then MatchSuccess MatchLiteral else NoMatch
matchPattern MatchNull Null = MatchSuccess MatchLiteral
-- valued
matchPattern MatchLiteral (String a) = MatchSuccess $ MatchString a
matchPattern MatchLiteral (Number a) = MatchSuccess $ MatchNumber a
matchPattern MatchLiteral (Bool a) = MatchSuccess $ MatchBool a
matchPattern MatchLiteral Null = MatchSuccess $ MatchNull
-- default case
matchPattern _ _ = NoMatch

-- matchPattern (MatchString $ T.pack "abcd") (String $ T.pack "abcd")
-- matchPattern (MatchNumber 11.0) (Number 11.0)
-- matchPattern (MatchBool True) (Bool True)
-- matchPattern MatchNull Null

matchOp = MatchApply . MatchOp

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
matchToValueMinimal MatchLiteral = Nothing
matchToValueMinimal (MatchFunnelResult v) = Just v
matchToValueMinimal (MatchFunnelResultM v) = Just v
matchToValueMinimal x = error $ show x

matchToValueMinimal' x = (m2mp $ MatchFailure $ "here" ++ show x) $ (matchToValueMinimal x)

resetUnsignificant (MatchObjectPartialResult _ a) = MatchObjectPartialResultU (fmap resetUnsignificant a)
resetUnsignificant (MatchArraySomeResult _ a) = MatchArraySomeResultU ((fmap . fmap) resetUnsignificant a)
--resetUnsignificant (MatchAnyResult _) = MatchAnyResultU
resetUnsignificant (MatchSimpleOrResult m) = resetUnsignificant m
resetUnsignificant a = a

-- Match functions end


someFunc :: IO ()
someFunc = P.putStrLn "someFunc"

getData :: IO (Maybe Value)
getData = do
  fileData <- BL.readFile "/home/andrey/Work/rt/so.json"
  return $ decode fileData
{-- "answer_count"
"content_license"
"creation_date"
"is_answered"
"last_activity_date"
"last_edit_date"
"link"
"owner"
"question_id"
"score"
"tags"
"title"
"view_count"
"accepted_answer_id"
"closed_date"
"closed_reason" -}


-- ["entry","id","link","meta","total","type"]
-- {"items": ...}
grammar = (MatchObjectPartial (fromList [(fromString "items", MatchArray $ (MatchObjectPartial (fromList [(fromString "is_answered", MatchFunnel)])))]))

--(MatchObjectPartial (fromList [(fromString "items", MatchArray $ (MatchObjectPartial (fromList [(fromString "answer_count", MatchFunnel)])))]))

-- helpers begin
asJust (Just x) = x

catSuccesses xs = L.foldl' f mempty xs
  where f a b = case b of
                     MatchSuccess x -> a ++ [x]
                     _ -> a

-- helpers end

hh a = P.concat $ fmap f a
  where f x = (TL.unpack . TL.decodeUtf8 . encode) x ++ "\n"


p1 :: IO (Maybe Value) -> IO ()
p1 theData = do
  -- d :: Maybe Value
  d <- theData
  let v = do
        -- d' :: Value
        d' <- d
        let f v = do
              r' <- matchPattern grammar v
              -- r' :: MatchResult MatchPattern
              r <- return $ resetUnsignificant r'
              -- r' :: MatchResult MatchPattern
              r <- matchToValueMinimal' r
              return $ "Result\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode) r ++ "\n\n\n" ++ "Funnel\n\n" ++ hh (gatherFunnel [] r')
              --return $ (r, gatherFunnel [] r')
        return $ f d'
  P.putStrLn $ case v of
       Nothing -> "Nothing to see"
       Just a -> case a of
                      NoMatch -> "NoMatch"
                      MatchFailure s -> "MatchFailure " ++ s
                      MatchSuccess s -> "Success!!!\n\n\n" ++ s
