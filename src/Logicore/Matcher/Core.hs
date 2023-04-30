{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}


module Logicore.Matcher.Core where
{-  (
  --  matchPattern
  --, matchPattern
  --, contextFreeMatch
  --, ContextFreeGrammar(..)
  --, MatchPattern(..)
  --, MatchStatus(..)
  -- result processing fns
  --, gatherFunnel
  -- Matcher utils
   m2ms
  -- Aeson utils
  , asKeyMap
  , asArray
  , asString
  , catMaybes
  -- common utils
  , m2e
  , safeHead
  ) where-}

import qualified Data.Vector.Generic
--import qualified Data.Set
import qualified Data.List        as L
import GHC.Generics
import Data.Aeson
--import Data.ByteString            as B
--import Data.ByteString.Lazy       as BL
import Data.Text                  as T
--import Data.Text.Encoding         as T
--import Data.Text.IO               as T
import Data.Text.Lazy             as TL
import Data.Text.Lazy.Encoding    as TL
--import Data.Text.Lazy.IO          as TL
--import Data.Map                   as M
import Data.Aeson.KeyMap          as KM
import Data.Aeson.Key             as K
import qualified Data.Scientific as Sci
import qualified Data.Vector as V
import Prelude                    as P
import Control.Monad()
import Control.Comonad
--import qualified Data.ByteString.UTF8       as BLU
--import Logicore.Matcher.Utils
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Functor.Foldable
import Data.Bifunctor
import Data.Maybe (isJust, fromJust)
import Data.Monoid
import qualified Data.Set                     as S

import Test.QuickCheck
import Test.QuickCheck.Gen (oneof)
import Test.Hspec

import Language.Haskell.TH
import Language.Haskell.TH.Datatype as TH.Abs
import Language.Haskell.TH.Datatype.TyVarBndr
import Language.Haskell.TH.Syntax (mkNameG_tc, mkNameG_v)

import Logicore.Matcher.Helpers

--
-- MatchStatus is a monad for representing match outcome similar to Either
--

data MatchStatus a = MatchSuccess a
                 | MatchFailure String
                 | NoMatch String
                 deriving (Eq, Show)

instance Functor MatchStatus where
  fmap f (MatchSuccess m) = MatchSuccess (f m)
  fmap _ (MatchFailure x) = MatchFailure x
  fmap _ (NoMatch x) = NoMatch x

instance Applicative MatchStatus where
  (<*>) (MatchSuccess f) (MatchSuccess m) = MatchSuccess (f m)
  (<*>) _ (MatchFailure x) = (MatchFailure x)
  (<*>) (MatchFailure x) _ = (MatchFailure x)
  (<*>) (NoMatch x) _ = (NoMatch x)
  (<*>) _ (NoMatch x) = (NoMatch x)
  pure x = MatchSuccess x

instance Monad MatchStatus where
  (>>=) (MatchSuccess m) f = f m
  (>>=) (MatchFailure m) _ = (MatchFailure m)
  (>>=) (NoMatch m) _ = (NoMatch m)

instance Comonad MatchStatus where
  extract (MatchSuccess s) = s
  extract (MatchFailure e) = error $ "cannot extract1: " ++ e
  extract (NoMatch e) = error $ "cannot extract2: " ++ e
  duplicate (MatchSuccess s) = MatchSuccess (MatchSuccess s)
  duplicate (MatchFailure m) = MatchFailure m
  duplicate (NoMatch m) = NoMatch m

-- CF matcher
data ContextFreeGrammar a = Char a
                            | Seq [(ContextFreeGrammar a)]
                            | Or (KeyMap (ContextFreeGrammar a))
                            | Star (ContextFreeGrammar a)
                            | Plus (ContextFreeGrammar a)
                            | Optional (ContextFreeGrammar a)
                              deriving (Generic, Eq, Show, Functor, Foldable, Traversable)

instance Arbitrary a => Arbitrary (ContextFreeGrammar a) where
  arbitrary = oneof [
    Char <$> arbitrary,
    Seq <$> arbitrary,
    Or <$> arbitrary,
    Star <$> arbitrary,
    Plus <$> arbitrary,
    Optional <$> arbitrary]

makeBaseFunctor ''ContextFreeGrammar

instance ToJSON a => ToJSON (ContextFreeGrammar a) where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON a => FromJSON (ContextFreeGrammar a)

-- TODO: much better approach?
data ContextFreeGrammarResult g r = CharNode r
                                  | SeqNode [(ContextFreeGrammarResult g r)]
                                  | StarNodeEmpty (ContextFreeGrammar g)
                                  | StarNodeValue [(ContextFreeGrammarResult g r)]
                                  | PlusNode [(ContextFreeGrammarResult g r)]
                                  | OrNode (KeyMap (ContextFreeGrammar g)) Key (ContextFreeGrammarResult g r)
                                  | OptionalNodeValue (ContextFreeGrammarResult g r)
                                  | OptionalNodeEmpty (ContextFreeGrammar g)
                                    deriving (Generic, Eq, Show, Functor, Foldable, Traversable)

instance (Arbitrary g, Arbitrary r) => Arbitrary (ContextFreeGrammarResult g r) where
  arbitrary = oneof [
      CharNode <$> arbitrary,
      SeqNode <$> arbitrary,
      StarNodeEmpty <$> arbitrary,
      do
        h <- arbitrary
        t <- arbitrary
        return $ StarNodeValue (P.take (max t 1) $ P.repeat h),
      do
        h <- arbitrary
        t <- arbitrary
        return $ PlusNode (P.take (max t 1) $ P.repeat h),
      OrNode <$> arbitrary <*> arbitrary <*> arbitrary,
      OptionalNodeEmpty <$> arbitrary,
      OptionalNodeValue <$> arbitrary]

makeBaseFunctor ''ContextFreeGrammarResult

instance (ToJSON g, ToJSON r) => ToJSON (ContextFreeGrammarResult g r) where
    toEncoding = genericToEncoding defaultOptions

instance (FromJSON g, FromJSON r) => FromJSON (ContextFreeGrammarResult g r)

contextFreeMatch' :: (Show g, Show v, Show r) => ContextFreeGrammar g -> [v] -> (g -> v -> MatchStatus r) -> MatchStatus ([v], (ContextFreeGrammarResult g r))
contextFreeMatch' (Char _) [] _ = NoMatch "can't read char"
contextFreeMatch' (Char a) (x:xs) matchFn =
  case matchFn a x of
       NoMatch s -> NoMatch ("no char match: " ++ s)
       MatchFailure s -> MatchFailure s
       MatchSuccess a' -> MatchSuccess (xs, CharNode a')

contextFreeMatch' (Seq as) xs matchFn = (fmap . fmap) SeqNode $ L.foldl' f (MatchSuccess (xs, mempty)) as
  where f acc' a = do
          (xs, result) <- acc'
          (xs', result') <- contextFreeMatch' a xs matchFn
          return (xs', result ++ [result'])

contextFreeMatch' (Or as) xs matchFn = L.foldr f (NoMatch "or mismatch") (KM.toList as)
  where f (opt, a) b = do
          case contextFreeMatch' a xs matchFn of
               NoMatch _ -> b
               MatchFailure s -> MatchFailure s
               MatchSuccess (xs', r) -> MatchSuccess (xs', OrNode (KM.delete opt as) opt r)

contextFreeMatch' (Star a) xs matchFn = (fmap . fmap) c $ f (MatchSuccess (xs, mempty))
  where --f :: MatchStatus ([b], ContextFreeGrammar a) -> MatchStatus ([b], ContextFreeGrammar a)
        c [] = StarNodeEmpty a
        c xs = StarNodeValue xs
        f acc = do
          (xs, result) <- acc
          case contextFreeMatch' a xs matchFn of
               NoMatch _ -> acc
               MatchFailure s -> MatchFailure s
               MatchSuccess (xs', result') -> f (MatchSuccess (xs', result ++ [result']))

contextFreeMatch' (Plus a) xs matchFn = do
  (xs', subresult) <- contextFreeMatch' (Seq [a, Star a]) xs matchFn
  rs' <- case subresult of
              (SeqNode [r, (StarNodeValue rs)]) -> MatchSuccess (r:rs)
              _ -> NoMatch ("impossible203" ++ show subresult)
  return (xs', (PlusNode rs'))
  

contextFreeMatch' (Optional a) xs matchFn =
  case contextFreeMatch' a xs matchFn of
       NoMatch _ -> MatchSuccess (xs, OptionalNodeEmpty a)
       MatchFailure s -> MatchFailure s
       MatchSuccess (xs', subresult) -> MatchSuccess (xs', OptionalNodeValue subresult)

contextFreeMatch' a xs _ = error ("no contextFreeMatch for:\n\n" ++ (show a) ++ "\n\n" ++ (show xs))

contextFreeMatch :: (Show g, Show v, Show r) => ContextFreeGrammar g -> [v] -> (g -> v -> MatchStatus r) -> MatchStatus (ContextFreeGrammarResult g r)
contextFreeMatch a xs matchFn = do
  (rest, result) <- contextFreeMatch' a xs matchFn
  case P.length rest == 0 of
       False -> NoMatch ("rest left: " ++ show rest)
       True -> MatchSuccess result

-- helpers. Regular

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

-- helpers. Aeson

asKeyMap :: Value -> Maybe Object
asKeyMap (Object a) = Just a
asKeyMap _ = Nothing

asArray :: Value -> Maybe [Value]
asArray (Array a) = Just $ Data.Vector.Generic.toList a
asArray _ = Nothing

asString (String x) = Just x
asString _ = Nothing

asBool (Bool x) = Just x
asBool _ = Nothing

asNumber (Number x) = Just x
asNumber _ = Nothing

--- Helper types

--- Indicating if matching a key in an Object is obligatory
data ObjectKeyMatch a = KeyReq a | KeyOpt a | KeyExt Value deriving (Generic, Eq, Show, Functor, Foldable, Traversable)

instance ToJSON a => ToJSON (ObjectKeyMatch a) where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON a => FromJSON (ObjectKeyMatch a)
    -- No need to provide a parseJSON implementation.

instance Arbitrary a => Arbitrary (ObjectKeyMatch a) where
  arbitrary = oneof [
    KeyReq <$> arbitrary,
    KeyOpt <$> arbitrary]
    --KeyExt <$> arbitrary

--- Indicating if an element were matched or ignored (when only some must match)
data ArrayValMatch a = MatchedVal a | ExtraVal Value deriving (Generic, Eq, Show, Functor, Foldable, Traversable)

instance ToJSON a => ToJSON (ArrayValMatch a) where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON a => FromJSON (ArrayValMatch a)
    -- No need to provide a parseJSON implementation.


-- Match<What>[<How>], Match<What>[<How>]Result

                  -- structures - object
data MatchPattern = MatchObjectFull (KeyMap (ObjectKeyMatch MatchPattern))
                  | MatchObjectPartial (KeyMap (ObjectKeyMatch MatchPattern))
                  -- structures - array
                  -- | MatchArrayAll MatchPattern
                  -- | MatchArraySome MatchPattern
                  -- | MatchArrayOne MatchPattern
                  -- | MatchArrayExact [MatchPattern]
                  | MatchArrayContextFree (ContextFreeGrammar MatchPattern)
                  -- literals: match particular value of
                  | MatchStringExact !T.Text
                  | MatchNumberExact !Sci.Scientific
                  | MatchBoolExact !Bool
                  -- literals: match any of
                  | MatchStringAny
                  | MatchNumberAny
                  | MatchBoolAny
                  -- literals: null is just null
                  | MatchNull
                  -- conditions
                  | MatchAny
                  | MatchOr (KeyMap MatchPattern)
                  | MatchIfThen MatchPattern T.Text MatchPattern
                  -- funnel
                  | MatchFunnel
                  | MatchFunnelKeys
                  | MatchFunnelKeysU
                  -- special
                  | MatchRef String
                    deriving (Generic, Eq, Show)

instance Arbitrary MatchPattern where
  arbitrary = oneof [
      MatchObjectFull <$> arbitrary,
      MatchObjectPartial <$> arbitrary,
      MatchArrayContextFree <$> arbitrary,
      MatchStringExact <$> T.pack <$> arbitrary,
      MatchNumberExact <$> (Sci.scientific <$> arbitrary <*> arbitrary),
      MatchBoolExact <$> arbitrary,
      return $ MatchStringAny,
      return $ MatchNumberAny,
      return $ MatchBoolAny,
      return $ MatchNull,
      return $ MatchAny,
      MatchOr <$> arbitrary]
      --MatchIfThen <$> arbitrary <*> (T.pack <$> arbitrary) <*> arbitrary
      --return $ MatchFunnel,
      --return $ MatchFunnelKeys,
      --return $ MatchFunnelKeysU
      --MatchRef <$> arbitrary

makeBaseFunctor ''MatchPattern

instance ToJSON MatchPattern where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON MatchPattern
    -- No need to provide a parseJSON implementation.

                 -- structures - object
data MatchResult = MatchObjectFullResult (KeyMap MatchPattern) (KeyMap (ObjectKeyMatch MatchResult))
                 | MatchObjectPartialResult (KeyMap MatchPattern) (KeyMap (ObjectKeyMatch MatchResult))
                 -- structures - array
                 -- | MatchArrayAllResult (V.Vector MatchResult)
                 -- | MatchArraySomeResult (V.Vector (ArrayValMatch MatchResult))
                 -- | MatchArrayOneResult MatchResult
                 -- | MatchArrayExactResult [MatchResult]
                 | MatchArrayContextFreeResult (ContextFreeGrammarResult MatchPattern MatchResult)
                 -- literals: match particular value of
                 | MatchStringExactResult !T.Text
                 | MatchNumberExactResult !Sci.Scientific
                 | MatchBoolExactResult !Bool
                 -- literals: match any of
                 | MatchStringAnyResult !T.Text
                 | MatchNumberAnyResult !Sci.Scientific
                 | MatchBoolAnyResult !Bool
                 -- literals: null is just null
                 | MatchNullResult
                 -- conditions
                 | MatchAnyResult Value
                 | MatchOrResult (KeyMap MatchPattern) Key MatchResult
                 | MatchIfThenResult MatchPattern T.Text MatchResult
                 -- funnel
                 | MatchFunnelResult Value
                 | MatchFunnelKeysResult (KeyMap Value)
                 | MatchFunnelKeysUResult (KeyMap Value)
                 -- special
                 | MatchRefResult String MatchResult
                   deriving (Generic, Eq, Show)

instance Arbitrary MatchResult where
  arbitrary = oneof [
    MatchObjectFullResult <$> arbitrary <*> arbitrary,
    MatchObjectPartialResult <$> arbitrary <*> arbitrary,
    MatchArrayContextFreeResult <$> (SeqNode <$> arbitrary),
    MatchStringExactResult <$> T.pack <$> arbitrary,
    MatchNumberExactResult <$> (Sci.scientific <$> arbitrary <*> arbitrary),
    MatchBoolExactResult <$> arbitrary,
    MatchStringAnyResult <$> T.pack <$> arbitrary,
    MatchNumberAnyResult <$> (Sci.scientific <$> arbitrary <*> arbitrary),
    MatchBoolAnyResult <$> arbitrary,
    return $ MatchNullResult,
    MatchAnyResult <$> arbitrary,
    MatchOrResult <$> arbitrary <*> arbitrary <*> arbitrary]
    --MatchIfThenResult <$> arbitrary <*> (T.pack <$> arbitrary) <*> arbitrary,
    --MatchFunnelResult <$> arbitrary,
    --MatchFunnelKeysResult <$> arbitrary,
    --MatchFunnelKeysUResult <$> arbitrary
    --MatchRefResult <$> arbitrary <*> arbitrary

makeBaseFunctor ''MatchResult

instance ToJSON MatchResult where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON MatchResult
    -- No need to provide a parseJSON implementation.

-- MatchPattern × Value -(matchPattern)-> MatchResult

data MatchPath = ObjKey Key | ArrKey Int deriving (Generic, Eq, Show)

{-
gatherFunnel :: [Value] -> MatchPattern -> [Value]
gatherFunnel acc (MatchObjectPartialResult _ o) = L.foldl' gatherFunnel acc (KM.elems o)
gatherFunnel acc (MatchObject o) = L.foldl' gatherFunnel acc (KM.elems o) -- FIXME
gatherFunnel acc (MatchArraySomeResult _ o) = L.foldl' gatherFunnel acc (fmap snd o)
gatherFunnel acc (MatchArrayResult o) = L.foldl' gatherFunnel acc o
gatherFunnel acc (MatchArrayContextFreeResult a) = L.foldl' gatherFunnel acc a
gatherFunnel acc (MatchArrayOneResult o) = gatherFunnel acc o
gatherFunnel acc (MatchSimpleOrResult o) = gatherFunnel acc o
gatherFunnel acc (MatchFunnelResult r) = r:acc
gatherFunnel acc (MatchFunnelResultM r) = case asArray r of
                                               Nothing -> error ("aaa: " ++ show acc)
                                               Just a -> L.nub $ a ++ acc
gatherFunnel acc MatchLiteral = acc
gatherFunnel acc (MatchAnyResult _) = acc
-- gatherFunnel acc MatchIgnoreResult = acc
gatherFunnel acc (MatchString _) = acc
gatherFunnel acc (MatchNumber _) = acc
gatherFunnel acc MatchNull = acc
gatherFunnel acc x = error (show x)
--gatherFunnel acc _ = acc
-}

--
-- Convert Maybe to MatchStatus (e.g. a result of KM.lookup)
--

m2ms :: MatchStatus a -> Maybe a -> MatchStatus a
m2ms m v = case v of
              Just x -> MatchSuccess x
              Nothing -> m

-- pattern -> value -> result. result = value × pattern (is a product)
-- Both pattern and value can be derived from a result using trivial projections
-- (look category theory product)
matchPattern :: MatchPattern -> Value -> MatchStatus MatchResult

mObj :: Bool -> KeyMap (ObjectKeyMatch MatchPattern) -> Object -> MatchStatus (KeyMap MatchPattern, KeyMap (ObjectKeyMatch MatchResult))
mObj keepExt m a = do
  preResult <- L.foldl' (doKeyMatch m a) (MatchSuccess mempty) (keys m)
  L.foldl' f (MatchSuccess preResult) (keys a)
    where
      step k r acc req = case KM.lookup k a of
                      -- KeyOpt means key might be missing
                      Nothing -> if req
                                      then NoMatch $ "Required key " ++ show k ++ " not found in map"
                                      else MatchSuccess $ first (KM.insert k r) acc
                      -- if it exists, it must match
                      Just n -> case matchPattern r n of
                                     NoMatch s -> NoMatch s
                                     MatchFailure s -> MatchFailure s
                                     MatchSuccess s -> MatchSuccess $ second (KM.insert k el) acc
                                        where
                                          el = if req then (KeyReq s) else (KeyOpt s)
      doKeyMatch m a acc' k = do
        acc <- acc'
        v <- (m2ms $ MatchFailure "impossible") (KM.lookup k m)
        case v of
            KeyReq r -> step k r acc True
            KeyOpt r -> step k r acc False
            KeyExt _ -> MatchFailure "malformed grammar: KeyExt cannot be here"
      f acc' k = do
            acc <- acc'
            case KM.member k m of
                 True -> MatchSuccess acc
                 False -> case keepExt of
                               False -> NoMatch "extra key in arg"
                               True -> case KM.lookup k a of
                                            Nothing -> MatchFailure "impossible"
                                            Just v -> MatchSuccess $ second (KM.insert k (KeyExt v)) acc

matchPattern (MatchObjectFull m) (Object a) = (fmap $ uncurry MatchObjectFullResult) (mObj False m a)
matchPattern (MatchObjectPartial m) (Object a) = (fmap $ uncurry MatchObjectPartialResult) (mObj True m a)


matchPattern (MatchArrayContextFree m) (Array a) = do
  case contextFreeMatch m (V.toList a) matchPattern of
       NoMatch e -> NoMatch ("context-free nomatch: " ++ e)
       MatchFailure s -> MatchFailure s
       MatchSuccess x -> MatchSuccess (MatchArrayContextFreeResult x)

matchPattern (MatchArrayContextFree m) (Object a) = MatchFailure ("object in cf:\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode $ m) ++ "\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode $ toJSON $ a))

matchPattern MatchFunnel v = MatchSuccess $ MatchFunnelResult v

matchPattern MatchFunnelKeys (Object v) = MatchSuccess $ MatchFunnelKeysResult $ v
matchPattern MatchFunnelKeys _ = MatchFailure "MatchFunnelKeys met not an Object"

matchPattern MatchFunnelKeysU (Object v) = MatchSuccess $ MatchFunnelKeysUResult $ v
matchPattern MatchFunnelKeysU _ = MatchFailure "MatchFunnelKeysU met not an Object"

matchPattern (MatchIfThen baseMatch failMsg match) v =
  case matchPattern baseMatch v of
       NoMatch x -> NoMatch x
       MatchFailure f -> MatchFailure f
       MatchSuccess _ -> case matchPattern match v of
                            NoMatch x -> MatchFailure ((T.unpack failMsg) ++ show x)
                            MatchFailure f -> MatchFailure f
                            MatchSuccess s -> MatchSuccess (MatchIfThenResult baseMatch failMsg s)

matchPattern MatchAny a = MatchSuccess $ MatchAnyResult a
matchPattern (MatchOr ms) v = do
  let f (k, a) b = case matchPattern a v of
                     MatchSuccess x -> MatchSuccess (k, x)
                     MatchFailure f -> MatchFailure f
                     _ -> b
  (k, res) <- P.foldr f (NoMatch "or fail") (KM.toList ms)
  return $ MatchOrResult (KM.delete k ms) k res

-- specific (aka exact)
matchPattern (MatchStringExact m) (String a) = if m == a then MatchSuccess $ MatchStringExactResult a else NoMatch ("string mismatch: expected " ++ show m ++ " but found " ++ show a)
matchPattern (MatchNumberExact m) (Number a) = if m == a then MatchSuccess $ MatchNumberExactResult a else NoMatch ("number mismatch: expected " ++ show m ++ " but found " ++ show a)
matchPattern (MatchBoolExact m) (Bool a) = if m == a then MatchSuccess $ MatchBoolExactResult a else NoMatch ("bool mismatch: expected " ++ show m ++ " but found " ++ show a)
-- any (of a type)
matchPattern MatchStringAny (String a) = MatchSuccess $ MatchStringAnyResult a
matchPattern MatchNumberAny (Number a) = MatchSuccess $ MatchNumberAnyResult a
matchPattern MatchBoolAny (Bool a) = MatchSuccess $ MatchBoolAnyResult a
-- null is just null
matchPattern MatchNull Null = MatchSuccess MatchNullResult
-- default ca
matchPattern m a = NoMatch ("bottom reached:\n" ++ show m ++ "\n" ++ show a)

--contextFreeGrammarResultToGrammar :: (MatchResult -> MatchPattern) -> (ContextFreeGrammarResult (ContextFreeGrammar MatchPattern) MatchResult) -> (ContextFreeGrammar MatchPattern)
--contextFreeGrammarResultToGrammar :: (r -> p) -> (ContextFreeGrammarResult (ContextFreeGrammar p) r) -> (ContextFreeGrammar p)
--contextFreeGrammarResultToGrammar :: (Data.Functor.Foldable.Recursive t1, Data.Functor.Foldable.Base t1 ~ ContextFreeGrammarResultF a t2) => (t2 -> a) -> t1 -> ContextFreeGrammar a
contextFreeGrammarResultToGrammarAlg f = go
  where
    --go :: ContextFreeGrammarResultF (ContextFreeGrammar p) r (ContextFreeGrammar p) -> ContextFreeGrammar p
    go (CharNodeF r) = Char (f r)
    go (SeqNodeF r) = Seq r
    go (StarNodeEmptyF g) = Star g
    go (StarNodeValueF r) = Star (P.head r)
    go (PlusNodeF r) = Plus (P.head r)
    go (OrNodeF g k r) = Or (KM.insert k r g)
    go (OptionalNodeValueF r) = Optional r
    go (OptionalNodeEmptyF g) = Optional g

contextFreeGrammarResultToGrammar f = cata $ contextFreeGrammarResultToGrammarAlg f
  where

contextFreeGrammarResultToSource :: (r -> a) -> ContextFreeGrammarResult g r -> [a]
contextFreeGrammarResultToSource f = cata go
  where
    go (CharNodeF r) = [f r]
    go (SeqNodeF r) = P.concat r
    go (StarNodeEmptyF g) = []
    go (StarNodeValueF r) = P.concat r
    go (PlusNodeF r) = P.concat r
    go (OrNodeF g k r) = r
    go (OptionalNodeValueF r) = r
    go (OptionalNodeEmptyF g) = []

contextFreeGrammarResultToSourceBad f = cata go
  where
    go (CharNodeF r) = [f r]
    go (SeqNodeF r) = P.concat r
    go (StarNodeEmptyF g) = []
    go (StarNodeValueF r) = P.concat r
    go (PlusNodeF r) = P.concat r
    go (OrNodeF g k r) = [P.concat r]
    go (OptionalNodeValueF r) = [P.concat r]
    go (OptionalNodeEmptyF g) = []

--matchResultToPatternAlg :: (MatchResultF MatchPattern) -> MatchPattern


matchResultToPattern :: MatchResult -> MatchPattern
matchResultToPattern = cata go where
  go (MatchObjectFullResultF g r) = MatchObjectFull (KM.union (fmap KeyOpt g) r)
  go (MatchObjectPartialResultF g r) = MatchObjectPartial (KM.union (fmap KeyOpt g) (KM.filter f r))
    where
      f (KeyExt _) = False
      f _ = True
  go (MatchArrayContextFreeResultF r) = MatchArrayContextFree $ contextFreeGrammarResultToGrammar id r
  go (MatchStringExactResultF r) = MatchStringExact r
  go (MatchNumberExactResultF r) = MatchNumberExact r
  go (MatchBoolExactResultF r) = MatchBoolExact r
  go (MatchStringAnyResultF r) = MatchStringAny
  go (MatchNumberAnyResultF r) = MatchNumberAny
  go (MatchBoolAnyResultF r) = MatchBoolAny
  go MatchNullResultF = MatchNull
  go (MatchAnyResultF r) = MatchAny
  go (MatchOrResultF m k r) = MatchOr (KM.insert k r m)
  go (MatchIfThenResultF p errorMsg r) = MatchIfThen p errorMsg r
  go (MatchFunnelResultF r) = MatchFunnel
  go (MatchFunnelKeysResultF r) = MatchFunnelKeys
  go (MatchFunnelKeysUResultF r) = MatchFunnelKeysU
  go (MatchRefResultF ref r) = MatchRef ref

matchResultToValue :: MatchResult -> Value
matchResultToValue = cata go
  where
    --go :: (MatchResultF MatchPattern) -> Value
    go (MatchObjectFullResultF g r) = Object (KM.map f r)
      where
        f (KeyReq v) = v
        f (KeyOpt v) = v
        -- f (KeyExt v) = v
    go (MatchObjectPartialResultF g r) = Object (KM.map f r)
      where
        f (KeyReq v) = v
        f (KeyOpt v) = v
        f (KeyExt v) = v
    go (MatchArrayContextFreeResultF r) = Array $ V.fromList $ contextFreeGrammarResultToSource id r
    go (MatchStringExactResultF r) = String r
    go (MatchNumberExactResultF r) = Number r
    go (MatchBoolExactResultF r) = Bool r
    go (MatchStringAnyResultF r) = String r
    go (MatchNumberAnyResultF r) = Number r
    go (MatchBoolAnyResultF r) = Bool r
    go MatchNullResultF = Null
    go (MatchAnyResultF r) = r
    go (MatchOrResultF m k r) = r
    go (MatchIfThenResultF p errorMsg r) = r
    go (MatchFunnelResultF r) = r
    go (MatchFunnelKeysResultF r) = Object r
    go (MatchFunnelKeysUResultF r) = Object r
    go (MatchRefResultF ref r) = r


makeBaseFunctor ''Value

valueToExactGrammar :: Value -> MatchPattern
valueToExactGrammar = cata go
  where
    go (ObjectF a) = MatchObjectFull (fmap KeyReq a)
    go (ArrayF a) = MatchArrayContextFree $ Seq $ (fmap Char) $ V.toList a
    go (StringF a) = MatchStringExact a
    go (NumberF a) = MatchNumberExact a
    go (BoolF a) = MatchBoolExact a
    go NullF = MatchNull

valueToExactResult :: Value -> MatchStatus MatchResult
valueToExactResult v = matchPattern g v where g = valueToExactGrammar v


extractObjectKeyMatch :: a -> (ObjectKeyMatch a) -> a
extractObjectKeyMatch ext (KeyReq a) = a
extractObjectKeyMatch ext (KeyOpt a) = a
extractObjectKeyMatch ext (KeyExt v) = ext


--contextFreeGrammarIsWellFormed

isStarLike :: ContextFreeGrammar a -> Bool
isStarLike (Star _) = True
isStarLike (Plus _) = True
isStarLike (Optional _) = True
isStarLike _ = False

isSeq :: ContextFreeGrammar a -> Bool
isSeq (Seq _) = True
isSeq _ = False

contextFreeGrammarIsWellFormed :: Show a => (a -> Bool) -> ContextFreeGrammar a -> Bool
contextFreeGrammarIsWellFormed f = para go
  where
    --go :: Show a => ContextFreeGrammarF a (ContextFreeGrammar a, Bool) -> Bool
    go (CharF c) = f c
    go (SeqF a) = P.all id (fmap snd a)
    go (OrF a) = P.all id (fmap snd (KM.elems a))
    go (StarF (p, a)) = (not (isStarLike p)) && a
    go (PlusF (p, a)) = (not (isStarLike p)) && a
    go (OptionalF (p, a)) = (not (isStarLike p)) && a

-- is well-formed

matchPatternIsWellFormed :: MatchPattern -> Bool
matchPatternIsWellFormed = cata go
  where
    go (MatchObjectFullF g) = L.foldl' f True (KM.elems g)
      where
        f acc (KeyOpt x) = acc && x
        f acc (KeyReq x) = acc && x
        f acc (KeyExt _) = False
    go (MatchObjectPartialF g) = L.foldl' f True (KM.elems g)
      where
        f acc (KeyOpt x) = acc && x
        f acc (KeyReq x) = acc && x
        f acc (KeyExt _) = False
    go (MatchArrayContextFreeF g) = isSeq g && contextFreeGrammarIsWellFormed id g
    go (MatchStringExactF _) = True
    go (MatchNumberExactF _) = True
    go (MatchBoolExactF _) = True
    go MatchStringAnyF = True
    go MatchNumberAnyF = True
    go MatchBoolAnyF = True
    go MatchNullF = True
    go MatchAnyF = True
    go (MatchOrF g) = P.all id (KM.elems g)
    go (MatchIfThenF _ _ _) = False -- TODO
    go MatchFunnelF = True
    go MatchFunnelKeysF = True
    go MatchFunnelKeysUF = True
    --go MatchRef String =


isStarNodeLike :: ContextFreeGrammarResult g r -> Bool
isStarNodeLike (StarNodeValue _) = True
isStarNodeLike (StarNodeEmpty _) = True
isStarNodeLike (PlusNode _) = True
isStarNodeLike (OptionalNodeValue _) = True
isStarNodeLike (OptionalNodeEmpty _) = True
isStarNodeLike _ = False

allTheSame [] = True
allTheSame (x:xs) = P.all (== x) xs

--contextFreeGrammarResultIsWellFormed :: (Show g, Show r) => (g -> Bool) -> (r -> Bool) -> ContextFreeGrammarResult g r -> Bool
--contextFreeGrammarResultIsWellFormed :: (Show g, Show r) => (g -> Bool) -> (r -> Bool) -> ContextFreeGrammarResult g r -> Bool
contextFreeGrammarResultIsWellFormed :: (MatchPattern -> Bool) -> (Bool -> Bool) -> ContextFreeGrammarResult MatchPattern (MatchResult, Bool) -> Bool
contextFreeGrammarResultIsWellFormed gf rf = para go
  where
    --go :: ContextFreeGrammarResultF MatchPattern MatchResult (MatchResult, Bool) -> Bool
    go (CharNodeF (_, r)) = rf r
    go (SeqNodeF r) = P.all id (fmap snd r)
    go (StarNodeEmptyF g) = contextFreeGrammarIsWellFormed gf g
    go (StarNodeValueF r) =
      (not $ isStarNodeLike (fst $ P.head r))
      && (snd $ P.head r)
      && (allTheSame $ (fmap (contextFreeGrammarResultToGrammar (matchResultToPattern . fst))) $ (fmap fst r))
    go (PlusNodeF r) =
      (not $ isStarNodeLike (fst $ P.head r))
      && (snd $ P.head r)
      && (allTheSame $ (fmap (contextFreeGrammarResultToGrammar (matchResultToPattern . fst))) $ (fmap fst r))
    go (OrNodeF g k (_, r)) = 
      P.all (contextFreeGrammarIsWellFormed gf) (KM.elems g)
      && (not $ KM.member k g)
      && r
    go (OptionalNodeEmptyF g) = contextFreeGrammarIsWellFormed gf g
    go (OptionalNodeValueF r) = (not $ isStarNodeLike (fst r)) && (snd r) {--}

matchResultIsWellFormed :: MatchResult -> Bool
matchResultIsWellFormed = para check
  where
    check (MatchArrayContextFreeResultF g) = contextFreeGrammarResultIsWellFormed matchPatternIsWellFormed id g
    check (MatchObjectFullResultF g r) = gc && rc && nck
      where
        f acc (KeyOpt (_, x)) = acc && x
        f acc (KeyReq (_, x)) = acc && x
        f acc (KeyExt _) = False
        rc = L.foldl' f True (KM.elems r)
        gc = P.all matchPatternIsWellFormed (KM.elems g)
        nck = S.null $ S.intersection (S.fromList $ KM.keys g) (S.fromList $ KM.keys r)
    check (MatchObjectPartialResultF g r) = gc && rc && nck
      where
        f acc (KeyOpt (_, x)) = acc && x
        f acc (KeyReq (_, x)) = acc && x
        f acc (KeyExt _) = False
        rc = L.foldl' f True (KM.elems r)
        gc = P.all matchPatternIsWellFormed (KM.elems g)
        nck = S.null $ S.intersection (S.fromList $ KM.keys g) (S.fromList $ KM.keys r)
    check (MatchStringExactResultF _) = True
    check (MatchNumberExactResultF _) = True
    check (MatchBoolExactResultF _) = True
    check (MatchStringAnyResultF _) = True
    check (MatchNumberAnyResultF _) = True
    check (MatchBoolAnyResultF _) = True
    check MatchNullResultF = True
    check (MatchAnyResultF _) = True
    check (MatchOrResultF g k (_, r)) = 
      P.all matchPatternIsWellFormed (KM.elems g)
      && (not $ KM.member k g)
      && r
    check (MatchIfThenResultF _ _ _) = False -- TODO
    check (MatchFunnelResultF _) = True
    check (MatchFunnelKeysResultF _) = True
    check (MatchFunnelKeysUResultF _) = True

-- is movable

contextFreeGrammarIsMovable :: (a -> Bool) -> ContextFreeGrammar a -> Bool
contextFreeGrammarIsMovable f = cata go
  where
    go (CharF a) = f a
    go (SeqF a) = P.any id a
    go (OrF a) = True --P.any id (KM.elems a)
    go (StarF a) = True
    go (PlusF a) = True
    go (OptionalF a) = True

contextFreeGrammarResultIsMovable :: (g -> Bool) -> (r -> Bool) -> ContextFreeGrammarResult g r -> Bool
contextFreeGrammarResultIsMovable gf rf = cata go
  where
    go (CharNodeF r) = rf r
    go (SeqNodeF r) = P.any id r
    go (StarNodeEmptyF g) = True
    go (StarNodeValueF r) = True
    go (PlusNodeF r) = True
    go (OrNodeF g k r) = True -- r || P.any (contextFreeGrammarIsMovable gf) (KM.elems g)
    go (OptionalNodeValueF r) = True
    go (OptionalNodeEmptyF g) = True

matchPatternIsMovable :: MatchPattern -> Bool
matchPatternIsMovable = cata go
  where
    go (MatchObjectFullF g) = L.foldl' f False (KM.elems g)
      where
        f acc (KeyOpt _) = True
        f acc (KeyReq x) = x || acc
        f acc (KeyReq x) = error $ "must not be here"
    go (MatchObjectPartialF g) = True -- may have ext --P.any (extractObjectKeyMatch $ error "must not be here") (KM.elems g)
    go (MatchArrayContextFreeF g) = contextFreeGrammarIsMovable id g
    go (MatchStringExactF _) = False
    go (MatchNumberExactF _) = False
    go (MatchBoolExactF _) = False
    go MatchStringAnyF = True
    go MatchNumberAnyF = True
    go MatchBoolAnyF = True
    go MatchNullF = False
    go MatchAnyF = True
    go (MatchOrF g) = True --P.any id (KM.elems g)
    go (MatchIfThenF _ _ g) = g
    go MatchFunnelF = True
    go MatchFunnelKeysF = True
    go MatchFunnelKeysUF = True
    --go MatchRef String =

isKeyReq (KeyReq _) = True
isKeyReq _ = False

getKeyReqs :: [ObjectKeyMatch b] -> [b]
getKeyReqs xs = fmap (extractObjectKeyMatch $ error "must not be here697") $ P.filter isKeyReq xs

isKeyOpt (KeyOpt _) = True
isKeyOpt _ = False

getKeyOpts :: [ObjectKeyMatch b] -> [b]
getKeyOpts xs = fmap (extractObjectKeyMatch $ error "must not be here703") $ P.filter isKeyOpt xs

matchResultIsMovableAlg :: MatchResultF Bool -> Bool
matchResultIsMovableAlg = check where
    check (MatchObjectFullResultF g r) = (
      (not $ KM.null g)
      || (not $ P.null $ getKeyOpts $ KM.elems r)
      || (P.any id $ getKeyReqs $ KM.elems r))
    check (MatchObjectPartialResultF g r) = True --P.any (extractObjectKeyMatch $ error "must not be here") (KM.elems r) || P.any matchPatternIsMovable g
    check (MatchArrayContextFreeResultF g) = contextFreeGrammarResultIsMovable matchPatternIsMovable id g
    check (MatchStringExactResultF _) = False
    check (MatchNumberExactResultF _) = False
    check (MatchBoolExactResultF _) = False
    check (MatchStringAnyResultF _) = True
    check (MatchNumberAnyResultF _) = True
    check (MatchBoolAnyResultF _) = True
    check MatchNullResultF = False
    check (MatchAnyResultF _) = True
    check (MatchOrResultF g _ r) = r || P.any matchPatternIsMovable (KM.elems g)
    check (MatchIfThenResultF _ _ g) = g
    check (MatchFunnelResultF _) = True
    check (MatchFunnelKeysResultF _) = True
    check (MatchFunnelKeysUResultF _) = True

matchResultIsMovable :: MatchResult -> Bool
matchResultIsMovable = cata matchResultIsMovableAlg


-- Thick/Thin stuff
                  -- structures - object
data ThickMatchPattern = ThickMatchObjectFull (KeyMap (ObjectKeyMatch ThickMatchPattern))
                  | ThickMatchObjectPartial (KeyMap (ObjectKeyMatch ThickMatchPattern))
                  -- structures - array
                  -- | ThickMatchArrayAll ThickMatchPattern
                  -- | ThickMatchArraySome ThickMatchPattern
                  -- | ThickMatchArrayOne ThickMatchPattern
                  -- | ThickMatchArrayExact [ThickMatchPattern]
                  | ThickMatchArrayContextFree (ContextFreeGrammar ThickMatchPattern)
                  -- literals: match particular value of
                  | ThickMatchStringExact !T.Text
                  | ThickMatchNumberExact !Sci.Scientific
                  | ThickMatchBoolExact !Bool
                  -- literals: match any of
                  | ThickMatchStringAny
                  | ThickMatchNumberAny
                  | ThickMatchBoolAny
                  -- literals: null is just null
                  | ThickMatchNull
                  -- conditions
                  | ThickMatchAny
                  | ThickMatchOr (KeyMap ThickMatchPattern)
                  | ThickMatchIfThen ThickMatchPattern T.Text ThickMatchPattern
                  -- funnel
                  | ThickMatchFunnel
                  | ThickMatchFunnelKeys
                  | ThickMatchFunnelKeysU
                  -- special
                  | ThickMatchRef String
                    deriving (Generic, Eq, Show)

instance Arbitrary ThickMatchPattern where
  arbitrary = oneof [
      ThickMatchObjectFull <$> arbitrary,
      ThickMatchObjectPartial <$> arbitrary,
      ThickMatchArrayContextFree <$> arbitrary,
      ThickMatchStringExact <$> T.pack <$> arbitrary,
      ThickMatchNumberExact <$> (Sci.scientific <$> arbitrary <*> arbitrary),
      ThickMatchBoolExact <$> arbitrary,
      return $ ThickMatchStringAny,
      return $ ThickMatchNumberAny,
      return $ ThickMatchBoolAny,
      return $ ThickMatchNull,
      return $ ThickMatchAny,
      ThickMatchOr <$> arbitrary,
      ThickMatchIfThen <$> arbitrary <*> (T.pack <$> arbitrary) <*> arbitrary,
      return $ ThickMatchFunnel,
      return $ ThickMatchFunnelKeys,
      return $ ThickMatchFunnelKeysU,
      ThickMatchRef <$> arbitrary]


makeBaseFunctor ''ThickMatchPattern

instance ToJSON ThickMatchPattern where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON ThickMatchPattern
    -- No need to provide a parseJSON implementation.

data ThickContextFreeGrammar a = ThickChar a
                               | ThickSeq [(ThickContextFreeGrammar a)]
                               | ThickOr (KeyMap (ThickContextFreeGrammar a))
                               | ThickStar (ThickContextFreeGrammar a)
                               | ThickPlus (ThickContextFreeGrammar a)
                               | ThickOptional (ThickContextFreeGrammar a)
                                 deriving (Generic, Eq, Show, Functor, Foldable, Traversable)

instance Arbitrary a => Arbitrary (ThickContextFreeGrammar a) where
  arbitrary = oneof [
    ThickChar <$> arbitrary,
    ThickSeq <$> arbitrary,
    ThickOr <$> arbitrary,
    ThickStar <$> arbitrary,
    ThickPlus <$> arbitrary,
    ThickOptional <$> arbitrary]

makeBaseFunctor ''ThickContextFreeGrammar

instance ToJSON a => ToJSON (ThickContextFreeGrammar a) where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON a => FromJSON (ThickContextFreeGrammar a)


tMap t v = Object $ KM.fromList [(K.fromString "type", String t), (K.fromString "value", v)]
tMapT t = Object $ KM.fromList [(K.fromString "type", String t)]
tMapK t k = Object $ KM.fromList [(K.fromString "type", String t), (K.fromString "key", (String . T.pack . K.toString) k)]
tMapF t f = Object $ KM.fromList [(K.fromString "type", String t), (K.fromString "flag", Bool f)]
tMapKV t k v = Object $ KM.fromList [(K.fromString "type", String t), (K.fromString "key", (String . T.pack . K.toString) k), (K.fromString "value", v)]
tMapFV t f v = Object $ KM.fromList [(K.fromString "type", String t), (K.fromString "flag", Bool f), (K.fromString "value", v)]

contextFreeGrammarResultToThinValue :: ContextFreeGrammarResult MatchPattern (Maybe Value) -> Maybe Value
contextFreeGrammarResultToThinValue = cata go
  where
    gg = contextFreeGrammarIsMovable matchPatternIsMovable
    go :: ContextFreeGrammarResultF MatchPattern (Maybe Value) (Maybe Value) -> Maybe Value
    go (CharNodeF r) = r --fmap (tMap "Char") r
    go (SeqNodeF r) = let l = P.map fromJust $ P.filter isJust r in
      if P.null l
         then Nothing
         else if P.length l == 1
                 then Just $ P.head l
                 else Just $ tMap "SeqNode" $ Array $ V.fromList $ l
    go (StarNodeEmptyF g) = Just $ if gg g
                                      then tMap "StarNode" $ Array $ V.fromList ([] :: [Value])
                                      else tMap "StarNodeTrivial" $ Number 0
    go (StarNodeValueF r) = Just $ if P.head r == Nothing -- aka grammar is trivial
                               then tMap "StarNodeTrivial" $ Number $ Sci.scientific (toInteger (P.length r)) 0
                               else tMap "StarNode" $ Array $ V.fromList $ P.map fromJust r
    go (PlusNodeF r) = Just $ if P.head r == Nothing -- aka grammar is trivial
                               then tMap "PlusNodeTrivial" $ Number $ Sci.scientific (toInteger (P.length r)) 0
                               else tMap "PlusNode" $ Array $ V.fromList $ P.map fromJust r
    go (OrNodeF g k r) = Just $ if r == Nothing
                            then tMapK "OrNodeTrivial" k
                            else tMapKV "OrNode" k (fromJust r)
    go (OptionalNodeValueF r) = Just $ if r == Nothing
                            then tMapF "OptionalNodeTrivial" True
                            else tMapFV "OptionalNode" True (fromJust r)
    go (OptionalNodeEmptyF g) = Just $ if not $ gg g
                            then tMapF "OptionalNodeTrivial" False
                            else tMapF "OptionalNode" False


matchResultToThinValue :: MatchResult -> Maybe Value
matchResultToThinValue = cata go
  where
    filterEmpty a = (KM.map fromJust (KM.filter isJust a))
    nonEmptyMap m = if KM.null m then Nothing else Just m
    replaceSingleton (Object m) = if (KM.size m) == 1 then P.head (KM.elems m) else Object m
    go :: MatchResultF (Maybe Value) -> Maybe Value
    go (MatchObjectFullResultF g r) = fmap (replaceSingleton . Object) $ nonEmptyMap $ filterEmpty $ u
      where
        f (KeyReq v) = v
        f (KeyOpt v) = case v of
                            Nothing -> Just $ Bool True
                            Just a -> Just a
        f (KeyExt _) = error "must not be here4"
        optf :: MatchPattern -> Maybe Value
        optf x = case matchPatternIsMovable x of
                      True -> Nothing
                      False -> Just $ Bool False
        u = KM.union (KM.map f r) (fmap optf g)
    go (MatchObjectPartialResultF g r) = fmap Object $ Just $ filterEmpty $ u
      where
        f (KeyReq v) = v
        f (KeyOpt v) = case v of
                            Nothing -> Just $ Bool True
                            Just a -> Just $ tMap "KeyOpt" a
        f (KeyExt _) = error "must not be here5"
        optf :: MatchPattern -> Maybe Value
        optf x = case matchPatternIsMovable x of
                      True -> Just $ tMapT "KeyOpt"
                      False -> Just $ Bool False
        u = KM.union (KM.map f r) (fmap optf g)
    go (MatchArrayContextFreeResultF r) = contextFreeGrammarResultToThinValue r
    go (MatchStringExactResultF r) = Nothing
    go (MatchNumberExactResultF r) = Nothing
    go (MatchBoolExactResultF r) = Nothing
    go (MatchStringAnyResultF r) = Just $ String r
    go (MatchNumberAnyResultF r) = Just $ Number r
    go (MatchBoolAnyResultF r) = Just $ Bool r
    go MatchNullResultF = Nothing
    go (MatchAnyResultF r) = Just $ r
    go (MatchOrResultF g k r) = Just $ if r == Nothing
                                   then tMapK "OrTrivial" k
                                   else tMapKV "Or" k (fromJust r)
    go (MatchIfThenResultF p errorMsg r) = r
    go (MatchFunnelResultF r) = Just $ r
    go (MatchFunnelKeysResultF r) = Just $ Object r
    go (MatchFunnelKeysUResultF r) = Just $ Object r
    go (MatchRefResultF ref r) = r

-- thin pattern
or2 = (MatchOr (KM.fromList [(K.fromString "option1", (MatchNumberExact 1)), (K.fromString "option2", MatchNumberAny)]))


thinSeq as v = do
        let gs = fmap (contextFreeGrammarIsMovable matchPatternIsMovable) as
        v <- case P.length (P.filter id gs) of
                  0 ->
                    do
                      return $ []
                  1 ->
                    do
                      return $ [v]
                  _ ->
                    do
                      v <- (m2ms $ MatchFailure $ "data error7" ++ show v) $ asKeyMap v
                      itsType <- (m2ms $ MatchFailure $ "data error8" ++ show v) $ KM.lookup "type" v
                      itsValue <- (m2ms $ MatchFailure $ "data error9" ++ show v) $ KM.lookup "value" v
                      (m2ms $ MatchFailure $ "data error10" ++ show v) $ asArray itsValue
        let f acc' (a, gg) = do
                (ii, acc) <- acc'
                let (i:is) = ii
                if gg -- movable
                  then fmap (\x -> (is, acc <> (bimap All L.singleton x))) (thinContextFreeMatch a (Just i))
                  else fmap (\x -> (ii, acc <> (bimap (const mempty) L.singleton x))) (thinContextFreeMatch a Nothing)
        r <- L.foldl' f (MatchSuccess (v, mempty)) $ P.zip as gs
        _ <- if P.null $ fst r then MatchSuccess () else MatchFailure $ "not all consumed" ++ show (fst r)
        let r1@(bb, _) = bimap getAll SeqNode (snd r)
        if not bb then MatchFailure ("bb fail" ++ show as) else MatchSuccess r1
        --MatchSuccess r1

thinContextFreeMatch :: ContextFreeGrammar MatchPattern -> Maybe Value -> MatchStatus (Bool, ContextFreeGrammarResult MatchPattern MatchResult)
thinContextFreeMatch (Char a) v = do
  case thinPattern a v of
       NoMatch s -> NoMatch ("no char match: " ++ s)
       MatchFailure s -> MatchFailure ("thinContextFreeMatch: " ++ s)
       MatchSuccess (b, r) -> MatchSuccess (b, CharNode r)

thinContextFreeMatch (Seq as) Nothing = if not $ contextFreeGrammarIsMovable matchPatternIsMovable (Seq as)
                                           then thinSeq as (Array $ V.fromList [])
                                           else NoMatch "data error5"
thinContextFreeMatch (Seq as) (Just v) = do
  if not $ contextFreeGrammarIsMovable matchPatternIsMovable (Seq as)
     then NoMatch ("data error6:\n\n" ++ show as ++ "\n\n" ++ show v ++ "\n\n")
     else thinSeq as v

thinContextFreeMatch (Or ms) (Just (Object v)) = do -- or requires an exsistance of a value (Just)
  itsType <- (m2ms $ MatchFailure ("data error1" ++ show v)) $ KM.lookup (K.fromString "type") v -- OrNodeTrivial or OrNode
  itsKey <- (m2ms $ MatchFailure ("data error 951: " ++ show v)) $ KM.lookup (K.fromString "key") v
  itsKey <- (m2ms $ MatchFailure ("data error3" ++ show itsKey)) $ asString itsKey
  let itsK = (K.fromString . T.unpack) itsKey
  itsMatch <- (m2ms $ MatchFailure ("data error4" ++ show ms)) $ KM.lookup itsK ms
  fmap ((\a -> (True, a)) . (OrNode (KM.delete itsK ms) itsK) . snd) (thinContextFreeMatch itsMatch (KM.lookup (K.fromString "value") v))

thinContextFreeMatch (Star a) (Just (Object v)) = do
  let gg = contextFreeGrammarIsMovable matchPatternIsMovable
  itsType <- (m2ms $ MatchFailure ("data error1" ++ show v)) $ KM.lookup (K.fromString "type") v -- OrNodeTrivial or OrNode
  itsValue <- (m2ms $ MatchFailure ("data error2" ++ show v)) $ KM.lookup (K.fromString "value") v
  if gg a
     then -- actual
        do
          itsValue <- (m2ms $ MatchFailure ("data error2" ++ show itsValue)) $ asArray itsValue
          if P.null itsValue
             then
                return $ (True, StarNodeEmpty a)
             else
              do
                aa <- P.traverse (thinContextFreeMatch a) (fmap Just itsValue)
                let ab = (P.map snd aa)
                return $ (True, StarNodeValue ab)
      else -- trivial
        do
          itsValue <- (m2ms $ MatchFailure ("data error2" ++ show itsValue)) $ asNumber itsValue
          if itsValue == 0
             then
                return (True, StarNodeEmpty $ a)
              else
                do
                  (_, aa) <- thinContextFreeMatch a Nothing
                  return (True, StarNodeValue $ P.take (fromIntegral $ Sci.coefficient itsValue) $ P.repeat aa)

thinContextFreeMatch (Plus a) (Just (Object v)) = do
  let gg = contextFreeGrammarIsMovable matchPatternIsMovable
  itsType <- (m2ms $ MatchFailure ("data error1" ++ show v)) $ KM.lookup (K.fromString "type") v -- OrNodeTrivial or OrNode
  itsValue <- (m2ms $ MatchFailure ("data error2" ++ show v)) $ KM.lookup (K.fromString "value") v
  if gg a
     then -- actual
        do
          itsValue <- (m2ms $ MatchFailure ("data error3" ++ show v)) $ asArray itsValue
          aa <- P.traverse (thinContextFreeMatch a) (fmap Just itsValue)
          let ab = (P.map snd aa)
          return $ (True, PlusNode ab)
      else -- trivial
        do
          itsValue <- (m2ms $ MatchFailure ("data error4" ++ show v)) $ asNumber itsValue
          (_, aa) <- thinContextFreeMatch a Nothing
          return (True, PlusNode $ P.take (fromIntegral $ Sci.coefficient itsValue) $ P.repeat aa)

thinContextFreeMatch (Optional a) (Just (Object v)) = do
  let gg = contextFreeGrammarIsMovable matchPatternIsMovable
  itsType <- (m2ms $ NoMatch ("data error5" ++ show v)) $ KM.lookup (K.fromString "type") v -- OrNodeTrivial or OrNode
  itsType <- (m2ms $ NoMatch ("data error1129" ++ show v)) $ asString itsType -- OrNodeTrivial or OrNode
  _ <- if itsType == "OptionalNode" || itsType == "OptionalNodeTrivial" then MatchSuccess () else NoMatch ("type mismatch: "  ++ T.unpack itsType)
  itsKey <- (m2ms $ MatchFailure ("data error6" ++ (show . TL.unpack . TL.decodeUtf8 . encode) v)) $ KM.lookup (K.fromString "flag") v
  itsKey <- (m2ms $ MatchFailure ("data error7" ++ show v)) $ asBool itsKey
  if itsKey
     then
        do
          r <- thinContextFreeMatch a (KM.lookup (K.fromString "value") v)
          return $ bimap (const True) OptionalNodeValue r
      else
        do
          return $ (True, OptionalNodeEmpty a)

thinContextFreeMatch a xs = error ("no match for: " ++ (show a) ++ " " ++ (show xs))

tObj :: Bool -> KeyMap (ObjectKeyMatch MatchPattern) -> (KeyMap Value) -> MatchStatus (KeyMap MatchPattern, KeyMap (ObjectKeyMatch MatchResult))
tObj keepExt m a = do
  preResult <- L.foldl' (doKeyMatch m a) (MatchSuccess mempty) (keys m)
  L.foldl' f (MatchSuccess preResult) (keys a)
    where
      gg = matchPatternIsMovable
      step k r acc req = case KM.lookup k a of
                      -- KeyOpt means key might be missing
                      Nothing -> if req
                                    then NoMatch $ "Required key " ++ show k ++ " not found in map"
                                    else MatchSuccess $ first (KM.insert k r) acc
                      -- if it exists, it must match
                      Just n -> case fmap snd $ thinPattern r (Just n) of
                                     NoMatch s -> NoMatch s
                                     MatchFailure s -> MatchFailure s
                                     MatchSuccess s -> MatchSuccess $ second (KM.insert k el) acc
                                        where
                                          el = if req then (KeyReq s) else (KeyOpt s)
      doKeyMatch m a acc' k = do
        acc <- acc'
        v <- (m2ms $ MatchFailure "impossible") (KM.lookup k m)
        case v of
            KeyReq r -> step k r acc True
            KeyOpt r -> step k r acc False
            KeyExt _ -> MatchFailure "malformed grammar: KeyExt cannot be here"
      f acc' k = do
            acc <- acc'
            case KM.member k m of
                 True -> MatchSuccess acc
                 False -> case keepExt of
                               False -> NoMatch "extra key in arg"
                               True -> case KM.lookup k a of
                                            Nothing -> MatchFailure "impossible"
                                            Just v -> MatchSuccess $ second (KM.insert k (KeyExt v)) acc


--thinPatternMap m a allowExt = undefined

thinPatternMap allowExt m a = do
  let f1 (KeyReq x) = matchPatternIsMovable x
      f1 (KeyOpt _) = True
      f1 (KeyExt _) = error "must not be here1"
  let ms = KM.map f1 m
  let mm = P.any id (KM.elems ms)

  let f2 (KeyReq x) = matchPatternIsMovable x
      f2 (KeyOpt x) = matchPatternIsMovable x
      f2 (KeyExt _) = error "must not be here2"
  let vs = KM.map f2 m

  na <- case (KM.size (KM.filter id ms), allowExt) of
             (0, False) -> do
               case a of
                    Nothing -> return $ KM.empty
                    (Just x) -> MatchFailure ("must not be here 1071: " ++ show x)
             (1, False) -> do -- very special case (replaceSingleton)
                     aa <- (m2ms $ MatchFailure ("must not be such 1073: " ++ show a)) a
                     return $ KM.singleton (P.head (KM.keys (KM.filter id ms))) aa
             _ -> do
                     aa <- (m2ms $ MatchFailure ("must not be such 1076: " ++ show a)) a
                     (m2ms $ MatchFailure ("must not be such 1077: " ++ show a)) $ asKeyMap aa

  let f acc' k = do
        acc <- acc'
        mk <- (m2ms $ MatchFailure "impossible") $ KM.lookup k vs
        v <- (m2ms $ MatchFailure "impossible") $ KM.lookup k m
        case (v, mk) of
             -- trivial
             (KeyReq v, False) -> case KM.lookup k na of
                                       Nothing -> do
                                         e <- (fmap snd) $ thinPattern v Nothing
                                         return $ second (KM.insert k $ KeyReq e) acc
                                       Just x -> MatchFailure ("must not be here 1089: " ++ show x)
             (KeyOpt v, False) -> do
               vv <- (m2ms $ MatchFailure ("doesn't exist1" ++ show na)) $ KM.lookup k na
               flg <- (m2ms $ MatchFailure ("doesn't exist5" ++ show vv)) $ asBool vv
               case flg of
                    False -> return $ first (KM.insert k v) acc
                    True -> do
                      e <- (fmap snd) $ thinPattern v Nothing
                      return $ second (KM.insert k $ KeyOpt e) acc
             -- movable
             (KeyReq v, True) -> do
               case KM.lookup k na of
                    Nothing -> NoMatch "Key not found"
                    Just x -> do
                      e <- (fmap snd) $ thinPattern v (Just x)
                      return $ second (KM.insert k $ KeyReq e) acc
             (KeyOpt v, True) -> do
               case KM.lookup k na of
                    Nothing -> return $ first (KM.insert k v) acc
                    Just x -> do
                      e <- (fmap snd) $ thinPattern v (Just x)
                      return $ second (KM.insert k $ KeyOpt e) acc
             -- error
             (KeyExt v, _) -> MatchFailure ("must not be here" ++ show v)

  (os, xs) <- L.foldl' f (MatchSuccess mempty) (KM.keys m)
  let rst = KM.filterWithKey (\kk _ -> not $ KM.member kk m) na
  xs <- if allowExt && (not $ KM.null rst)
          then NoMatch "might not have extra"
          else return $ KM.union xs $ (KM.map KeyExt) rst

  let c = if allowExt then MatchObjectPartialResult else MatchObjectFullResult
  return $ (True, c os xs)

thinPattern :: MatchPattern -> Maybe Value -> MatchStatus (Bool, MatchResult)
thinPattern (MatchObjectFull m) a = thinPatternMap False m a
thinPattern (MatchObjectPartial m) a = thinPatternMap True m a

thinPattern (MatchArrayContextFree m) a = do
  case thinContextFreeMatch m a of
       NoMatch e -> NoMatch ("context-free nomatch: " ++ e)
       MatchFailure s -> MatchFailure s
       MatchSuccess (b, x) -> MatchSuccess (b, (MatchArrayContextFreeResult x))

thinPattern MatchFunnel (Just v) = MatchSuccess (True, MatchFunnelResult v)

thinPattern MatchFunnelKeys (Just (Object v)) = MatchSuccess (True, MatchFunnelKeysResult v)
thinPattern MatchFunnelKeys _ = MatchFailure "MatchFunnelKeys met not an Object or met Nothing"

thinPattern MatchFunnelKeysU (Just (Object v)) = MatchSuccess (True, MatchFunnelKeysUResult v)
thinPattern MatchFunnelKeysU _ = MatchFailure "MatchFunnelKeysU met not an Object or met Nothing"

thinPattern (MatchIfThen baseMatch failMsg match) v =
  case thinPattern baseMatch v of
       NoMatch x -> NoMatch x
       MatchFailure f -> MatchFailure f
       MatchSuccess _ -> case thinPattern match v of
                            NoMatch x -> MatchFailure ((T.unpack failMsg) ++ show x)
                            MatchFailure f -> MatchFailure f
                            MatchSuccess s -> MatchSuccess $ fmap (MatchIfThenResult baseMatch failMsg) s

thinPattern MatchAny (Just a) = MatchSuccess (True, MatchAnyResult a)

thinPattern (MatchOr ms) (Just (Object v)) = do -- or requires an exsistance of a value (Just)
  itsType <- (m2ms $ MatchFailure ("data error1" ++ show v)) $ KM.lookup (K.fromString "type") v
  itsKey <- (m2ms $ MatchFailure ("data error2" ++ show v)) $ KM.lookup (K.fromString "key") v
  itsKey <- (m2ms $ MatchFailure ("data error3" ++ show v)) $ asString itsKey
  let itsK = (K.fromString . T.unpack) itsKey
  itsMatch <- (m2ms $ MatchFailure ("data error4" ++ show v)) $ KM.lookup itsK ms
  fmap ((\a -> (True, a)) . (MatchOrResult (KM.delete itsK ms) itsK) . snd) (thinPattern itsMatch (KM.lookup (K.fromString "value") v))


-- specific (aka exact)
thinPattern (MatchStringExact m) Nothing = MatchSuccess (False, MatchStringExactResult m)
thinPattern (MatchNumberExact m) Nothing = MatchSuccess (False, MatchNumberExactResult m)
thinPattern (MatchBoolExact m) Nothing = MatchSuccess (False, MatchBoolExactResult m)
-- any (of a type)
thinPattern MatchStringAny (Just (String a)) = MatchSuccess (True, MatchStringAnyResult a)
thinPattern MatchNumberAny (Just (Number a)) = MatchSuccess (True, MatchNumberAnyResult a)
thinPattern MatchBoolAny (Just (Bool a)) = MatchSuccess (True, MatchBoolAnyResult a)
-- null is just null
thinPattern MatchNull Nothing = MatchSuccess (False, MatchNullResult)
-- default ca
thinPattern m a = NoMatch ("thinPattern bottom reached:\n" ++ show m ++ "\n" ++ show a)

-- Match functions end

g00 = (Seq [(Star (Char 1)), (Optional (Char 4))])

main1 = do
  contextFreeMatch g00 ([1, 1, 1, 4] :: [Int]) ((\a b -> if a == b then MatchSuccess a else NoMatch "foo") :: Int -> Int -> MatchStatus Int)


qc1 = do
  quickCheck (\g v -> case (matchPattern g v) of (MatchSuccess s) -> v == matchResultToValue s; _ -> True)

qc2 = do
  quickCheck (\g v -> case (matchPattern g v) of (MatchSuccess s) -> g == matchResultToPattern s; _ -> True)


qc3 = do
  quickCheck (\v -> case (matchPattern (valueToExactGrammar v) v) of MatchSuccess _ -> True; _ -> False)

-- TH tricks (read DT)

d1 = reifyDatatype ''MatchPattern
-- TL.unpack . TL.decodeUtf8 . encode . toJ
d2 = $(ddd [''MatchPattern,
            ''MatchResult,
            ''ContextFreeGrammar,
            ''ContextFreeGrammarResult,
            ''ObjectKeyMatch
            ])

-- constantness

qc4 = do
  quickCheck (not . matchPatternIsMovable . valueToExactGrammar)

qc5 = do
  quickCheck (\v -> case valueToExactResult v of MatchSuccess s -> not $ matchResultIsMovable s; _ -> False)


c6f r = let
        p = matchResultToPattern r
        t = matchResultToThinValue r
        r0 = (fmap snd) $ thinPattern p t
        r1 = case r0 of
                  NoMatch s -> error ("NoMatch: " ++ s ++ "\n\n" ++ show p ++ "\n\n" ++ show (matchResultToValue r))
                  MatchFailure s -> error ("MatchFailure: " ++ s ++ "\n\n" ++ show p ++ "\n\n" ++ show (matchResultToValue r))
                  MatchSuccess s -> s
      in r == r1

c6c r = if matchResultIsWellFormed r then c6f r else True

qc6 = quickCheck c6c
qq = quickCheck (withMaxSuccess 10000 c6c)

-- Different matches for or example (trivial and normal)
-- p[attern] v[alue] r[esult] t[hin value]

tVIs :: MatchPattern -> Value -> Expectation
tVIs p v = 
      let r = extract $ matchPattern p v
          t' = matchResultToThinValue r
          r' = extract (fmap snd (thinPattern p t'))
      in r' `shouldBe` r

tIs :: MatchPattern -> Value -> Maybe Value -> Expectation
tIs p v t = 
      let r = extract $ matchPattern p v
          t' = matchResultToThinValue r
      in t' `shouldBe` t

test :: IO ()
test = hspec $ do
  describe "handles MatchPattern nodes correctly" $ do
    it "Handles trivial MatchOr correctly. Nothing case" $ do
      let p = (MatchOr (KM.fromList [
            (K.fromString "option1", (MatchNumberExact 1)),
            (K.fromString "option2", (MatchNumberExact 2))]))
          v = Number 1
      tVIs p v
    it "Handles trivial MatchOr correctly. Nothing case" $ do
      let p = (MatchOr (KM.fromList [
            (K.fromString "option1", (MatchNumberExact 1)),
            (K.fromString "option2", (MatchNumberExact 2))]))
          v = Number 2
      tVIs p v
    it "Handles actual MatchOr correctly. Nothing case" $ do
      let p = (MatchOr (KM.fromList [
            (K.fromString "option1", (MatchNumberExact 1)),
            (K.fromString "option2", (MatchNumberAny))]))
          v = Number 1
      tVIs p v
    it "Handles actual MatchOr correctly. Just case" $ do
      let p = (MatchOr (KM.fromList [
            (K.fromString "option1", (MatchNumberExact 1)),
            (K.fromString "option2", (MatchNumberAny))]))
          v = Number 2
      tVIs p v
    it "Handles actual MatchObjectFull correctly. Some nothing, some Just case. Some opts exist, some don't" $ do
      let p = (MatchObjectFull (KM.fromList [
            (K.fromString "a", KeyReq (MatchNumberExact 1))
            , (K.fromString "b", KeyOpt (MatchNumberExact 2))
            , (K.fromString "b1", KeyOpt (MatchNumberExact 3))
            , (K.fromString "c", KeyReq (MatchNumberAny))
            , (K.fromString "d", KeyOpt (MatchNumberAny))
            , (K.fromString "d1", KeyOpt (MatchNumberAny))
            ]))
          v = Object (KM.fromList [
            (K.fromString "a", Number 1)
            , (K.fromString "b", Number 2)
            , (K.fromString "c", Number 4)
            , (K.fromString "d", Number 5)
            ])
      tVIs p v
      --2 + 2 `shouldBe` 4
  describe "matchResultToThinValue works correctly" $ do
    it "case a a" $ do
      let p = (MatchObjectFull (KM.fromList [
            (K.fromString "a", KeyReq (MatchNumberExact 1))
            ]))
          v = Object (KM.fromList [
            (K.fromString "a", Number 1)
            ])
          t = Nothing
      tIs p v t
    it "case c" $ do
      let p = (MatchObjectFull (KM.fromList [
            (K.fromString "c", KeyReq MatchNumberAny)
            ]))
          v = Object (KM.fromList [
            (K.fromString "c", Number 1)
            ])
          t = Just $ Number 1
      tIs p v t
  describe "handles ContextFreeGrammar nodes correctly" $ do
    it "Handles trivial Optional correctly. thin value = Just" $ do
      let p = MatchArrayContextFree (Seq [(Optional (Char $ MatchNumberExact 44))])
          v = Array $ V.fromList [Number 44]
      tVIs p v
    it "Handles trivial Optional correctly. thin value = Nothing" $ do
      let p = MatchArrayContextFree (Seq [(Optional (Char $ MatchNumberExact 44))])
          v = Array $ V.fromList []
      tVIs p v
    it "Handles actual Optional correctly. thin value = Just" $ do
      let p = MatchArrayContextFree (Seq [(Optional (Char $ MatchNumberAny))])
          v = Array $ V.fromList [Number 44]
      tVIs p v
    it "Handles actual Optional correctly. thin value = Nothing" $ do
      let p = MatchArrayContextFree (Seq [(Optional (Char $ MatchNumberAny))])
          v = Array $ V.fromList []
      tVIs p v
    it "Handles trivial null Star correctly" $ do
      let p = MatchArrayContextFree (Seq [(Star (Char $ MatchNumberExact 1))])
          v = Array $ V.fromList []
      tVIs p v
    it "Handles trivial full Star correctly" $ do
      let p = MatchArrayContextFree (Seq [(Star (Char $ MatchNumberExact 1))])
          v = Array $ V.fromList [Number 1, Number 1, Number 1, Number 1]
      tVIs p v
    it "Handles actual null Star correctly" $ do
      let p = MatchArrayContextFree (Seq [(Star (Char $ MatchNumberAny))])
          v = Array $ V.fromList []
      tVIs p v
    it "Handles actual full Star correctly" $ do
      let p = MatchArrayContextFree (Seq [(Star (Char $ MatchNumberAny))])
          v = Array $ V.fromList [Number 1, Number 1, Number 1, Number 1]
      tVIs p v
    it "Handles trivial full Plus correctly" $ do
      let p = MatchArrayContextFree (Seq [(Plus (Char $ MatchNumberExact 1))])
          v = Array $ V.fromList [Number 1, Number 1, Number 1, Number 1]
      tVIs p v
    it "Handles actual full Plus correctly" $ do
      let p = MatchArrayContextFree (Seq [(Plus (Char $ MatchNumberAny))])
          v = Array $ V.fromList [Number 1, Number 1, Number 1, Number 1]
      tVIs p v

demo1 = do
  let p = (MatchObjectFull (KM.fromList [
        (K.fromString "a", KeyReq (MatchNumberExact 1))
        , (K.fromString "b", KeyOpt (MatchNumberExact 2))
        , (K.fromString "b1", KeyOpt (MatchNumberExact 3))
        , (K.fromString "c", KeyReq (MatchNumberAny))
        , (K.fromString "d", KeyOpt (MatchNumberAny))
        , (K.fromString "d1", KeyOpt (MatchNumberAny))
        ]))
      v = Object (KM.fromList [
        (K.fromString "a", Number 1)
        , (K.fromString "b", Number 2)
        , (K.fromString "c", Number 4)
        , (K.fromString "d", Number 5)
        ])
      r = extract $ matchPattern p v
      t = matchResultToThinValue r
  putStrLn $ show $ r
  putStrLn $ show $ t
  putStrLn $ show $ (extract . extract) $ thinPattern p t

w1 p v = 
      let r = extract $ matchPattern p v
          t' = matchResultToThinValue r
      in t'

--work :: 
work = do
  -- trivial, null
  let p = MatchArrayContextFree (Seq [(Star (Char $ MatchNumberExact 1))])
      v = Array $ V.fromList []
  print $ w1 p v
  -- trivial, full
  let p = MatchArrayContextFree (Seq [(Star (Char $ MatchNumberExact 1))])
      v = Array $ V.fromList [Number 1, Number 1, Number 1]
  print $ w1 p v
  -- actual, null
  let p = MatchArrayContextFree (Seq [(Star (Char $ MatchNumberAny))])
      v = Array $ V.fromList []
  print $ w1 p v
  -- actual, full
  let p = MatchArrayContextFree (Seq [(Star (Char $ MatchNumberAny))])
      v = Array $ V.fromList [Number 1, Number 1, Number 1, Number 1, Number 1]
  print $ w1 p v
  -- trivial, full
  let p = MatchArrayContextFree (Seq [(Plus (Char $ MatchNumberExact 1))])
      v = Array $ V.fromList [Number 1, Number 1, Number 1]
  print $ w1 p v
  -- actual, full
  let p = MatchArrayContextFree (Seq [(Plus (Char $ MatchNumberAny))])
      v = Array $ V.fromList [Number 1, Number 1, Number 1, Number 1]
  print $ w1 p v

valueToPythonGrammar :: Value -> MatchPattern
valueToPythonGrammar = para go
  where
    go (ObjectF a) = MatchObjectFull (fmap KeyReq a)
    go (ArrayF a) = MatchArrayContextFree $ Seq $ (fmap Char) $ V.toList a
    go (StringF a) = MatchStringExact a
    go (NumberF a) = MatchNumberExact a
    go (BoolF a) = MatchBoolExact a
    go NullF = MatchNull
