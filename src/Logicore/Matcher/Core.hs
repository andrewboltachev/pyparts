{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}


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

import Logicore.Matcher.ValueBaseFunctor
import Logicore.Matcher.Helpers

--
-- MatchStatus is a monad for representing match outcome similar to Either
--

k2s = (String . T.pack . K.toString)

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
                                  | StarNodeIndexed [(ContextFreeGrammarResult g r)] [Int]
                                  | PlusNode [(ContextFreeGrammarResult g r)]
                                  | PlusNodeIndexed [(ContextFreeGrammarResult g r)] [Int]
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
                  | MatchObjectWithDefaults (KeyMap MatchPattern) (KeyMap Value)
                  | MatchObjectOnly (KeyMap MatchPattern)
                  | MatchObjectPartial (KeyMap (ObjectKeyMatch MatchPattern))
                  -- structures - array
                  -- | MatchArrayAll MatchPattern
                  -- | MatchArraySome MatchPattern
                  -- | MatchArrayOne MatchPattern
                  -- | MatchArrayExact [MatchPattern]
                  | MatchArrayContextFree (ContextFreeGrammar MatchPattern)
                  | MatchArrayOnly MatchPattern
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
                  | MatchIgnore
                  | MatchDefault Value
                  | MatchOr (KeyMap MatchPattern)
                  | MatchIfThen MatchPattern T.Text MatchPattern
                  -- funnel
                  | MatchFunnel
                  | MatchFunnelKeys
                  | MatchFunnelKeysU
                  -- special
                  | MatchRef String
                    deriving (Generic, Eq, Show)

matchObjectWithDefaultsArbitrary = do
        m <- arbitrary
        v <- arbitrary
        let m' = fmap (bimap (K.fromString . ("m"++)) id) m
        let v' = fmap (bimap (K.fromString . ("v"++)) id) v
        return $ MatchObjectWithDefaults (fromList m') (fromList v')

instance Arbitrary MatchPattern where
  arbitrary = oneof [
      MatchObjectFull <$> arbitrary,
      matchObjectWithDefaultsArbitrary,
      MatchObjectPartial <$> arbitrary,
      MatchArrayContextFree <$> arbitrary,
      MatchArrayOnly <$> arbitrary,
      MatchStringExact <$> T.pack <$> arbitrary,
      MatchNumberExact <$> (Sci.scientific <$> arbitrary <*> arbitrary),
      MatchBoolExact <$> arbitrary,
      return $ MatchStringAny,
      return $ MatchNumberAny,
      return $ MatchBoolAny,
      return $ MatchNull,
      return $ MatchAny,
      return $ MatchIgnore,
      MatchDefault <$> arbitrary,
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
                 | MatchObjectWithDefaultsResult (KeyMap MatchResult) (KeyMap Value) (KeyMap Value)
                 | MatchArrayContextFreeResult (ContextFreeGrammarResult MatchPattern MatchResult)
                 | MatchArrayOnlyResult MatchPattern [MatchResult]
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
                 | MatchIgnoreResult Value
                 | MatchDefaultResult Value
                 | MatchOrResult (KeyMap MatchPattern) Key MatchResult
                 | MatchIfThenResult MatchPattern T.Text MatchResult
                 -- funnel
                 | MatchFunnelResult Value
                 | MatchFunnelKeysResult (KeyMap Value)
                 | MatchFunnelKeysUResult (KeyMap Value)
                 -- special
                 | MatchRefResult String MatchResult
                   deriving (Generic, Eq, Show)

matchObjectWithDefaultsResultArbitrary = do
        m <- arbitrary
        d <- arbitrary
        v <- arbitrary
        let m' = fmap (bimap (K.fromString . ("m"++)) id) m
        let d' = fmap (bimap (K.fromString . ("d"++)) id) d
        let v' = fmap (bimap (K.fromString . ("v"++)) id) v
        return $ MatchObjectWithDefaultsResult (fromList m') (fromList d') (fromList v')

instance Arbitrary MatchResult where
  arbitrary = oneof [
    MatchObjectFullResult <$> arbitrary <*> arbitrary,
    MatchObjectPartialResult <$> arbitrary <*> arbitrary,
    matchObjectWithDefaultsResultArbitrary,
    MatchArrayContextFreeResult <$> (SeqNode <$> arbitrary),
    MatchArrayOnlyResult <$> arbitrary <*> arbitrary,
    MatchStringExactResult <$> T.pack <$> arbitrary,
    MatchNumberExactResult <$> (Sci.scientific <$> arbitrary <*> arbitrary),
    MatchBoolExactResult <$> arbitrary,
    MatchStringAnyResult <$> T.pack <$> arbitrary,
    MatchNumberAnyResult <$> (Sci.scientific <$> arbitrary <*> arbitrary),
    MatchBoolAnyResult <$> arbitrary,
    return $ MatchNullResult,
    MatchAnyResult <$> arbitrary,
    MatchIgnoreResult <$> arbitrary,
    MatchDefaultResult <$> arbitrary,
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

gatherFunnelContextFree :: ContextFreeGrammarResult MatchPattern [a] -> [a]
gatherFunnelContextFree = cata go
  where
    go (CharNodeF r) = r
    go (SeqNodeF r) = L.foldl' (++) mempty r
    go (StarNodeEmptyF g) = []
    go (StarNodeValueF r) = L.foldl' (++) mempty r
    go (PlusNodeF r) = L.foldl' (++) mempty r
    go (OrNodeF g k r) = r
    go (OptionalNodeValueF r) = r
    go (OptionalNodeEmptyF g) = []

unique = P.reverse . L.nub . P.reverse

gatherFunnel :: MatchResult -> [Value] -- TODO Monoid?
gatherFunnel = cata go
  where
    go (MatchObjectFullResultF _ r) = L.foldl' f mempty (KM.elems r)
      where f acc (KeyReq e) = acc ++ e
            f acc (KeyOpt e) = acc ++ e
            f acc (KeyExt _) = acc
    go (MatchObjectPartialResultF _ r) = L.foldl' f mempty (KM.elems r)
      where f acc (KeyReq e) = acc ++ e
            f acc (KeyOpt e) = acc ++ e
            f acc (KeyExt _) = acc
    go (MatchObjectWithDefaultsResultF r _ _) = L.foldl' (++) mempty (KM.elems r)
    go (MatchArrayContextFreeResultF c) = gatherFunnelContextFree c
    go (MatchArrayOnlyResultF g r) = L.foldl' (++) mempty r
    go (MatchOrResultF g k r) = r
    go (MatchIfThenResultF _ _ r) = r
    go (MatchFunnelResultF r) = [r]
    go (MatchFunnelKeysResultF m) = fmap k2s (KM.keys m)
    go (MatchFunnelKeysUResultF m) = unique $ fmap k2s (KM.keys m) -- TODO what idea?
    go _ = []

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
                               False -> NoMatch $ ("extra key in arg: " ++ show k)
                               True -> case KM.lookup k a of
                                            Nothing -> MatchFailure "impossible"
                                            Just v -> MatchSuccess $ second (KM.insert k (KeyExt v)) acc

matchPattern (MatchObjectFull m) (Object a) = (fmap $ uncurry MatchObjectFullResult) (mObj False m a)
matchPattern (MatchObjectOnly m) (Object a) = (fmap $ uncurry MatchObjectFullResult) (mObj False (fmap KeyReq m) (KM.filterWithKey (\k v -> KM.member k m) a))
matchPattern (MatchObjectPartial m) (Object a) = (fmap $ uncurry MatchObjectPartialResult) (mObj True m a)


matchPattern (MatchObjectWithDefaults m d) (Object a) = do
  let f acc' (k, v) = do
          acc <- acc' -- (mm, dd)
          if KM.member k m
            then
                do
                  m' <- (m2ms $ MatchFailure "impossible") $ KM.lookup k m
                  rr <- matchPattern m' v
                  return $ first (KM.insert k rr) acc
            else
              if KM.member k d
                then
                  do
                    d' <- (m2ms $ MatchFailure "impossible") $ KM.lookup k d
                    let ff = if v /= d'
                              then KM.insert k v
                              else id
                    return $ second ff acc
                else NoMatch $ "extra key: " ++ show k
  (mm, vv) <- L.foldl' f (MatchSuccess mempty) $ KM.toList a
  return $ MatchObjectWithDefaultsResult mm d vv


matchPattern (MatchArrayContextFree m) (Array a) = do
  case contextFreeMatch m (V.toList a) matchPattern of
       NoMatch e -> NoMatch ("context-free nomatch: " ++ e)
       MatchFailure s -> MatchFailure s
       MatchSuccess x -> MatchSuccess (MatchArrayContextFreeResult x)

matchPattern (MatchArrayContextFree m) (Object a) = NoMatch ("object in cf:\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode $ m) ++ "\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode $ toJSON $ a))

matchPattern (MatchArrayOnly m) (Array a) = do
  let f acc' e = do
        acc <- acc'
        case matchPattern m e of
             MatchSuccess s -> MatchSuccess $ acc ++ [s]
             MatchFailure e -> MatchFailure e
             NoMatch e -> MatchSuccess $ acc
  r <- L.foldl' f (MatchSuccess []) (V.toList a)
  return $ MatchArrayOnlyResult m r

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
matchPattern MatchIgnore a = MatchSuccess $ MatchIgnoreResult a
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
    go (StarNodeIndexedF r _) = P.concat r
    go (PlusNodeF r) = P.concat r
    go (PlusNodeIndexedF r _) = P.concat r
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
  go (MatchObjectWithDefaultsResultF r d v) = MatchObjectWithDefaults r d
  go (MatchArrayContextFreeResultF r) = MatchArrayContextFree $ contextFreeGrammarResultToGrammar id r
  go (MatchArrayOnlyResultF g r) = g
  go (MatchStringExactResultF r) = MatchStringExact r
  go (MatchNumberExactResultF r) = MatchNumberExact r
  go (MatchBoolExactResultF r) = MatchBoolExact r
  go (MatchStringAnyResultF r) = MatchStringAny
  go (MatchNumberAnyResultF r) = MatchNumberAny
  go (MatchBoolAnyResultF r) = MatchBoolAny
  go MatchNullResultF = MatchNull
  go (MatchAnyResultF r) = MatchAny
  go (MatchIgnoreResultF r) = MatchIgnore
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
    go (MatchObjectWithDefaultsResultF r d v) = Object $ KM.union r $ KM.union v d
    go (MatchArrayContextFreeResultF r) = Array $ V.fromList $ contextFreeGrammarResultToSource id r
    go (MatchArrayOnlyResultF g r) = Array $ V.fromList $ r
    go (MatchStringExactResultF r) = String r
    go (MatchNumberExactResultF r) = Number r
    go (MatchBoolExactResultF r) = Bool r
    go (MatchStringAnyResultF r) = String r
    go (MatchNumberAnyResultF r) = Number r
    go (MatchBoolAnyResultF r) = Bool r
    go MatchNullResultF = Null
    go (MatchAnyResultF r) = r
    go (MatchIgnoreResultF r) = r
    go (MatchOrResultF m k r) = r
    go (MatchIfThenResultF p errorMsg r) = r
    go (MatchFunnelResultF r) = r
    go (MatchFunnelKeysResultF r) = Object r
    go (MatchFunnelKeysUResultF r) = Object r
    go (MatchRefResultF ref r) = r

valueToExactGrammar :: Value -> MatchPattern
valueToExactGrammar = cata go
  where
    go (ObjectF a) = MatchObjectWithDefaults a mempty
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
    go (MatchArrayOnlyF g) = g
    go (MatchStringExactF _) = True
    go (MatchNumberExactF _) = True
    go (MatchBoolExactF _) = True
    go MatchStringAnyF = True
    go MatchNumberAnyF = True
    go MatchBoolAnyF = True
    go MatchNullF = True
    go MatchAnyF = True
    go MatchIgnoreF = True
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
    check (MatchArrayOnlyResultF g r) = matchPatternIsWellFormed g
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
    check (MatchIgnoreResultF _) = True
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
    go (MatchObjectWithDefaultsF g _) = getAny $ mconcat $ P.map Any (KM.elems g)
    go (MatchObjectPartialF g) = True -- may have ext --P.any (extractObjectKeyMatch $ error "must not be here") (KM.elems g)
    go (MatchArrayContextFreeF g) = contextFreeGrammarIsMovable id g
    go (MatchArrayOnlyF g) = True
    go (MatchStringExactF _) = False
    go (MatchNumberExactF _) = False
    go (MatchBoolExactF _) = False
    go MatchStringAnyF = True
    go MatchNumberAnyF = True
    go MatchBoolAnyF = True
    go MatchNullF = False
    go MatchAnyF = True
    go MatchIgnoreF = False
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
    check (MatchArrayOnlyResultF g r) = True
    check (MatchStringExactResultF _) = False
    check (MatchNumberExactResultF _) = False
    check (MatchBoolExactResultF _) = False
    check (MatchStringAnyResultF _) = True
    check (MatchNumberAnyResultF _) = True
    check (MatchBoolAnyResultF _) = True
    check MatchNullResultF = False
    check (MatchAnyResultF _) = True
    check (MatchIgnoreResultF _) = False
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

tMapK1 k = Object $ KM.fromList [(K.fromString "k", k2s k)]
tMapKV1 k v = Object $ KM.fromList [(K.fromString "k", k2s k), (K.fromString "v", v)]

int2sci :: Integral a => a -> Value
int2sci x = Number $ Sci.scientific (toInteger x) 0

enumerate :: [Value] -> [Value]
enumerate a = fmap (\(i, a) -> Array $ V.fromList [int2sci i, a]) $ P.zip [1..] a

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
                 else Just $ Array $ V.fromList $ l
    go (StarNodeEmptyF g) = Just $ if gg g
                                      then Array $ V.fromList ([] :: [Value])
                                      else Number 0
    go (StarNodeValueF r) = Just $ if P.head r == Nothing -- aka grammar is trivial
                               then int2sci (P.length r)
                               else Array $ V.fromList $ enumerate $ P.map fromJust r
    go (PlusNodeF r) = Just $ if P.head r == Nothing -- aka grammar is trivial
                               then int2sci (P.length r)
                               else Array $ V.fromList $ enumerate $ P.map fromJust r
    go (OrNodeF g k r) = Just $ if r == Nothing
                            then tMapK1 k
                            else tMapKV1 k (fromJust r)
    go (OptionalNodeValueF r) = Just $ if r == Nothing
                            then Bool True
                            else Array $ V.fromList [(fromJust r)]
    go (OptionalNodeEmptyF g) = Just $ if not $ gg g
                            then Bool False
                            else Array $ V.fromList []


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
                            Just a -> Just $ a
        f (KeyExt _) = error "must not be here5"
        ff (KeyReq v) = True
        ff (KeyOpt v) = True
        ff (KeyExt v) = False
        optf :: MatchPattern -> Maybe Value
        optf x = case matchPatternIsMovable x of
                      True -> Just $ Bool True
                      False -> Just $ Bool False
        u = KM.union (KM.map f (KM.filter ff r)) (fmap optf g)
    go (MatchObjectWithDefaultsResultF r d a) = go (MatchObjectFullResultF (KM.empty) (fmap KeyReq r))
    go (MatchArrayContextFreeResultF r) = contextFreeGrammarResultToThinValue r
    go (MatchArrayOnlyResultF g r) = Just $ (Array . V.fromList) $ catMaybes r
    go (MatchStringExactResultF r) = Nothing
    go (MatchNumberExactResultF r) = Nothing
    go (MatchBoolExactResultF r) = Nothing
    go (MatchStringAnyResultF r) = Just $ String r
    go (MatchNumberAnyResultF r) = Just $ Number r
    go (MatchBoolAnyResultF r) = Just $ Bool r
    go MatchNullResultF = Nothing
    go (MatchAnyResultF r) = Just $ r
    go (MatchIgnoreResultF r) = Nothing
    go (MatchOrResultF g k r) = Just $ if r == Nothing
                                   then tMapK1 k
                                   else tMapKV1 k (fromJust r)
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
                      (m2ms $ MatchFailure $ "data error10" ++ show v) $ asArray v
        let f acc' (a, gg) = do
                acc <- acc'
                (ii, acc) <- acc'
                let (i:is) = ii
                if gg -- movable
                  then fmap (\x -> (is, acc ++ [x])) (thinContextFreeMatch a (Just i))
                  else fmap (\x -> (ii, acc ++ [x])) (thinContextFreeMatch a Nothing)

        r <- L.foldl' f (MatchSuccess (v, [])) $ P.zip as gs
        _ <- if P.null $ fst r then MatchSuccess () else MatchFailure $ "not all consumed" ++ show (fst r)
        return $ SeqNode (snd r)

throwAwayIndexes :: MatchStatus [Value] -> Value -> MatchStatus [Value]
throwAwayIndexes err (Array a') = do
  a <- return $ V.toList a'
  let f acc' x = do
        acc <- acc'
        x' <- (m2ms err) $ asArray x
        -- array of pairs
        _ <- if P.length x' == 2 then MatchSuccess mempty else err
        return $ acc ++ [P.head $ P.tail $ x']
  L.foldl' f (MatchSuccess mempty) a
throwAwayIndexes err _ = err

getIndexes :: a -> Value -> MatchStatus [Int]
getIndexes _ (Array a') = do
  a <- return $ V.toList a'
  let f acc' x = do
        acc <- acc'
        x' <- (m2ms (MatchFailure "index problem")) $ asArray x
        -- array of pairs
        _ <- if P.length x' == 2 then MatchSuccess ([] :: [Int]) else (MatchFailure "index problem")
        let i' :: Value
            i' = P.head $ x'
        i <- (m2ms $ (MatchFailure "index problem")) $ asNumber i'
        return $ acc ++ [fromInteger $ Sci.coefficient i]
  L.foldl' f (MatchSuccess mempty) a
getIndexes _ _ = (MatchFailure "index problem")

thinContextFreeMatch :: ContextFreeGrammar MatchPattern -> Maybe Value -> MatchStatus (ContextFreeGrammarResult MatchPattern MatchResult)
thinContextFreeMatch (Char a) v = do
  case thinPattern a v of
       NoMatch s -> NoMatch ("no char match: " ++ s)
       MatchFailure s -> MatchFailure ("thinContextFreeMatch: " ++ s)
       MatchSuccess r -> MatchSuccess $ CharNode r

thinContextFreeMatch (Seq as) Nothing = if not $ contextFreeGrammarIsMovable matchPatternIsMovable (Seq as)
                                           then thinSeq as (Array $ V.fromList [])
                                           else NoMatch "data error5"
thinContextFreeMatch (Seq as) (Just v) = do
  if not $ contextFreeGrammarIsMovable matchPatternIsMovable (Seq as)
     then NoMatch ("data error6:\n\n" ++ show as ++ "\n\n" ++ show v ++ "\n\n")
     else thinSeq as v

thinContextFreeMatch (Or ms) (Just (Object v)) = do -- or requires an exsistance of a value (Just)
  itsKey <- (m2ms $ MatchFailure ("data error 951: " ++ show v)) $ KM.lookup (K.fromString "k") v
  itsKey <- (m2ms $ MatchFailure ("data error3" ++ show itsKey)) $ asString itsKey
  let itsK = (K.fromString . T.unpack) itsKey
  itsMatch <- (m2ms $ MatchFailure ("data error4" ++ show ms)) $ KM.lookup itsK ms
  mch <- thinContextFreeMatch itsMatch (KM.lookup (K.fromString "v") v)
  return $ OrNode (KM.delete itsK ms) itsK mch

thinContextFreeMatch (Star a) (Just itsValue) = do
  let gg = contextFreeGrammarIsMovable matchPatternIsMovable
  if gg a
     then -- actual
        do
          is <- (getIndexes $ MatchFailure ("data error2" ++ show itsValue)) $ itsValue
          itsValue <- (throwAwayIndexes $ MatchFailure ("data error2" ++ show itsValue)) $ itsValue
          if P.null itsValue
             then
                return $ StarNodeEmpty a
             else
              do
                aa <- P.traverse (thinContextFreeMatch a) (fmap Just itsValue)
                return $ StarNodeIndexed aa is
      else -- trivial
        do
          itsValue <- (m2ms $ MatchFailure ("data error2" ++ show itsValue)) $ asNumber itsValue
          if itsValue == 0
             then
                return $ StarNodeEmpty $ a
              else
                do
                  aa' <- thinContextFreeMatch a Nothing
                  let aa = P.take (fromIntegral $ Sci.coefficient itsValue) $ P.repeat aa'
                  return $ StarNodeValue aa

thinContextFreeMatch (Plus a) (Just itsValue) = do
  let gg = contextFreeGrammarIsMovable matchPatternIsMovable
  if gg a
     then -- actual
        do
          is <- (getIndexes $ MatchFailure ("data error2" ++ show itsValue)) $ itsValue
          itsValue <- (throwAwayIndexes $ MatchFailure ("data error3" ++ show itsValue)) $ itsValue
          aa <- P.traverse (thinContextFreeMatch a) (fmap Just itsValue)
          return $ PlusNodeIndexed aa is
      else -- trivial
        do
          itsValue <- (m2ms $ MatchFailure ("data error4" ++ show itsValue)) $ asNumber itsValue
          aa' <- thinContextFreeMatch a Nothing
          let aa = P.take (fromIntegral $ Sci.coefficient itsValue) $ P.repeat aa'
          return $ PlusNode aa

thinContextFreeMatch (Optional a) (Just itsValue) = do
  let gg = contextFreeGrammarIsMovable matchPatternIsMovable
  if gg a
     then
      do
        itsValue <- (m2ms $ MatchFailure ("data error1141" ++ show itsValue)) $ asArray itsValue
        if not (P.null itsValue)
           then
            do
              r <- thinContextFreeMatch a (Just (P.head itsValue))
              return $ OptionalNodeValue r
           else return $ OptionalNodeEmpty a
     else
      do
        itsValue <- (m2ms $ MatchFailure ("data error1144" ++ show itsValue)) $ asBool itsValue
        if itsValue
           then
            do
              r <- thinContextFreeMatch a Nothing
              return $ OptionalNodeValue r
           else return $ OptionalNodeEmpty a

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
                      Just n -> case thinPattern r (Just n) of
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
                                         e <- thinPattern v Nothing
                                         return $ second (KM.insert k $ KeyReq e) acc
                                       Just x -> MatchFailure ("must not be here 1089: " ++ show x)
             (KeyOpt v, False) -> do
               vv <- (m2ms $ MatchFailure ("doesn't exist1" ++ show na)) $ KM.lookup k na
               flg <- (m2ms $ MatchFailure ("doesn't exist5" ++ show vv)) $ asBool vv
               case flg of
                    False -> return $ first (KM.insert k v) acc
                    True -> do
                      e <- thinPattern v Nothing
                      return $ second (KM.insert k $ KeyOpt e) acc
             -- movable
             (KeyReq v, True) -> do
               case KM.lookup k na of
                    Nothing -> NoMatch ("Key not found: " ++ show k)
                    Just x -> do
                      e <- thinPattern v (Just x)
                      return $ second (KM.insert k $ KeyReq e) acc
             (KeyOpt v, True) -> do
               case KM.lookup k na of
                    Nothing -> return $ first (KM.insert k v) acc
                    Just x -> do
                      e <- thinPattern v (Just x)
                      return $ second (KM.insert k $ KeyOpt e) acc
             -- error
             (KeyExt v, _) -> MatchFailure ("must not be here" ++ show v)

  (os, xs) <- L.foldl' f (MatchSuccess mempty) (KM.keys m)
  let rst = KM.filterWithKey (\kk _ -> not $ KM.member kk m) na
  xs <- if allowExt && (not $ KM.null rst)
          then NoMatch "might not have extra"
          else return $ KM.union xs $ (KM.map KeyExt) rst

  let c = if allowExt then MatchObjectPartialResult else MatchObjectFullResult
  return $ c os xs

extractKeyReq (KeyReq a) = a
getReqs a = (KM.map extractKeyReq (KM.filter isKeyReq a))

thinPattern :: MatchPattern -> Maybe Value -> MatchStatus MatchResult
thinPattern (MatchObjectFull m) a = thinPatternMap False m a
thinPattern (MatchObjectPartial m) a = thinPatternMap True m a
thinPattern (MatchObjectWithDefaults m d) a = do
  let mm = KM.map KeyReq m
  r <- thinPattern (MatchObjectFull mm) a
  rr <- case r of
             (MatchObjectFullResult _ e) -> return $ e
             _ -> MatchFailure "should be impossible"
  return $ MatchObjectWithDefaultsResult (getReqs rr) d (KM.empty)


thinPattern (MatchArrayContextFree m) a = do
  case thinContextFreeMatch m a of
       NoMatch e -> NoMatch ("context-free nomatch: " ++ e)
       MatchFailure s -> MatchFailure s
       MatchSuccess x -> MatchSuccess $ MatchArrayContextFreeResult x

thinPattern (MatchArrayOnly m) a = error $ "Not implemented"

thinPattern MatchFunnel (Just v) = MatchSuccess $ MatchFunnelResult v

thinPattern MatchFunnelKeys (Just (Object v)) = MatchSuccess $ MatchFunnelKeysResult v
thinPattern MatchFunnelKeys _ = MatchFailure "MatchFunnelKeys met not an Object or met Nothing"

thinPattern MatchFunnelKeysU (Just (Object v)) = MatchSuccess $ MatchFunnelKeysUResult v
thinPattern MatchFunnelKeysU _ = MatchFailure "MatchFunnelKeysU met not an Object or met Nothing"

thinPattern (MatchIfThen baseMatch failMsg match) v =
  case thinPattern baseMatch v of
       NoMatch x -> NoMatch x
       MatchFailure f -> MatchFailure f
       MatchSuccess _ -> case thinPattern match v of
                            NoMatch x -> MatchFailure ((T.unpack failMsg) ++ show x)
                            MatchFailure f -> MatchFailure f
                            MatchSuccess s -> MatchSuccess $ MatchIfThenResult baseMatch failMsg s

thinPattern MatchAny (Just a) = MatchSuccess $ MatchAnyResult a
thinPattern MatchIgnore (Just a) = MatchFailure "thinPattern over Ignore"

thinPattern (MatchOr ms) (Just (Object v)) = do
  itsK <- (m2ms $ MatchFailure $ "data error117" ++ show v) $ (KM.lookup "k") v
  itsK <- (m2ms $ MatchFailure $ "data error117" ++ show v) $ asString itsK
  itsK <- return $ K.fromString $ T.unpack $ itsK
  let itsV = KM.lookup "v" v
  aa <- (m2ms $ NoMatch $ "Wrong k" ++ show itsK) $ (KM.lookup itsK) ms
  r <- thinPattern aa itsV
  rr <- return $ MatchOrResult (KM.delete itsK ms) itsK r
  return $ rr

-- specific (aka exact)
thinPattern (MatchStringExact m) Nothing = MatchSuccess $ MatchStringExactResult m
thinPattern (MatchNumberExact m) Nothing = MatchSuccess $ MatchNumberExactResult m
thinPattern (MatchBoolExact m) Nothing = MatchSuccess $ MatchBoolExactResult m
-- any (of a type)
thinPattern MatchStringAny (Just (String a)) = MatchSuccess $ MatchStringAnyResult a
thinPattern MatchNumberAny (Just (Number a)) = MatchSuccess $ MatchNumberAnyResult a
thinPattern MatchBoolAny (Just (Bool a)) = MatchSuccess $ MatchBoolAnyResult a
-- null is just null
thinPattern MatchNull Nothing = MatchSuccess $ MatchNullResult
-- default ca
thinPattern m a = NoMatch ("thinPattern bottom reached:\n" ++ show m ++ "\n" ++ show a)

-- thin pattern R
{-
thinPatternR (MatchObjectFullResult _ _) = error "not implemented"
thinPatternR (MatchObjectPartialResult _ _) = error "not implemented"
--thinPatternR (MatchObjectWithDefaultsResult r d o) = L.foldl' f (MatchStatus mempty) r-}

safeGet :: [a] -> Int -> Maybe a
safeGet xs n
  | n < 0     = Nothing
             -- Definition adapted from GHC.List
  | otherwise = P.foldr (\x r k -> case k of
                                   0 -> Just x
                                   _ -> r (k-1)) (const Nothing) xs n

applyOriginalValueDefaultsCF :: ContextFreeGrammarResult MatchPattern MatchResult -> Maybe (ContextFreeGrammarResult MatchPattern MatchResult) -> ContextFreeGrammarResult MatchPattern MatchResult

applyOriginalValueDefaultsCF (CharNode x) (Just (CharNode x')) = CharNode $ applyOriginalValueDefaults x (Just x')
applyOriginalValueDefaultsCF (SeqNode x) (Just (SeqNode x')) = SeqNode $ P.map (\(e, e') -> applyOriginalValueDefaultsCF e (Just e')) $ P.zip x x'
-- Or
-- Star
-- Plus
-- Optional
applyOriginalValueDefaultsCF o@(OrNode ms k m) (Just (OrNode ms' k' m')) = l
  where
    l = if k == k' then OrNode ms k (applyOriginalValueDefaultsCF m (Just m'))
                   else o
applyOriginalValueDefaultsCF o@(StarNodeIndexed m is) (Just (StarNodeValue m')) = l
  where
    l = StarNodeValue $ P.map (\(e, i) -> applyOriginalValueDefaultsCF e (safeGet m' (i - 1))) $ P.zip m is

applyOriginalValueDefaultsCF o@(StarNodeValue m) (Just (StarNodeValue m')) = l
  where
    l = StarNodeValue $ P.map (\(e, i) -> applyOriginalValueDefaultsCF e (safeGet m' (i - 1))) $ P.zip m [1..]

applyOriginalValueDefaultsCF o@(PlusNodeIndexed m is) (Just (PlusNode m')) = l
  where
    l = PlusNode $ P.map (\(e, i) -> applyOriginalValueDefaultsCF e (safeGet m' (i - 1))) $ P.zip m is

applyOriginalValueDefaultsCF o@(PlusNode m) (Just (PlusNode m')) = l
  where
    l = PlusNode $ P.map (\(e, i) -> applyOriginalValueDefaultsCF e (safeGet m' (i - 1))) $ P.zip m [1..]

applyOriginalValueDefaultsCF (OptionalNodeValue m) (Just (OptionalNodeValue m')) = l
  where
    l = OptionalNodeValue (applyOriginalValueDefaultsCF m (Just m'))
applyOriginalValueDefaultsCF x _ = x

applyOriginalValueDefaults :: MatchResult -> Maybe MatchResult -> MatchResult
applyOriginalValueDefaults (MatchObjectWithDefaultsResult m d _) (Just (MatchObjectWithDefaultsResult m' _ a)) = l --error $ show (m, m', d, a)
  where
    m'' = KM.mapMaybeWithKey (\k e -> Just $ applyOriginalValueDefaults e (KM.lookup k m')) m'
    l = MatchObjectWithDefaultsResult m'' d a
applyOriginalValueDefaults (MatchArrayContextFreeResult m) (Just (MatchArrayContextFreeResult m')) = l
  where
    l = MatchArrayContextFreeResult (applyOriginalValueDefaultsCF m (Just m'))
applyOriginalValueDefaults o@(MatchOrResult ms k m) (Just (MatchOrResult ms' k' m')) = l
  where
    l = if k == k' then MatchOrResult ms k (applyOriginalValueDefaults m (Just m'))
                   else o
applyOriginalValueDefaults (MatchIfThenResult b e m) (Just (MatchOrResult b' e' m')) = l
  where
    l = MatchIfThenResult b e (applyOriginalValueDefaults m (Just m'))
applyOriginalValueDefaults x _ = x

-- The most useful
-- Value -> MatchPattern -> MatchResult
-- MatchResult -> Thin Value
-- Thin Value, MatchPattern -> 
-- Thin Value, Original MatchResult -> 
thinPatternWithDefaults :: MatchResult -> Maybe Value -> MatchStatus MatchResult
thinPatternWithDefaults r v = do
  let p = matchResultToPattern r
  vr <- thinPattern p v
  return $ applyOriginalValueDefaults vr (Just r)

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
        r0 = thinPattern p t
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
          r' = extract $ thinPattern p t'
      in r' `shouldBe` r

tIs :: MatchPattern -> Value -> Maybe Value -> Expectation
tIs p v t = 
      let r = extract $ matchPattern p v
          t' = matchResultToThinValue r
      in t' `shouldBe` t

test :: IO ()
test = hspec $ do
  describe "MatchObjectWithDefaults matchPattern works correctly" $ do
    it "handles correctly the empty case" $ do
      let r = matchPattern (MatchObjectWithDefaults (fromList []) (fromList [])) (Object (fromList []))
      r `shouldBe` MatchSuccess (MatchObjectWithDefaultsResult (fromList []) (fromList []) (fromList []))

    it "handles correctly the case with default value" $ do
      let r = matchPattern (MatchObjectWithDefaults (fromList [("a", MatchNumberAny)]) (fromList [("w", String " ")])) (Object (fromList [("a", Number 1), ("w", String $ " ")]))
      r `shouldBe` MatchSuccess (MatchObjectWithDefaultsResult (fromList [("a",MatchNumberAnyResult 1.0)]) (fromList [("w", String " ")]) (fromList []))

    it "handles correctly the case with different value" $ do
      let r = matchPattern (MatchObjectWithDefaults (fromList [("a", MatchNumberAny)]) (fromList [("w", String " ")])) (Object (fromList [("a", Number 1), ("w", String $ "   ")]))
      r `shouldBe` MatchSuccess (MatchObjectWithDefaultsResult (fromList [("a",MatchNumberAnyResult 1.0)]) (fromList [("w",String " ")]) (fromList [("w",String "   ")]))

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
  putStrLn $ show $ extract $ thinPattern p t

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

-- the thin case
thinWithDefaults1 = do
  let v = Array [
            (Object (fromList [("type", String "Node"), ("value", Number 10), ("ws", String " ")])),
            (Object (fromList [("type", String "Node"), ("value", Number 20), ("ws", String "  ")])),
            (Object (fromList [("type", String "Node"), ("value", Number 30), ("ws", String "   ")]))]
  let p = MatchArrayContextFree $ Seq [Star $ Char $ MatchObjectWithDefaults (fromList [("type", MatchStringExact "Node"), ("value", MatchNumberAny)]) (fromList [("ws", String " ")])]
  r <- matchPattern p v
  let t = Just (Array [Array [Number 1.0,Number 10.0],Array [Number 2.0,Number 20.0],Array [Number 0,Number 50.0],Array [Number 3.0,Number 30.0]])
  --return $ thinPattern p t
  r' <- thinPatternWithDefaults r t
  return $ matchResultToValue r'

thinWithDefaults2 = do
  let v = Array [
            (Object (fromList [("type", String "Node"), ("value", Number 10), ("ws", String " ")])),
            (Object (fromList [("type", String "Node"), ("value", Number 10), ("ws", String "  ")])),
            (Object (fromList [("type", String "Node"), ("value", Number 10), ("ws", String "   ")]))]
  let p = MatchArrayContextFree $ Seq [Star $ Char $ MatchObjectWithDefaults (fromList [("type", MatchStringExact "Node"), ("value", MatchNumberExact 10.0)]) (fromList [("ws", String " ")])]
  r <- matchPattern p v
  --return $ matchResultToThinValue r
  let t = Just $ Number 5.0
  r' <- thinPatternWithDefaults r t
  return $ matchResultToValue r'
