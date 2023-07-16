{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE FlexibleContexts #-}


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
import Control.Monad ((>=>), liftM)
import Control.Comonad
--import qualified Data.ByteString.UTF8       as BLU
--import Logicore.Matcher.Utils
import Data.Fix (Fix (..), unFix, Mu (..), Nu (..))
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

--cata :: Recursive t => (Base t c -> c) -> t -> c
cataM :: (Traversable (Base t), Monad m, Recursive t) => (Base t c -> m c) -> t -> m c
cataM f c = cata (sequence >=> f) c
{-cataM f x = c x
  where c x = do
          let a1 = (fmap c . project) x
          a2 <- sequence a1
          f a2-}

--para :: Recursive t => (Base t (t, c) -> c) -> t -> c
paraM :: (Traversable (Base t), Monad m, Recursive t) => (Base t (t, c) -> m c) -> t -> m c
{-paraM f x = c x
  where c x = do
          let a0 = project x
          let g (a, mc) = do
              c' <- mc
              return (a, c')
          let a1 = fmap (sequence . ((,) <*> c)) a0
          a2 <- sequence a1
          f a2-}
paraM f = c where c = (sequence >=> f) . fmap (sequence . ((,) <*> c)) . project

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
                  | MatchArrayOr (KeyMap MatchPattern)
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
                 | MatchObjectOnlyResult (KeyMap MatchResult) (KeyMap Value)
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
        let m' = fmap (first (K.fromString . ("m"++))) m
        let d' = fmap (first (K.fromString . ("d"++))) d
        let v' = fmap (first (K.fromString . ("v"++))) v
        return $ MatchObjectWithDefaultsResult (fromList m') (fromList d') (fromList v')

matchObjectOnlyResultArbitrary = do
        m <- arbitrary
        d <- arbitrary
        let m' = fmap (first (K.fromString . ("m"++))) m
        let d' = fmap (first (K.fromString . ("d"++))) d
        return $ MatchObjectOnlyResult (fromList m') (fromList d')

instance Arbitrary MatchResult where
  arbitrary = oneof [
    MatchObjectFullResult <$> arbitrary <*> arbitrary,
    MatchObjectPartialResult <$> arbitrary <*> arbitrary,
    matchObjectWithDefaultsResultArbitrary,
    matchObjectOnlyResultArbitrary,
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
    go (MatchObjectOnlyResultF r _) = L.foldl' (++) mempty (KM.elems r)
    go (MatchArrayContextFreeResultF c) = gatherFunnelContextFree c
    go (MatchArrayOnlyResultF g r) = L.foldl' (++) mempty r
    go (MatchOrResultF g k r) = r
    go (MatchIfThenResultF _ _ r) = r
    go (MatchFunnelResultF r) = [r]
    go (MatchFunnelKeysResultF m) = fmap k2s (KM.keys m)
    go (MatchFunnelKeysUResultF m) = unique $ fmap k2s (KM.keys m) -- TODO what idea?
    go (MatchRefResultF ref r) = r
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
matchPattern :: (KeyMap MatchPattern) -> MatchPattern -> Value -> MatchStatus MatchResult

mObj :: (KeyMap MatchPattern) -> Bool -> KeyMap (ObjectKeyMatch MatchPattern) -> Object -> MatchStatus (KeyMap MatchPattern, KeyMap (ObjectKeyMatch MatchResult))
mObj g keepExt m a = do
  preResult <- L.foldl' (doKeyMatch m a) (MatchSuccess mempty) (keys m)
  L.foldl' f (MatchSuccess preResult) (keys a)
    where
      step k r acc req = case KM.lookup k a of
                      -- KeyOpt means key might be missing
                      Nothing -> if req
                                      then NoMatch $ "Required key " ++ show k ++ " not found in map"
                                      else MatchSuccess $ first (KM.insert k r) acc
                      -- if it exists, it must match
                      Just n -> case matchPattern g r n of
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

matchPattern g (MatchObjectFull m) (Object a) = (fmap $ uncurry MatchObjectFullResult) (mObj g False m a)
--matchPattern (MatchObjectOnly m) (Object a) = (fmap $ uncurry MatchObjectFullResult) (mObj g False (fmap KeyReq m) (KM.filterWithKey (\k v -> KM.member k m) a))
matchPattern g (MatchObjectPartial m) (Object a) = (fmap $ uncurry MatchObjectPartialResult) (mObj g True m a)


matchPattern g (MatchObjectWithDefaults m d) (Object a) = do
  let f acc' (k, v) = do
          acc <- acc' -- (mm, dd)
          if KM.member k m
            then
                do
                  m' <- (m2ms $ MatchFailure "impossible") $ KM.lookup k m
                  rr <- matchPattern g m' v
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


matchPattern g (MatchObjectOnly m) (Object a) = do
  let f acc' (k, v) = do
          acc <- acc' -- (mm, dd)
          if KM.member k m
            then
                do
                  m' <- (m2ms $ MatchFailure "impossible") $ KM.lookup k m
                  rr <- matchPattern g m' v
                  return $ first (KM.insert k rr) acc
            else
              return $ second (KM.insert k v) acc
  (mm, vv) <- L.foldl' f (MatchSuccess mempty) $ KM.toList a
  return $ MatchObjectOnlyResult mm vv


matchPattern g (MatchArrayContextFree m) (Array a) = do
  case contextFreeMatch m (V.toList a) (matchPattern g) of
       NoMatch e -> NoMatch ("context-free nomatch: " ++ e)
       MatchFailure s -> MatchFailure s
       MatchSuccess x -> MatchSuccess (MatchArrayContextFreeResult x)

matchPattern g (MatchArrayContextFree m) (Object a) = NoMatch ("object in cf:\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode $ m) ++ "\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode $ toJSON $ a))

matchPattern g (MatchArrayOnly m) (Array a) = do
  let f acc' e = do
        acc <- acc'
        case matchPattern g m e of
             MatchSuccess s -> MatchSuccess $ acc ++ [s]
             MatchFailure e -> MatchFailure e
             NoMatch e -> MatchSuccess $ acc
  r <- L.foldl' f (MatchSuccess []) (V.toList a)
  return $ MatchArrayOnlyResult m r

matchPattern g MatchFunnel v = MatchSuccess $ MatchFunnelResult v

matchPattern g MatchFunnelKeys (Object v) = MatchSuccess $ MatchFunnelKeysResult $ v
matchPattern g MatchFunnelKeys _ = MatchFailure "MatchFunnelKeys met not an Object"

matchPattern g MatchFunnelKeysU (Object v) = MatchSuccess $ MatchFunnelKeysUResult $ v
matchPattern g MatchFunnelKeysU _ = MatchFailure "MatchFunnelKeysU met not an Object"

matchPattern g (MatchIfThen baseMatch failMsg match) v =
  case matchPattern g baseMatch v of
       NoMatch x -> NoMatch x
       MatchFailure f -> MatchFailure f
       MatchSuccess _ -> case matchPattern g match v of
                            NoMatch x -> MatchFailure ((T.unpack failMsg) ++ show x)
                            MatchFailure f -> MatchFailure f
                            MatchSuccess s -> MatchSuccess (MatchIfThenResult baseMatch failMsg s)

matchPattern g MatchAny a = MatchSuccess $ MatchAnyResult a
matchPattern g MatchIgnore a = MatchSuccess $ MatchIgnoreResult a
matchPattern g (MatchOr ms) v = do
  let f (k, a) b = case matchPattern g a v of
                     MatchSuccess x -> MatchSuccess (k, x)
                     MatchFailure f -> MatchFailure f
                     _ -> b
  (k, res) <- P.foldr f (NoMatch "or fail") (KM.toList ms)
  return $ MatchOrResult (KM.delete k ms) k res

matchPattern g (MatchArrayOr ms) (Array arr) = do
  let h acc' e = do
        acc <- acc'
        case matchPattern g (MatchOr ms) e of
             MatchSuccess s -> return $ acc ++ [s]
             MatchFailure err -> MatchFailure err
             NoMatch err -> return $ acc
  r <- L.foldl' h (MatchSuccess []) (V.toList arr)
  let inner = if P.null r
                 then StarNodeEmpty $ Char $ MatchOr ms
                 else StarNodeValue $ fmap CharNode r
  return $ MatchArrayContextFreeResult $ SeqNode [inner]

-- specific (aka exact)
matchPattern g (MatchStringExact m) (String a) = if m == a then MatchSuccess $ MatchStringExactResult a else NoMatch ("string mismatch: expected " ++ show m ++ " but found " ++ show a)
matchPattern g (MatchNumberExact m) (Number a) = if m == a then MatchSuccess $ MatchNumberExactResult a else NoMatch ("number mismatch: expected " ++ show m ++ " but found " ++ show a)
matchPattern g (MatchBoolExact m) (Bool a) = if m == a then MatchSuccess $ MatchBoolExactResult a else NoMatch ("bool mismatch: expected " ++ show m ++ " but found " ++ show a)
-- any (of a type)
matchPattern g MatchStringAny (String a) = MatchSuccess $ MatchStringAnyResult a
matchPattern g MatchNumberAny (Number a) = MatchSuccess $ MatchNumberAnyResult a
matchPattern g MatchBoolAny (Bool a) = MatchSuccess $ MatchBoolAnyResult a
-- null is just null
matchPattern g MatchNull Null = MatchSuccess MatchNullResult
-- refs, finally :-)
matchPattern g (MatchRef r) v = do
  p <- (m2ms $ MatchFailure $ "Non-existant ref: " ++ r) $ KM.lookup (K.fromString r) g
  a <- matchPattern g p v
  return $ MatchRefResult r a
-- default ca
matchPattern g m a = NoMatch ("bottom reached:\n" ++ show m ++ "\n" ++ show a)

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
  go (MatchObjectOnlyResultF r v) = MatchObjectOnly r
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
    go (MatchObjectOnlyResultF r v) = Object $ KM.union r v
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
valueToExactResult v = matchPattern mempty g v where g = valueToExactGrammar v


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

contextFreeGrammarIsWellFormed' :: (Monad m, Show a) => (a -> m Bool) -> ContextFreeGrammar a -> m Bool
contextFreeGrammarIsWellFormed' f = paraM goM
  where
    --goM :: Show a => ContextFreeGrammarF a (ContextFreeGrammar a, Bool) -> m Bool
    goM (CharF c) = f c
    goM x = return $ go x

    --go :: Show a => ContextFreeGrammarF a (ContextFreeGrammar a, Bool) -> Bool
    go (SeqF a) = P.all id (fmap snd a)
    go (OrF a) = P.all id (fmap snd (KM.elems a))
    go (StarF (p, a)) = (not (isStarLike p)) && a
    go (PlusF (p, a)) = (not (isStarLike p)) && a
    go (OptionalF (p, a)) = (not (isStarLike p)) && a

-- is well-formed

matchPatternIsWellFormed :: (KeyMap MatchPattern) -> MatchPattern -> MatchStatus Bool
matchPatternIsWellFormed g = cataM goM
  where
    goM (MatchRefF r) = do
      p <- (m2ms $ MatchFailure $ "Non-existant ref: " ++ r) $ KM.lookup (K.fromString r) g
      matchPatternIsWellFormed g p
    goM x = return $ go x

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
contextFreeGrammarResultIsWellFormed :: Monad m => (MatchPattern -> m Bool) -> (Bool -> Bool) -> ContextFreeGrammarResult MatchPattern (MatchResult, MatchStatus Bool) -> m Bool
contextFreeGrammarResultIsWellFormed gf rf = paraM go
  where
    --go :: ContextFreeGrammarResultF MatchPattern MatchResult (MatchResult, MatchStatus Bool) -> MatchStatus Bool
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
    go (OptionalNodeValueF r) = (not $ isStarNodeLike (fst r)) && (snd r)

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


