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
  extract (MatchFailure _) = error "cannot extract"
  extract (NoMatch _) = error "cannot extract"
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
      StarNodeValue <$> arbitrary,
      PlusNode <$> arbitrary,
      OrNode <$> arbitrary <*> arbitrary <*> arbitrary,
      OptionalNodeEmpty <$> arbitrary,
      OptionalNodeValue <$> arbitrary]

makeBaseFunctor ''ContextFreeGrammarResult

instance (ToJSON g, ToJSON r) => ToJSON (ContextFreeGrammarResult g r) where
    toEncoding = genericToEncoding defaultOptions

instance (FromJSON g, FromJSON r) => FromJSON (ContextFreeGrammarResult g r)

contextFreeMatch' :: (Show g, Show v) => ContextFreeGrammar g -> [v] -> (g -> v -> MatchStatus r) -> MatchStatus ([v], (ContextFreeGrammarResult g r))
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
              _ -> NoMatch "impossible"
  return (xs', (PlusNode rs'))
  

contextFreeMatch' (Optional a) xs matchFn =
  case contextFreeMatch' a xs matchFn of
       NoMatch _ -> MatchSuccess (xs, OptionalNodeEmpty a)
       MatchFailure s -> MatchFailure s
       MatchSuccess (xs', subresult) -> MatchSuccess (xs', OptionalNodeValue subresult)

contextFreeMatch' a xs _ = error ("no match for: " ++ (show a) ++ " " ++ (show xs))

contextFreeMatch :: (Show g, Show v) => ContextFreeGrammar g -> [v] -> (g -> v -> MatchStatus r) -> MatchStatus (ContextFreeGrammarResult g r)
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
    KeyOpt <$> arbitrary,
    KeyExt <$> arbitrary]

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
      MatchOr <$> arbitrary,
      MatchIfThen <$> arbitrary <*> (T.pack <$> arbitrary) <*> arbitrary,
      return $ MatchFunnel,
      return $ MatchFunnelKeys,
      return $ MatchFunnelKeysU,
      MatchRef <$> arbitrary]


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
    MatchArrayContextFreeResult <$> arbitrary,
    MatchStringExactResult <$> T.pack <$> arbitrary,
    MatchNumberExactResult <$> (Sci.scientific <$> arbitrary <*> arbitrary),
    MatchBoolExactResult <$> arbitrary,
    MatchStringAnyResult <$> T.pack <$> arbitrary,
    MatchNumberAnyResult <$> (Sci.scientific <$> arbitrary <*> arbitrary),
    MatchBoolAnyResult <$> arbitrary,
    return $ MatchNullResult,
    MatchAnyResult <$> arbitrary,
    MatchOrResult <$> arbitrary <*> arbitrary <*> arbitrary,
    MatchIfThenResult <$> arbitrary <*> (T.pack <$> arbitrary) <*> arbitrary,
    MatchFunnelResult <$> arbitrary,
    MatchFunnelKeysResult <$> arbitrary,
    MatchFunnelKeysUResult <$> arbitrary,
    MatchRefResult <$> arbitrary <*> arbitrary]

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

{-
matchPattern (MatchArrayAll m) (Array a) = do
  let vv = (V.toList a)
      f acc e = do
          acc' <- acc
          case matchPattern m e of
             MatchSuccess r -> MatchSuccess (acc' ++ [r])
             MatchFailure r -> MatchFailure r
             NoMatch _ -> MatchSuccess acc'
  acc <- L.foldl' f (MatchSuccess mempty) vv
  acc <- if P.length acc /= P.length vv then NoMatch "Array length mismatch" else MatchSuccess acc
  return $ MatchArrayAllResult (V.fromList acc)

matchPattern (MatchArrayOne m) (Array a) = do
  let vv = (V.toList a)
      f acc e = do
          acc' <- acc
          case matchPattern m e of
             MatchSuccess r -> MatchSuccess (acc' ++ [r])
             MatchFailure r -> MatchFailure r
             NoMatch _ -> MatchSuccess acc'
  acc <- L.foldl' f (MatchSuccess mempty) vv
  acc <- if P.length acc /= 1 then NoMatch "Array length isn't 1" else MatchSuccess acc
  return $ MatchArrayOneResult (P.head acc)

matchPattern (MatchArraySome m) (Array a) = do
  let f acc' e = do
          acc <- acc'
          case matchPattern m e of
             MatchSuccess r -> MatchSuccess $ V.snoc acc (MatchedVal r)
             MatchFailure r -> MatchFailure r
             NoMatch _ -> MatchSuccess $ V.snoc acc (ExtraVal e)
  a1 <- L.foldl' f (MatchSuccess mempty) a
  return $ MatchArraySomeResult a1

matchPattern (MatchArrayExact m) (Array a) = if P.length m /= V.length a then MatchFailure "Array exact match" else do
  let f acc (p, e) = do
          acc' <- acc
          case matchPattern p e of
             MatchSuccess r -> MatchSuccess (acc' ++ [r])
             MatchFailure r -> MatchFailure r
             NoMatch r -> NoMatch r
  acc <- L.foldl' f (MatchSuccess mempty) (P.zip m (V.toList a))
  return $ MatchArrayExactResult acc
-}

matchPattern (MatchArrayContextFree m) (Array a) = do
  case contextFreeMatch m (V.toList a) matchPattern of
       NoMatch e -> NoMatch ("context-free nomatch: " ++ e)
       MatchFailure s -> MatchFailure s
       MatchSuccess x -> MatchSuccess (MatchArrayContextFreeResult x)

matchPattern (MatchArrayContextFree m) (Object a) = MatchFailure ("object in cf:\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode $ m) ++ "\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode $ toJSON $ a))

{-
matchPattern (MatchArrayContextFree m) (Object a) = do
  let a1 = case KM.lookup (fromString "body") a of
              Nothing -> MatchFailure "cf extra fail"
              Just v -> MatchSuccess v
  v <- a1
  v' <- case asArray v of Nothing -> MatchFailure "cf extra fail 2"; Just v -> MatchSuccess v
  let a2 = case contextFreeMatch m v' matchPattern of
             NoMatch e -> NoMatch ("context-free nomatch: " ++ e)
             MatchFailure s -> MatchFailure s
             MatchSuccess x ->  MatchSuccess (MatchArrayContextFreeResult x)
  a2
-}

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
contextFreeGrammarResultToGrammar f = cata go
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
matchResultToPatternAlg (MatchObjectFullResultF g r) = MatchObjectFull (KM.union (fmap KeyOpt g) r)
matchResultToPatternAlg (MatchObjectPartialResultF g r) = MatchObjectPartial (KM.union (fmap KeyOpt g) (KM.filter f r))
  where
    f (KeyExt _) = False
    f _ = True


matchResultToPattern :: MatchResult -> MatchPattern
matchResultToPattern = cata go where
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

contextFreeGrammarIsMovable :: (a -> Bool) -> ContextFreeGrammar a -> Bool
contextFreeGrammarIsMovable f = cata go
  where
    go (CharF a) = f a
    go (SeqF a) = P.any id a
    go (OrF a) = P.any id (KM.elems a)
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
    go (OrNodeF g k r) = r || P.any (contextFreeGrammarIsMovable gf) (KM.elems g)
    go (OptionalNodeValueF r) = True
    go (OptionalNodeEmptyF g) = True

matchPatternIsMovable :: MatchPattern -> Bool
matchPatternIsMovable = cata go
  where
    go (MatchObjectFullF g) = P.any (extractObjectKeyMatch $ error "must not be here") (KM.elems g)
    go (MatchObjectPartialF g) = P.any (extractObjectKeyMatch $ error "must not be here") (KM.elems g)
    go (MatchArrayContextFreeF g) = contextFreeGrammarIsMovable id g
    go (MatchStringExactF _) = False
    go (MatchNumberExactF _) = False
    go (MatchBoolExactF _) = False
    go MatchStringAnyF = True
    go MatchNumberAnyF = True
    go MatchBoolAnyF = True
    go MatchNullF = False
    go MatchAnyF = True
    go (MatchOrF g) = P.any id (KM.elems g)
    go (MatchIfThenF _ _ g) = g
    go MatchFunnelF = True
    go MatchFunnelKeysF = True
    go MatchFunnelKeysUF = True
    --go MatchRef String =

matchResultIsMovableAlg :: MatchResultF Bool -> Bool
matchResultIsMovableAlg = check where
    check (MatchObjectFullResultF g r) = P.any (extractObjectKeyMatch $ error "must not be here") (KM.elems r) || P.any matchPatternIsMovable g
    check (MatchObjectPartialResultF g r) = P.any (extractObjectKeyMatch $ error "must not be here") (KM.elems r) || P.any matchPatternIsMovable g
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
tMapT t v = Object $ KM.fromList [(K.fromString "type", String t)]
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
    go (MatchObjectFullResultF g r) = fmap (replaceSingleton . Object) $ nonEmptyMap $ filterEmpty $ (KM.map f r)
      where
        f (KeyReq v) = v
        f (KeyOpt v) = v
        f (KeyExt _) = error "must not be here"
    go (MatchObjectPartialResultF g r) = fmap (replaceSingleton . Object) $ nonEmptyMap $ filterEmpty $ (KM.map f r)
      where
        f (KeyReq v) = v
        f (KeyOpt v) = v
        f (KeyExt v) = Just v
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
{-
thinPattern or2 $ Just (Object (KM.fromList [("key",String "option2"),("type",String "Or"),("value",Number 44.0)]))
thinPattern or2 $ Just (Object (KM.fromList [("key",String "option1"),("type",String "OrTrivial")]))
-}


thinSeq as v = do
        let gs = fmap (contextFreeGrammarIsMovable matchPatternIsMovable) as
        let isOne = P.length (P.filter id gs) == 1
        v <- if not isOne
                then
                  do
                    v <- (m2ms $ MatchFailure "data error7") $ asKeyMap v
                    itsType <- (m2ms $ MatchFailure "data error8") $ KM.lookup "type" v
                    itsValue <- (m2ms $ MatchFailure "data error9") $ KM.lookup "value" v
                    (m2ms $ MatchFailure "data error10") $ asArray itsValue
                else
                  do
                    return $ [v]
        let f acc' (a, gg) = do
            (ii, acc) <- acc'
            let (i:is) = ii
            if gg -- movable
              then fmap (\x -> (is, acc <> (bimap All L.singleton x))) (thinContextFreeMatch a (Just i))
              else fmap (\x -> (ii, acc <> (bimap (const mempty) L.singleton x))) (thinContextFreeMatch a Nothing)
        r <- L.foldl' f (MatchSuccess (v, mempty)) $ P.zip as gs
        _ <- if P.null $ fst r then MatchSuccess "foo" else MatchFailure "not all consumed"
        let r1@(bb, _) = bimap getAll SeqNode (snd r)
        if not bb then MatchFailure "bb fail" else MatchSuccess r1
        --MatchSuccess r1

thinContextFreeMatch :: ContextFreeGrammar MatchPattern -> Maybe Value -> MatchStatus (Bool, ContextFreeGrammarResult MatchPattern MatchResult)
thinContextFreeMatch (Char a) v = do
  case thinPattern a v of
       NoMatch s -> NoMatch ("no char match: " ++ s)
       MatchFailure s -> MatchFailure s
       MatchSuccess (b, r) -> MatchSuccess (b, CharNode r)

thinContextFreeMatch (Seq as) Nothing = if not $ contextFreeGrammarIsMovable matchPatternIsMovable (Seq as)
                                           then thinSeq as (Array $ V.fromList [])
                                           else NoMatch "data error5"
thinContextFreeMatch (Seq as) (Just v) = do
  if not $ contextFreeGrammarIsMovable matchPatternIsMovable (Seq as)
     then NoMatch "data error6"
     else thinSeq as v

thinContextFreeMatch (Or ms) (Just (Object v)) = do -- or requires an exsistance of a value (Just)
  itsType <- (m2ms $ MatchFailure "data error1") $ KM.lookup (K.fromString "type") v -- OrNodeTrivial or OrNode
  itsKey <- (m2ms $ MatchFailure "data error2") $ KM.lookup (K.fromString "key") v
  itsKey <- (m2ms $ MatchFailure "data error3") $ asString itsKey
  let itsK = (K.fromString . T.unpack) itsKey
  itsMatch <- (m2ms $ MatchFailure "data error4") $ KM.lookup itsK ms
  fmap ((\a -> (True, a)) . (OrNode (KM.delete itsK ms) itsK) . snd) (thinContextFreeMatch itsMatch (KM.lookup (K.fromString "value") v))

thinContextFreeMatch (Star a) (Just (Object v)) = do
  let gg = contextFreeGrammarIsMovable matchPatternIsMovable
  itsType <- (m2ms $ MatchFailure "data error1") $ KM.lookup (K.fromString "type") v -- OrNodeTrivial or OrNode
  itsValue <- (m2ms $ MatchFailure "data error2") $ KM.lookup (K.fromString "value") v
  if gg a
     then -- actual
        do
          itsValue <- (m2ms $ MatchFailure "data error2") $ asArray itsValue
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
          itsValue <- (m2ms $ MatchFailure "data error2") $ asNumber itsValue
          if itsValue == 0
             then
                return (True, StarNodeEmpty $ a)
              else
                do
                  (_, aa) <- thinContextFreeMatch a Nothing
                  return (True, StarNodeValue $ P.take (fromIntegral $ Sci.coefficient itsValue) $ P.repeat aa)

thinContextFreeMatch (Plus a) (Just (Object v)) = do
  let gg = contextFreeGrammarIsMovable matchPatternIsMovable
  itsType <- (m2ms $ MatchFailure "data error1") $ KM.lookup (K.fromString "type") v -- OrNodeTrivial or OrNode
  itsValue <- (m2ms $ MatchFailure "data error2") $ KM.lookup (K.fromString "value") v
  if gg a
     then -- actual
        do
          itsValue <- (m2ms $ MatchFailure "data error2") $ asArray itsValue
          aa <- P.traverse (thinContextFreeMatch a) (fmap Just itsValue)
          let ab = (P.map snd aa)
          return $ (True, PlusNode ab)
      else -- trivial
        do
          itsValue <- (m2ms $ MatchFailure "data error2") $ asNumber itsValue
          (_, aa) <- thinContextFreeMatch a Nothing
          return (True, PlusNode $ P.take (fromIntegral $ Sci.coefficient itsValue) $ P.repeat aa)

thinContextFreeMatch (Optional a) (Just (Object v)) = do
  let gg = contextFreeGrammarIsMovable matchPatternIsMovable
  itsType <- (m2ms $ MatchFailure "data error1") $ KM.lookup (K.fromString "type") v -- OrNodeTrivial or OrNode
  itsKey <- (m2ms $ MatchFailure "data error2") $ KM.lookup (K.fromString "flag") v
  itsKey <- (m2ms $ MatchFailure "data error3") $ asBool itsKey
  if itsKey
     then
        do
          r <- thinContextFreeMatch a (KM.lookup (K.fromString "value") v)
          return $ bimap (const True) OptionalNodeValue r
      else
        do
          return $ (True, OptionalNodeEmpty a)
{-
       NoMatch _ -> MatchSuccess (xs, OptionalNodeEmpty a)
       MatchFailure s -> MatchFailure s
       MatchSuccess (xs', subresult) -> MatchSuccess (xs', OptionalNodeValue subresult)-}

thinContextFreeMatch a xs = error ("no match for: " ++ (show a) ++ " " ++ (show xs))

{-
thinContextFreeMatch :: (Show g, Show v) => ContextFreeGrammar g -> [v] -> (g -> v -> MatchStatus r) -> MatchStatus (ContextFreeGrammarResult g r)
thinContextFreeMatch a xs = do
  (rest, result) <- thinContextFreeMatch a xs
  case P.length rest == 0 of
       False -> NoMatch ("rest left: " ++ show rest)
       True -> MatchSuccess result-}

thinPattern :: MatchPattern -> Maybe Value -> MatchStatus (Bool, MatchResult)

tObj :: Bool -> KeyMap (ObjectKeyMatch MatchPattern) -> Object -> MatchStatus (KeyMap MatchPattern, KeyMap (ObjectKeyMatch MatchResult))
tObj keepExt m a = do
  preResult <- L.foldl' (doKeyMatch m a) (MatchSuccess mempty) (keys m)
  L.foldl' f (MatchSuccess preResult) (keys a)
    where
      gg = matchPatternIsMovable
      step k r acc req = case KM.lookup k a of
                      -- KeyOpt means key might be missing
                      Nothing -> if gg r
                                    then -- actual. only might be missing opt key
                                      if req
                                        then NoMatch $ "Required key " ++ show k ++ " not found in map"
                                        else MatchSuccess $ first (KM.insert k r) acc
                                    else -- trivial. get from grammar
                                      do
                                        rr <- thinPattern r Nothing
                                        ll <- return $ snd rr
                                        el <- return $ if req then (KeyReq ll) else (KeyOpt ll)
                                        return $ second (KM.insert k el) acc
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

thinPattern (MatchObjectFull m) (Just (Object a)) = (fmap $ (\x -> (True, uncurry MatchObjectFullResult x))) (tObj False m a)
thinPattern (MatchObjectPartial m) (Just (Object a)) = (fmap $ (\x -> (True, uncurry MatchObjectFullResult x))) (tObj True m a)

thinPattern (MatchObjectFull m) Nothing = thinPattern (MatchObjectFull m) (Just $ Object $ KM.empty)
thinPattern (MatchObjectPartial m) Nothing = thinPattern (MatchObjectPartial m) (Just $ Object $ KM.empty)


{-

seq1 = MatchArrayContextFree (Seq [Char $ MatchNumberExact 1, Char $ MatchNumberAny])
dseq1 = Array [Number 1, Number 2]
matchPattern seq1 dseq1

MatchSuccess (MatchArrayContextFreeResult (SeqNode [CharNode (MatchNumberExactResult 1.0),CharNode (MatchNumberAnyResult 2.0)]))

ghci> matchResultToThinValue $ MatchArrayContextFreeResult (SeqNode [CharNode (MatchNumberExactResult 1.0),CharNode (MatchNumberAnyResult 2.0)])

ts = Just (Object (fromList [("type",String "SeqNode"),("value",Array [Object (fromList [("type",String "Char"),("value",Number 2.0)])])]))
-}

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
  itsType <- (m2ms $ MatchFailure "data error1") $ KM.lookup (K.fromString "type") v
  itsKey <- (m2ms $ MatchFailure "data error2") $ KM.lookup (K.fromString "key") v
  itsKey <- (m2ms $ MatchFailure "data error3") $ asString itsKey
  let itsK = (K.fromString . T.unpack) itsKey
  itsMatch <- (m2ms $ MatchFailure "data error4") $ KM.lookup itsK ms
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
thinPattern m a = NoMatch ("bottom reached:\n" ++ show m ++ "\n" ++ show a)

-- Match functions end
{-
:{
matchPatternWithRefs
  (fromList [
    (
      "category",
       MatchObject (fromList [
        ("children", MatchArray $ MatchRef "category"),
        ("name", MatchLiteral)
       ])
    )
  ])
  (MatchRef "category")
  (Object (fromList [("name", "category1"), ("children", Array [(Object (fromList [("name", "category2"), ("children", Array [(Object (fromList [("name", "category3"), ("children", Array [])]))])]))])]))
:}
-}

{-
matchPattern
  (MatchArray
    (MatchObject
      (fromList [("name", MatchLiteral)])))
  (Array [
    Object (fromList [("name", String "apple")]),
    Object (fromList [("name", String "banana")]),
    Object (fromList [("name", String "orange")])])
MatchSuccess
  (MatchArrayResult [
    MatchObject (fromList [("name",MatchString "apple")]),
    MatchObject (fromList [("name",MatchString "banana")]),
    MatchObject (fromList [("name",MatchString "orange")])])
-}


g00 = (Seq [(Star (Char 1)), (Optional (Char 4))])

main1 = do
  contextFreeMatch g00 ([1, 1, 1, 4] :: [Int]) ((\a b -> if a == b then MatchSuccess a else NoMatch "foo") :: Int -> Int -> MatchStatus Int)


qc1 = do
  quickCheck (\g v -> case (matchPattern g v) of (MatchSuccess s) -> v == matchResultToValue s; _ -> True)

{-
ghci> qc2
*** Failed! Falsified (after 3 tests and 1 shrink):     
MatchObjectPartial (fromList [])
Object (fromList [])

-}

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

-- Different matches for or example (trivial and normal)
-- p[attern] v[alue] r[esult] t[hin value]

tVIs :: MatchPattern -> Value -> Expectation
tVIs p v = 
      let r = extract $ matchPattern p v
          t' = matchResultToThinValue r
          r' = extract (fmap snd (thinPattern p t'))
      in r' `shouldBe` r
      --t `shouldBe` t'

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
            (K.fromString "a", KeyReq (MatchNumberExact 1)),
            (K.fromString "b", KeyOpt (MatchNumberExact 2)),
            (K.fromString "b1", KeyOpt (MatchNumberExact 3)),
            (K.fromString "c", KeyReq (MatchNumberAny)),
            (K.fromString "d", KeyOpt (MatchNumberAny)),
            (K.fromString "d1", KeyOpt (MatchNumberAny))]))
          v = Object (KM.fromList [
            (K.fromString "a", Number 1),
            (K.fromString "a", Number 2),
            (K.fromString "c", Number 4),
            (K.fromString "d", Number 5)])
      tVIs p v
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


{-
fmap matchResultToThinValue  $ matchPattern or1 $ Number 2
uccess (Just (Object (fromList [("key",String "option2"),("type",String "OrTrivial")])))
or2 = (MatchOr (KM.fromList [(K.fromString "option1", (MatchNumberExact 1)), (K.fromString "option2", MatchNumberAny)]))
mor2 = matchPattern or1 $ Number 44
mor2
NoMatch "or fail"
ghci> mor2 = matchPattern or2 $ Number 44

<interactive>:164:1: warning: [-Wname-shadowing]
    This binding for ‘mor2’ shadows the existing binding
      defined at <interactive>:162:1
ghci> mor2
MatchSuccess (MatchOrResult (fromList [("option1",MatchNumberExact 1.0)]) "option2" (MatchNumberAnyResult 44.0))
ghci> fmap matchResultToThinValue mor2
MatchSuccess (Just (Object (fromList [("key",String "option2"),("type",String "Or"),("value",Number 44.0)])))

ghci> or1 = (MatchOr (KM.fromList [(K.fromString "option1", (MatchNumberExact 1)), (K.fromString "option2", (MatchNumberExact 2))]))
ghci> mor1 = matchPattern or1 $ Number 2
ghci> fmap matchResultToThinValue  $ matchPattern or1 $ Number 2
MatchSuccess (Just (Object (fromList [("key",String "option2"),("type",String "OrTrivial")])))
ghci> or2 = (MatchOr (KM.fromList [(K.fromString "option1", (MatchNumberExact 1)), (K.fromString "option2", MatchNumberAny)]))
ghci> mor2 = matchPattern or1 $ Number 44
ghci> mor2
NoMatch "or fail"
ghci> mor2 = matchPattern or2 $ Number 44

<interactive>:164:1: warning: [-Wname-shadowing]
    This binding for ‘mor2’ shadows the existing binding
      defined at <interactive>:162:1
ghci> mor2
MatchSuccess (MatchOrResult (fromList [("option1",MatchNumberExact 1.0)]) "option2" (MatchNumberAnyResult 44.0))
ghci> fmap matchResultToThinValue mor2
MatchSuccess (Just (Object (fromList [("key",String "option2"),("type",String "Or"),("value",Number 44.0)])))
-}

{-
ghci> matchPattern (MatchArrayContextFree $ (Seq [Char $ MatchNumberExact 1, Char $ MatchNumberAny])) (Array [(Number 1), (Number 2.0)])
MatchSuccess (MatchArrayContextFreeResult (SeqNode [CharNode (MatchNumberExactResult 1.0),CharNode (MatchNumberAnyResult 2.0)]))

old:
ghci> matchResultToThinValue $ MatchArrayContextFreeResult (SeqNode [CharNode (MatchNumberExactResult 1.0),CharNode (MatchNumberAnyResult 2.0)])
Just (Object (fromList [("type",String "Char"),("value",Number 2.0)]))

new:
Just (Number 2.0)

ghci> thinPattern (MatchArrayContextFree $ (Seq [Char $ MatchNumberExact 1, Char $ MatchNumberAny])) (Just (Number 2.0))
MatchFailure "bb fail"


or1 = MatchArrayContextFree (Seq [Or $ fromList [(fromString "opt1", Char $ MatchNumberExact 1), (fromString "opt2", Char $ MatchNumberAny)]])

ghci> matchPattern or1 (Array [Number 2])
MatchSuccess (MatchArrayContextFreeResult (SeqNode [OrNode (fromList [("opt1",Char (MatchNumberExact 1.0))]) "opt2" (CharNode (MatchNumberAnyResult 2.0))]))

ghci> ror1 = matchPattern or1 (Array [Number 2])
ghci> fmap matchResultToThinValue ror1
MatchSuccess (Just (Object (fromList [("key",String "opt2"),("type",String "OrNode"),("value",Number 2.0)])))

ortv1 = Just (Object (fromList [("key",String "opt2"),("type",String "OrNode"),("value",Number 2.0)]))

ghci> thinPattern or1 ortv1
MatchSuccess (True,MatchArrayContextFreeResult (SeqNode [OrNode (fromList [("opt1",Char (MatchNumberExact 1.0))]) "opt2" (CharNode (MatchNumberAnyResult 2.0))]))

ghci> ror2 = matchPattern or1 (Array [Number 1])
ghci> ror2
MatchSuccess (MatchArrayContextFreeResult (SeqNode [OrNode (fromList [("opt2",Char MatchNumberAny)]) "opt1" (CharNode (MatchNumberExactResult 1.0))]))

ghci> fmap matchResultToThinValue ror2
MatchSuccess (Just (Object (fromList [("key",String "opt1"),("type",String "OrNodeTrivial")])))

ortv2 = Just (Object (fromList [("key",String "opt1"),("type",String "OrNodeTrivial")]))

-}

{-
optional_grammar_1 = MatchArrayContextFree (Seq [Optional $ Char $ MatchNumberExact 1])
-}
