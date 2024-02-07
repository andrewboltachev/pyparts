{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}


module Logicore.Matcher.Core where
{-  (
  --  matchPattern'
  --, matchPattern'
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

import Prelude as P hiding ((++))

import qualified Data.Vector.Generic
--import qualified Data.Set
import qualified Data.List        as L
import GHC.Generics
import Data.Aeson
--import Data.ByteString            as B
import Data.ByteString.Lazy       as BL hiding (putStrLn)
import Data.Text                  as T
import Data.Text.Encoding         as T
--import Data.Text.IO               as T
import Data.Text.Lazy             as TL
import Data.Text.Lazy.Encoding    as TL
--import Data.Text.Lazy.IO          as TL
--import Data.Map                   as M
import Data.Aeson.KeyMap          as KM
import Data.Aeson.Key             as K
import qualified Data.Scientific as Sci
import qualified Data.Vector as V
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

import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Monad.IO.Class
import Data.Functor.Identity

import Test.QuickCheck
import Test.QuickCheck.Gen (oneof)
import Test.Hspec

import Language.Haskell.TH
import Language.Haskell.TH.Datatype as TH.Abs
import Language.Haskell.TH.Datatype.TyVarBndr
import Language.Haskell.TH.Syntax (mkNameG_tc, mkNameG_v)

import Logicore.Matcher.ValueBaseFunctor
import Logicore.Matcher.Helpers
import Control.Concurrent.Async (mapConcurrently)

import Text.Regex.TDFA((=~))

import qualified Database.MongoDB as MongoDB
import qualified Database.Redis as Redis
import Data.Aeson.Bson hiding (String)
import Data.IORef


a ++ b = T.append a b

-- Utils
wordsWhen     :: (Char -> Bool) -> String -> [String]
wordsWhen p s =  case P.dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = P.break p s'


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

k2s = (String . K.toText)

-- CF matcher
data ContextFreeGrammar a = Char a
                            | Seq (V.Vector (ContextFreeGrammar a))
                            | Or (KeyMap (ContextFreeGrammar a))
                            | Star (ContextFreeGrammar a)
                            | Plus (ContextFreeGrammar a)
                            | Optional (ContextFreeGrammar a)
                              deriving (Generic, Eq, Show, Functor, Foldable, Traversable)

{-instance Arbitrary a => Arbitrary (ContextFreeGrammar a) where
  arbitrary = oneof [
    Char <$> arbitrary,
    Seq <$> arbitrary,
    Or <$> arbitrary,
    Star <$> arbitrary,
    Plus <$> arbitrary,
    Optional <$> arbitrary]-}

makeBaseFunctor ''ContextFreeGrammar

instance ToJSON a => ToJSON (ContextFreeGrammar a) where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON a => FromJSON (ContextFreeGrammar a)

-- TODO: much better approach?
data ContextFreeGrammarResult g r = CharNode r
                                  | SeqNode (V.Vector (ContextFreeGrammarResult g r))
                                  | StarNodeEmpty (ContextFreeGrammar g)
                                  | StarNodeValue (V.Vector (ContextFreeGrammarResult g r))
                                  | StarNodeIndexed (V.Vector (ContextFreeGrammarResult g r)) (V.Vector Int)
                                  | PlusNode (V.Vector (ContextFreeGrammarResult g r))
                                  | PlusNodeIndexed (V.Vector (ContextFreeGrammarResult g r)) (V.Vector Int)
                                  | OrNode (KeyMap (ContextFreeGrammar g)) Key (ContextFreeGrammarResult g r)
                                  | OptionalNodeValue (ContextFreeGrammarResult g r)
                                  | OptionalNodeEmpty (ContextFreeGrammar g)
                                    deriving (Generic, Eq, Show, Functor, Foldable, Traversable)

{-instance (Arbitrary g, Arbitrary r) => Arbitrary (ContextFreeGrammarResult g r) where
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
      OptionalNodeValue <$> arbitrary]-}

makeBaseFunctor ''ContextFreeGrammarResult

instance (ToJSON g, ToJSON r) => ToJSON (ContextFreeGrammarResult g r) where
    toEncoding = genericToEncoding defaultOptions

instance (FromJSON g, FromJSON r) => FromJSON (ContextFreeGrammarResult g r)

-- types
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
data MatchPattern = MatchObjectFull (KeyMap (ObjectKeyMatch MatchPattern)) -- delete
                  | MatchObjectWithDefaults (KeyMap MatchPattern) (KeyMap Value)
                  | MatchObjectOnly (KeyMap MatchPattern)
                  | MatchObjectWhole MatchPattern
                  | MatchOmitField Key MatchPattern -- think
                  | MatchSelectFields (V.Vector Key) MatchPattern -- think
                  | MatchFork (KeyMap MatchPattern) -- think
                  | MatchObjectPartial (KeyMap (ObjectKeyMatch MatchPattern)) -- delete
                  -- structures - array
                  -- | MatchArrayAll MatchPattern
                  -- | MatchArraySome MatchPattern
                  -- | MatchArrayOne MatchPattern
                  -- | MatchArrayExact (V.Vector MatchPattern)
                  | MatchArrayContextFree (ContextFreeGrammar MatchPattern)
                  | MatchArray MatchPattern -- think hard
                  | MatchArrayOnly MatchPattern -- bigger pattern???
                  -- literals: match particular value of
                  | MatchStringExact !T.Text
                  | MatchStringRegExp !T.Text
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
                  | MatchNone
                  | MatchDefault Value -- remove
                  | MatchOr (KeyMap MatchPattern)
                  | MatchNot MatchPattern
                  | MatchAnd MatchPattern MatchPattern -- need?
                  | MatchArrayOr (KeyMap MatchPattern) -- need?
                  | MatchIfThen MatchPattern T.Text MatchPattern
                  -- funnel
                  | MatchFunnel
                  | MatchFunnelKeys
                  | MatchFunnelKeysU -- remove?
                  -- special
                  | MatchRef T.Text
                  | MatchFromMongoDB T.Text T.Text MatchPattern -- not sure
                  | MatchFromRedis T.Text T.Text MatchPattern -- not sure
                  | MatchGetFromRedis T.Text T.Text MatchPattern -- not sure
                  | MatchGetFromIORef MatchPattern -- not sure
                  | MatchGetFromFile T.Text MatchPattern -- not sure
                    deriving (Generic, Eq, Show)

-- extract: bigger patterns (also look bb) and ?

{-matchObjectWithDefaultsArbitrary = do
        m <- arbitrary
        v <- arbitrary
        let m' = fmap (bimap (K.fromText . (\a -> T.concat ["m", T.pack a])) id) m
        let v' = fmap (bimap (K.fromText . (\a -> T.concat ["v", T.pack a])) id) v
        return $ MatchObjectWithDefaults (fromList m') (fromList v')

instance Arbitrary MatchPattern where
  arbitrary = oneof [
      MatchObjectFull <$> arbitrary,
      matchObjectWithDefaultsArbitrary,
      MatchObjectPartial <$> arbitrary,
      MatchArrayContextFree <$> arbitrary,
      MatchArrayOnly <$> arbitrary,
      MatchStringExact <$> T.pack <$> arbitrary,
      --MatchStringRegExp <$> T.pack <$> arbitrary,
      MatchNumberExact <$> (Sci.scientific <$> arbitrary <*> arbitrary),
      MatchBoolExact <$> arbitrary,
      return $ MatchStringAny,
      return $ MatchNumberAny,
      return $ MatchBoolAny,
      return $ MatchNull,
      return $ MatchAny,
      return $ MatchNone,
      MatchDefault <$> arbitrary,
      MatchOr <$> arbitrary,
      MatchNot <$> arbitrary,
      MatchAnd <$> arbitrary <*> arbitrary]
      --MatchIfThen <$> arbitrary <*> (T.pack <$> arbitrary) <*> arbitrary
      --return $ MatchFunnel,
      --return $ MatchFunnelKeys,
      --return $ MatchFunnelKeysU
      --MatchRef <$> arbitrary-}

makeBaseFunctor ''MatchPattern

instance ToJSON MatchPattern where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON MatchPattern
    -- No need to provide a parseJSON implementation.

                 -- structures - object
data MatchResult = MatchObjectFullResult (KeyMap MatchPattern) (KeyMap (ObjectKeyMatch MatchResult)) -- delete
                 | MatchObjectPartialResult (KeyMap MatchPattern) (KeyMap (ObjectKeyMatch MatchResult)) -- delete
                 -- structures - array
                 -- | MatchArrayAllResult (V.Vector MatchResult)
                 -- | MatchArraySomeResult (V.Vector (ArrayValMatch MatchResult))
                 -- | MatchArrayOneResult MatchResult
                 -- | MatchArrayExactResult (V.Vector MatchResult)
                 | MatchObjectWithDefaultsResult (KeyMap MatchResult) (KeyMap Value) (KeyMap Value)
                 | MatchObjectOnlyResult (KeyMap MatchResult) (KeyMap Value)
                 | MatchObjectWholeResult (KeyMap MatchResult)
                 | MatchArrayContextFreeResult (ContextFreeGrammarResult MatchPattern MatchResult)
                 | MatchArrayOnlyResultEmpty MatchPattern (V.Vector Value)
                 | MatchArrayOnlyResultSome (V.Vector MatchResult) (V.Vector (Maybe Value))
                 -- literals: match particular value of
                 | MatchStringExactResult !T.Text
                 | MatchStringRegExpResult !T.Text !T.Text
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
                 | MatchNoneResult Value
                 | MatchDefaultResult Value
                 | MatchOrResult (KeyMap MatchPattern) Key MatchResult
                 | MatchNotResult MatchPattern Value
                 | MatchAndResult MatchResult MatchResult
                 | MatchIfThenResult MatchPattern T.Text MatchResult
                 -- funnel
                 | MatchFunnelResult Value
                 | MatchFunnelKeysResult (KeyMap Value)
                 | MatchFunnelKeysUResult (KeyMap Value)
                 -- special
                 | MatchRefResult T.Text MatchResult
                 | MatchFromMongoDBResult T.Text T.Text T.Text
                 | MatchFromRedisResult T.Text T.Text T.Text
                   deriving (Generic, Eq, Show)

{-matchObjectWithDefaultsResultArbitrary = do
        m <- arbitrary
        d <- arbitrary
        v <- arbitrary
        let m' = fmap (first (K.fromText . ("m"++) . T.pack)) m
        let d' = fmap (first (K.fromText . ("d"++) . T.pack)) d
        let v' = fmap (first (K.fromText . ("v"++) . T.pack)) v
        return $ MatchObjectWithDefaultsResult (fromList m') (fromList d') (fromList v')

matchObjectOnlyResultArbitrary = do
        m <- arbitrary
        d <- arbitrary
        let m' = fmap (first (K.fromText . ("m"++) . T.pack)) m
        let d' = fmap (first (K.fromText . ("d"++) . T.pack)) d
        return $ MatchObjectOnlyResult (fromList m') (fromList d')

instance Arbitrary MatchResult where
  arbitrary = oneof [
    MatchObjectFullResult <$> arbitrary <*> arbitrary,
    MatchObjectPartialResult <$> arbitrary <*> arbitrary,
    matchObjectWithDefaultsResultArbitrary,
    matchObjectOnlyResultArbitrary,
    MatchArrayContextFreeResult <$> (SeqNode <$> arbitrary),
    MatchArrayOnlyResultEmpty <$> arbitrary <*> arbitrary,
    MatchArrayOnlyResultSome <$> arbitrary <*> arbitrary,
    MatchStringExactResult <$> T.pack <$> arbitrary,
    --MatchStringRegExpResult <$> T.pack <$> arbitrary,
    MatchNumberExactResult <$> (Sci.scientific <$> arbitrary <*> arbitrary),
    MatchBoolExactResult <$> arbitrary,
    MatchStringAnyResult <$> T.pack <$> arbitrary,
    MatchNumberAnyResult <$> (Sci.scientific <$> arbitrary <*> arbitrary),
    MatchBoolAnyResult <$> arbitrary,
    return $ MatchNullResult,
    MatchAnyResult <$> arbitrary,
    MatchNoneResult <$> arbitrary,
    MatchDefaultResult <$> arbitrary,
    MatchOrResult <$> arbitrary <*> arbitrary <*> arbitrary,
    MatchNotResult <$> arbitrary <*> arbitrary,
    MatchAndResult <$> arbitrary <*> arbitrary]
    --MatchIfThenResult <$> arbitrary <*> (T.pack <$> arbitrary) <*> arbitrary,
    --MatchFunnelResult <$> arbitrary,
    --MatchFunnelKeysResult <$> arbitrary,
    --MatchFunnelKeysUResult <$> arbitrary
    --MatchRefResult <$> arbitrary <*> arbitrary-}

makeBaseFunctor ''MatchResult

instance ToJSON MatchResult where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON MatchResult
    -- No need to provide a parseJSON implementation.

-- MatchPattern × Value -(matchPattern')-> MatchResult

data MatchPath = ObjKey Key | ArrKey Int deriving (Generic, Eq, Show)

-- MatchStatus
data MatchStatus a = MatchSuccess a
                 | MatchFailure T.Text
                 | NoMatch T.Text
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
  extract (MatchFailure e) = error $ T.unpack $ "cannot extract1: " ++ e
  extract (NoMatch e) = error $ T.unpack $ "cannot extract2: " ++ e
  duplicate (MatchSuccess s) = MatchSuccess (MatchSuccess s)
  duplicate (MatchFailure m) = MatchFailure m
  duplicate (NoMatch m) = NoMatch m

data MatcherEnv = MatcherEnv { redisConn :: Redis.Connection, grammarMap :: (KeyMap MatchPattern), indexing :: Bool, dataRef :: IORef (KeyMap Value) }
emptyEnvValue = MatcherEnv { grammarMap = mempty, indexing = False }

newtype MatchStatusT m a = MatchStatusT { runMatchStatusT :: ReaderT MatcherEnv m (MatchStatus a) }
instance Functor m => Functor (MatchStatusT m) where
  fmap f (MatchStatusT ma) = MatchStatusT $ (fmap . fmap) f ma

instance (Applicative m) => Applicative (MatchStatusT m) where
  pure x = MatchStatusT (pure (pure x))
  (MatchStatusT fab) <*> (MatchStatusT mma) = MatchStatusT $ (fmap (<*>) fab) <*> mma

instance (Monad m) => Monad (MatchStatusT m) where
  return = pure
  (>>=) :: MatchStatusT m a -> (a -> MatchStatusT m b) -> MatchStatusT m b
  (MatchStatusT ma) >>= f = MatchStatusT $ ma >>= (f')
      where f' ma = case ma of
                      MatchSuccess x -> (runMatchStatusT . f) x
                      NoMatch e -> return $ NoMatch e
                      MatchFailure e -> return $ MatchFailure e

noMatch :: Monad m => T.Text -> MatchStatusT m a
noMatch x = MatchStatusT (return (NoMatch x))

matchFailure :: Monad m => T.Text -> MatchStatusT m a
matchFailure x = MatchStatusT (return (MatchFailure x))

instance MonadTrans MatchStatusT where
  lift = MatchStatusT . ReaderT . const . (fmap MatchSuccess)

instance (MonadIO m) => MonadIO (MatchStatusT m) where
  liftIO = lift. liftIO


-- functions
contextFreeMatch' :: (Show g, Show v, Show r, MonadIO m) => ContextFreeGrammar g -> (V.Vector v) -> (g -> v -> MatchStatusT m r) -> MatchStatusT m ((V.Vector v), (ContextFreeGrammarResult g r))
contextFreeMatch' (Char _) [] _ = noMatch "can't read char"
contextFreeMatch' (Char a) vec matchFn = MatchStatusT $ do
  let x = V.head vec; xs = V.tail vec
  rr <- runMatchStatusT $ matchFn a x
  return $ case rr of
       NoMatch s -> NoMatch ("no char match: " ++ s)
       MatchFailure s -> MatchFailure s
       MatchSuccess a' -> MatchSuccess (xs, CharNode a')

contextFreeMatch' (Seq as) xs matchFn = do
  let f acc' a = do
          (xs, result) <- acc'
          (xs', result') <- contextFreeMatch' a xs matchFn
          return (xs', V.snoc result result')
  (rest, res) <- L.foldl' f (return (xs, mempty)) as
  return $ (rest, SeqNode res)

contextFreeMatch' (Or as) xs matchFn = L.foldr f (noMatch "or mismatch") (KM.toList as)
  where f (opt, a) b = MatchStatusT $ do
          rr <- runMatchStatusT $ contextFreeMatch' a xs matchFn
          runMatchStatusT $ case rr of
               NoMatch _ -> b
               MatchFailure s -> matchFailure s
               MatchSuccess (xs', r) -> return (xs', OrNode (KM.delete opt as) opt r)

contextFreeMatch' (Star a) xs matchFn = (fmap . fmap) c $ f (return (xs, mempty))
  where --f :: MatchStatus ([b], ContextFreeGrammar a) -> MatchStatus ([b], ContextFreeGrammar a)
        c [] = StarNodeEmpty a
        c xs = StarNodeValue xs
        f acc = do
          (xs, result) <- acc
          MatchStatusT $ do
            rr <- runMatchStatusT $ contextFreeMatch' a xs matchFn
            runMatchStatusT $ case rr of
                NoMatch _ -> acc
                MatchFailure s -> matchFailure s
                MatchSuccess (xs', result') -> f (return (xs', V.snoc result result'))

contextFreeMatch' (Plus a) xs matchFn = do
  (xs', subresult) <- contextFreeMatch' (Seq [a, Star a]) xs matchFn
  rs' <- case subresult of
              (SeqNode [r, (StarNodeValue rs)]) -> return $ V.cons r rs
              _ -> noMatch ("impossible203" ++ (T.pack $ show subresult))
  return (xs', (PlusNode rs'))
  

contextFreeMatch' (Optional a) xs matchFn = MatchStatusT $ do
  rr <- runMatchStatusT $ contextFreeMatch' a xs matchFn
  return $ case rr of
       NoMatch _ -> MatchSuccess (xs, OptionalNodeEmpty a)
       MatchFailure s -> MatchFailure s
       MatchSuccess (xs', subresult) -> MatchSuccess (xs', OptionalNodeValue subresult)

contextFreeMatch' a xs _ = error $ T.unpack ("no contextFreeMatch for:\n\n" ++ (T.pack $ show a) ++ "\n\n" ++ (T.pack $ show xs))

contextFreeMatch :: (Show g, Show v, Show r, MonadIO m, ToJSON v) => ContextFreeGrammar g -> (V.Vector v) -> (g -> v -> MatchStatusT m r) -> MatchStatusT m (ContextFreeGrammarResult g r)
contextFreeMatch a xs matchFn = do
  (rest, result) <- contextFreeMatch' a xs matchFn
  case P.length rest == 0 of
       False -> noMatch ("rest lef1t: " ++ (T.decodeUtf8 $ BL.toStrict (encode $ rest)) ++ "\n\n" ++ "grammar was:\n" ++ (T.pack $ show a))
       True -> return result

-- helpers. Regular

m2e :: e -> Maybe a -> Either e a
m2e e m = case m of
               Nothing -> Left e
               Just x -> Right x

m2et :: MonadIO m => e -> Maybe a -> ExceptT e m a
m2et e x = ExceptT (return (m2e e x))

safeHead :: [a] -> Maybe a
safeHead (x:_) = Just x
safeHead _ = Nothing

catMaybes xs = L.foldl' f mempty xs
  where f a b = case b of
                     Nothing -> a
                     Just x -> V.snoc a x

-- helpers. Aeson

asKeyMap :: Value -> Maybe Object
asKeyMap (Object a) = Just a
asKeyMap _ = Nothing

asArray :: Value -> Maybe (V.Vector Value)
asArray (Array a) = Just a
asArray _ = Nothing

asString (String x) = Just x
asString _ = Nothing

asBool (Bool x) = Just x
asBool _ = Nothing

asNumber (Number x) = Just x
asNumber _ = Nothing

--- helpers

vconcat :: V.Vector (V.Vector a) -> V.Vector a
vconcat vs = V.foldl (V.++) mempty vs

gatherFunnelContextFreeFAlgebra :: ContextFreeGrammarResultF MatchPattern (V.Vector Value) (V.Vector Value) -> (V.Vector Value)
gatherFunnelContextFreeFAlgebra (CharNodeF r) = r
gatherFunnelContextFreeFAlgebra (SeqNodeF r) = vconcat r
gatherFunnelContextFreeFAlgebra (StarNodeEmptyF g) = V.empty
gatherFunnelContextFreeFAlgebra (StarNodeValueF r) = vconcat r
gatherFunnelContextFreeFAlgebra (PlusNodeF r) = vconcat r
gatherFunnelContextFreeFAlgebra (OrNodeF g k r) = r
gatherFunnelContextFreeFAlgebra (OptionalNodeValueF r) = r
gatherFunnelContextFreeFAlgebra (OptionalNodeEmptyF g) = V.empty

gatherFunnelContextFree :: ContextFreeGrammarResult MatchPattern (V.Vector Value) -> V.Vector Value
-- ContextFreeGrammarResultF MatchPattern (MatchStatusT m [a]) [a] -> MatchStatusT m [a]
-- ContextFreeGrammarResultF MatchPattern [a] [a] -> MatchStatusT m [a]
gatherFunnelContextFree = cata gatherFunnelContextFreeFAlgebra

--unique = P.reverse . L.nub . P.reverse

gatherFunnelFAlgebra :: MonadIO m => MatchResultF (V.Vector Value) -> MatchStatusT m (V.Vector Value)
gatherFunnelFAlgebra (MatchObjectFullResultF _ r) = return $ L.foldl' f mempty (KM.elems r)
  where f acc (KeyReq e) = acc V.++ e
        f acc (KeyOpt e) = acc V.++ e
        f acc (KeyExt _) = acc
gatherFunnelFAlgebra (MatchObjectPartialResultF _ r) = return $ L.foldl' f mempty (KM.elems r)
  where f acc (KeyReq e) = acc V.++ e
        f acc (KeyOpt e) = acc V.++ e
        f acc (KeyExt _) = acc
gatherFunnelFAlgebra (MatchObjectWithDefaultsResultF r _ _) = return $ V.concat (KM.elems r)
gatherFunnelFAlgebra (MatchObjectOnlyResultF r _) = return $ V.concat (KM.elems r)
gatherFunnelFAlgebra (MatchObjectWholeResultF r) = return $ V.concat (KM.elems r)
gatherFunnelFAlgebra (MatchArrayContextFreeResultF c) = return $ gatherFunnelContextFree c
gatherFunnelFAlgebra (MatchArrayOnlyResultEmptyF g r) = return $ V.empty
gatherFunnelFAlgebra (MatchArrayOnlyResultSomeF r v) = return $ vconcat r
gatherFunnelFAlgebra (MatchOrResultF g k r) = return $ r
gatherFunnelFAlgebra (MatchNotResultF g r) = return $ V.empty
gatherFunnelFAlgebra (MatchAndResultF r' r) = return $ r' V.++ r
gatherFunnelFAlgebra (MatchIfThenResultF _ _ r) = return $ r
gatherFunnelFAlgebra (MatchFunnelResultF r) = return $ V.singleton r
gatherFunnelFAlgebra (MatchFunnelKeysResultF m) = return $ V.fromList $ fmap k2s (KM.keys m)
gatherFunnelFAlgebra (MatchFunnelKeysUResultF m) = error "not implemented" -- return $ unique $ fmap k2s (KM.keys m) -- TODO what idea?
gatherFunnelFAlgebra (MatchRefResultF ref r) = return $ r
gatherFunnelFAlgebra (MatchFromMongoDBResultF _ _ _) = error "not implemented"
gatherFunnelFAlgebra (MatchFromRedisResultF _ _ _) = error "not implemented"
gatherFunnelFAlgebra _ = return $ V.empty

gatherFunnel' :: MonadIO m => MatchResult -> MatchStatusT m (V.Vector Value) -- TODO Monoid?
gatherFunnel' = cataM gatherFunnelFAlgebra

--
-- Convert Maybe to MatchStatus (e.g. a result of KM.lookup)
--

m2ms :: MatchStatus a -> Maybe a -> MatchStatus a
m2ms m v = case v of
              Just x -> MatchSuccess x
              Nothing -> m

m2mst :: MonadIO m => MatchStatusT m a -> Maybe a -> MatchStatusT m a
m2mst m v = case v of
              Just x -> return x
              Nothing -> m

-- pattern -> value -> result. result = value × pattern (is a product)
-- Both pattern and value can be derived from a result using trivial projections
-- (look category theory product)
--fa :: MonadIO m => MatchResultF MatchResult -> MatchStatusT m a
--fa = undefined
--matchPattern' :: MonadIO m => (MatchResultF a -> MatchStatusT m a) -> MatchPattern -> Value -> MatchStatusT m (MatchResultF a)
matchPattern'
  :: (Show r, MonadIO m) =>
     (MatchResultF r -> MatchStatusT m r)
     -> MatchPattern -> Value -> MatchStatusT m (MatchResultF r)

--mObj :: Monad m => Bool -> KeyMap (ObjectKeyMatch MatchPattern) -> Object -> MatchStatusT m (KeyMap MatchPattern, KeyMap (ObjectKeyMatch MatchResult))
mObj fa keepExt m a = do
  preResult <- L.foldl' (doKeyMatch m a) (return mempty) (keys m)
  L.foldl' f (return preResult) (keys a)
    where
      step k r acc req = do
                    case KM.lookup k a of
                      -- KeyOpt means key might be missing
                      Nothing -> if req
                                      then noMatch $ "Required key " ++ (T.pack $ show k) ++ " not found in map"
                                      else return $ first (KM.insert k r) acc
                      -- if it exists, it must match
                      Just n -> MatchStatusT $ do
                        rr <- runMatchStatusT $ fa =<< matchPattern' fa r n
                        return $ case rr of
                             NoMatch s -> NoMatch s
                             MatchFailure s -> MatchFailure s
                             MatchSuccess s -> return $ second (KM.insert k el) acc
                                where
                                  el = if req then (KeyReq $ s) else (KeyOpt $ s)
      doKeyMatch m a acc' k = do
        acc <- acc'
        v <- (m2mst $ matchFailure "impossible") (KM.lookup k m)
        case v of
            KeyReq r -> step k r acc True
            KeyOpt r -> step k r acc False
            KeyExt _ -> matchFailure "malformed grammar: KeyExt cannot be here"
      f acc' k = do
            acc <- acc'
            case KM.member k m of
                 True -> return acc
                 False -> case keepExt of
                               False -> noMatch $ ("extra key in arg: " ++ T.pack (show k))
                               True -> case KM.lookup k a of
                                            Nothing -> matchFailure "impossible"
                                            Just v -> return $ second (KM.insert k (KeyExt v)) acc

matchPattern' fa (MatchObjectFull m) (Object a) = (fmap $ uncurry MatchObjectFullResultF) (mObj fa False m a)
matchPattern' fa (MatchObjectPartial m) (Object a) = (fmap $ uncurry MatchObjectPartialResultF) (mObj fa True m a)


matchPattern' fa (MatchObjectWithDefaults m d) (Object a) = do
  let f acc' (k, v) = do
          acc <- acc' -- (mm, dd)
          if KM.member k m
            then
                do
                  m' <- (m2mst $ matchFailure "impossible") $ KM.lookup k m
                  rr <- fa =<< matchPattern' fa m' v
                  return $ first (KM.insert k rr) acc
            else
              if KM.member k d
                then
                  do
                    d' <- (m2mst $ matchFailure "impossible") $ KM.lookup k d
                    let ff = if v /= d'
                              then KM.insert k v
                              else id
                    return $ second ff acc
                else noMatch $ "extra key: " ++ T.pack (show k)
  (mm, vv) <- L.foldl' f (return mempty) $ KM.toList a
  return $ MatchObjectWithDefaultsResultF mm d vv


matchPattern' fa (MatchObjectOnly m) (Object a) = do
  let f acc' (k, v) = do
          acc <- acc' -- (mm, dd)
          case KM.lookup k a of
            Just a' ->
                do
                  rr <- fa =<< matchPattern' fa v a'
                  return $ (KM.insert k rr) acc
            Nothing -> noMatch ("Required key " ++ (K.toText k) ++ " not found in object")
  mm <- L.foldl' f (return mempty) $ KM.toList m
  vv <- return $ (KM.filterWithKey (\k _ -> not $ KM.member k m)) a
  return $ MatchObjectOnlyResultF mm vv


matchPattern' fa (MatchObjectWhole m) (Object a) = do
  let f acc' (k, v) = do
          acc <- acc' -- (mm, dd)
          rr <- fa =<< matchPattern' fa m v
          return $ (KM.insert k rr) acc
  mm <- L.foldl' f (return mempty) $ KM.toList a
  return $ MatchObjectWholeResultF mm


matchPattern' fa (MatchOmitField fname m) (Object a) = do
  b <- return $ KM.delete fname a
  matchPattern' fa m (Object b)


matchPattern' fa (MatchSelectFields fnames m) (Object a) = do
  b <- return $ KM.filterWithKey (\k _ -> P.elem k fnames) a
  matchPattern' fa m (Object b)


--matchPattern' fa (MatchRegroup m) a = matchPattern' fa m a -- trivial


{-matchPattern' fa (MatchFork fnames m) (Object a) = do
  b <- return $ KM.filterWithKey (\k _ -> P.elem k fnames) a
  matchPattern' fa m (Object b)-}


matchPattern' fa (MatchArrayContextFree m) (Array a) = MatchStatusT $ do
  rr <- runMatchStatusT $ contextFreeMatch m a (\p v -> fa =<< matchPattern' fa p v)
  return $ case rr of
       NoMatch e -> NoMatch ("context-free nomatch!!: " ++ e ++ "\n\n" ++ (T.pack $ show m) ++ "\n\n" ++ (T.pack $ show a))
       MatchFailure s -> MatchFailure s
       MatchSuccess x -> MatchSuccess (MatchArrayContextFreeResultF x)

matchPattern' fa (MatchArrayContextFree m) (Object a) = noMatch ("object in cf:\n\n" ++ (TL.toStrict . TL.decodeUtf8 . encode $ m) ++ "\n\n" ++ (TL.toStrict . TL.decodeUtf8 . encode $ toJSON $ a))

matchPattern' fa (MatchArrayOnly m) (Array a) = do
  let f acc' e = do
        acc <- acc'
        MatchStatusT $ do
          rr <- runMatchStatusT $ fa =<< matchPattern' fa m e
          return $ case rr of
              MatchFailure e -> MatchFailure e
              MatchSuccess s -> MatchSuccess $ bimap (\v -> V.snoc v s) (\v -> V.snoc v Nothing) acc
              NoMatch _ -> MatchSuccess $ second (\v -> V.snoc v (Just e)) acc
  (r, v) <- L.foldl' f (return mempty) (V.toList a)
  return $ if P.null r
              then MatchArrayOnlyResultEmptyF m (catMaybes v)
              else MatchArrayOnlyResultSomeF r v

matchPattern' fa MatchFunnel v = return $ MatchFunnelResultF v

matchPattern' fa MatchFunnelKeys (Object v) = return $ MatchFunnelKeysResultF $ v
matchPattern' fa MatchFunnelKeys _ = matchFailure "MatchFunnelKeys met not an Object"

matchPattern' fa MatchFunnelKeysU (Object v) = return $ MatchFunnelKeysUResultF $ v
matchPattern' fa MatchFunnelKeysU _ = matchFailure "MatchFunnelKeysU met not an Object"

matchPattern' fa (MatchIfThen baseMatch failMsg match) v = MatchStatusT $ do
  rr <- runMatchStatusT $ fa =<< matchPattern' fa baseMatch v
  case rr of
       NoMatch x -> return $ NoMatch x
       MatchFailure f -> return $ MatchFailure f
       MatchSuccess _ -> do
          rr' <- runMatchStatusT $ fa =<< matchPattern' fa match v
          return $ case rr' of
               NoMatch x -> MatchFailure (failMsg ++ (T.pack $ show x))
               MatchFailure f -> MatchFailure f
               MatchSuccess s -> MatchSuccess (MatchIfThenResultF baseMatch failMsg s)

matchPattern' fa MatchAny a = return $ MatchAnyResultF a
matchPattern' fa MatchNone a = return $ MatchNoneResultF a
matchPattern' fa (MatchOr ms) v = do
  let f (k, a) b = MatchStatusT $ do
                rr <- runMatchStatusT $ fa =<< matchPattern' fa a v
                runMatchStatusT $ case rr of
                     MatchSuccess x -> return (k, x)
                     MatchFailure f -> matchFailure f
                     _ -> b
  (k, res) <- P.foldr f (noMatch "or fail") (KM.toList ms)
  return $ MatchOrResultF (KM.delete k ms) k res

matchPattern' fa (MatchNot ms) v = MatchStatusT $ do
  rr <- runMatchStatusT $ fa =<< matchPattern' fa ms v
  return $ case rr of
       MatchSuccess x -> NoMatch $ "Not fail: (can't show)" -- ++ (T.pack $ show x)
       MatchFailure f -> MatchFailure f
       NoMatch s -> return $ MatchNotResultF ms v

matchPattern' fa (MatchAnd ms' ms) v = do
  s' <- fa =<< matchPattern' fa ms' v
  s <- fa =<< matchPattern' fa ms v
  return $ MatchAndResultF s' s


matchPattern' fa (MatchArrayOr ms) (Array arr) = do
  let h acc' e = do
        acc <- acc'
        MatchStatusT $ do
          rr <- runMatchStatusT $ fa =<< matchPattern' fa (MatchOr ms) e
          return $ case rr of
             MatchSuccess s -> MatchSuccess $ V.snoc acc s
             MatchFailure err -> MatchFailure err
             NoMatch err -> MatchSuccess $ acc
  r <- L.foldl' h (return []) (V.toList arr)
  let inner = if P.null r
                 then StarNodeEmpty $ Char $ MatchOr ms
                 else StarNodeValue $ fmap CharNode r
  return $ MatchArrayContextFreeResultF $ SeqNode [inner]

matchPattern' fa (MatchArray ms) (Array []) = do
  return $ MatchArrayContextFreeResultF $ SeqNode [StarNodeEmpty $ Char $ ms]

matchPattern' fa (MatchArray ms) (Array arr) = do
  rEnv <- MatchStatusT $ do
    v <- ask
    return $ return v
  rr <- liftIO $ mapConcurrently (\x -> ff1 fa ms rEnv x) arr
  rr <- P.traverse (\x -> MatchStatusT $ ReaderT (const x)) rr
  return $ MatchArrayContextFreeResultF $ SeqNode [StarNodeValue $ fmap CharNode rr]

-- specific (aka exact)
matchPattern' fa (MatchStringExact m) (String a) = if m == a then return $ MatchStringExactResultF a else noMatch ("string mismatch: expected " ++ (T.pack $ show m) ++ " but found " ++ (T.pack $ show a))
matchPattern' fa (MatchStringRegExp m) (String a) =
  if a =~ m
     then return $ MatchStringRegExpResultF m a
     else noMatch ("string regexp mismatch: expected " ++ (T.pack $ show m) ++ " but found " ++ (T.pack $ show a))
matchPattern' fa (MatchNumberExact m) (Number a) = if m == a then return $ MatchNumberExactResultF a else noMatch ("number mismatch: expected " ++ (T.pack $ show m) ++ " but found " ++ (T.pack $ show a))
matchPattern' fa (MatchBoolExact m) (Bool a) = if m == a then return $ MatchBoolExactResultF a else noMatch ("bool mismatch: expected " ++ (T.pack $ show m) ++ " but found " ++ (T.pack $ show a))
-- any (of a type)
matchPattern' fa MatchStringAny (String a) = return $ MatchStringAnyResultF a
matchPattern' fa MatchNumberAny (Number a) = return $ MatchNumberAnyResultF a
matchPattern' fa MatchBoolAny (Bool a) = return $ MatchBoolAnyResultF a
-- null is just null
matchPattern' fa MatchNull Null = return MatchNullResultF
-- refs, finally :-)
matchPattern' fa (MatchRef r) v = do
  g <- MatchStatusT $ do
    v <- asks grammarMap
    return $ return v
  p <- (m2mst $ matchFailure $ ("Non-existant ref: " ++ r)) $ KM.lookup (K.fromText r) g
  a <- fa =<< matchPattern' fa p v
  return $ MatchRefResultF r a

-- wow
{-
matchPattern' fa (MatchFromMongoDB db collection r) v = do
  --  TODO operate on Text for db etc
  v <- (m2mst $ matchFailure "MongoDB should see ObjectId") $ asString v
  -- XXX temporary

  --let words = wordsWhen (=='.') $ T.unpack va
  --if P.length words == 3 then return () else matchFailure "MongoDB should see a string <database>.<collection>.<ObjectId>"
  --let [db, collection, objectId] = (fmap T.pack words)
  let objectId = v
  pipe <- liftIO $ MongoDB.connect $ MongoDB.host "127.0.0.1"
  let run act = liftIO $ MongoDB.access pipe MongoDB.master db act
  --liftIO $ putStrLn $ "DB is: " ++ (T.unpack db)
  --liftIO $ putStrLn $ "Coll is: " ++ (T.unpack collection)
  --liftIO $ putStrLn $ "Id is: " ++ (T.unpack objectId)
  vv' <- run $ MongoDB.findOne $ MongoDB.select ["_id" MongoDB.=: objectId] collection
  vv <- (m2mst $ matchFailure $ "MongoDB Id not found: " ++ T.unpack v) vv'
  vx <- return $ toAeson vv
  --liftIO $ putStrLn $ "Read from db ok"
  rr <- fa =<< matchPattern' fa r (Object vx) -- one option is this
  --liftIO $ putStrLn $ "Match from db ok"
  --liftIO $ print rr
  let jj = toJSON rr
  kx <- (m2mst $ matchFailure "impossible12312344") $ asKeyMap jj
  let km = KM.insert (fromText "_id") (String objectId) kx
  let vvv = ((toBson km) :: MongoDB.Document)
  let resultsCollection = T.concat [collection, "Results"]
  kk <- liftIO $ MongoDB.access pipe MongoDB.master db $ MongoDB.insert resultsCollection vvv
  --liftIO $ putStrLn $ "Insert doc: " ++ (T.pack $ show kk)
  return $ MatchFromMongoDBResultF db collection (T.pack $ show kk) -- TODO better conversion?


matchPattern' fa (MatchFromRedis db collection r) v = do
  --  TODO operate on Text for db etc
  va <- (m2mst $ matchFailure "Redis should see ObjectId") $ asString v
  -- XXX temporary

  --lift $ asks redisConn
  -- MatchStatusT (ReaderT MatcherEnv m (MatchStatus a))
  -- runMatchStatusT
  -- ReaderT MatcherEnv m (MatchStatus a)
  -- runReaderT
  -- MatcherEnv -> m (MatchStatus a)
  conn <- MatchStatusT $ do
    a <- asks redisConn
    return $ (return a)

  --liftIO $ print c
  let dataKey = T.encodeUtf8 $ T.concat [db, ":", collection, ":", va]
  let resultKey = T.encodeUtf8 $ T.concat [db, ":", collection, "Results:", va]
  v <- liftIO $ Redis.runRedis conn $ do
     hello <- Redis.get $ dataKey
     return $ hello
  v' <- case v of
    Left e -> matchFailure "redis fail"
    Right e -> return e
  v'' <- case v' of
    Nothing -> matchFailure "redis fail"
    Just e -> return e
  vr <- case decode $ BL.fromStrict v'' of
    Nothing -> matchFailure "decode fail"
    Just e -> return (e :: Value)
  --liftIO $ print vr

  rr <- fa =<< matchPattern' fa r vr
  --liftIO $ putStrLn $ "Match from db ok"
  --liftIO $ print rr

  kv <- liftIO $ Redis.runRedis conn $ do
     hello <- Redis.set resultKey (BL.toStrict $ encode rr)
     return $ hello
  kv' <- case kv of
    Left e -> matchFailure "redis fail"
    Right e -> return e

  return $ MatchFromRedisResultF db collection va-}

matchPattern' fa (MatchGetFromRedis db collection r) v = do
  --  TODO operate on Text for db etc
  va <- (m2mst $ matchFailure "Redis should see ObjectId") $ asString v
  -- XXX temporary

  --lift $ asks redisConn
  -- MatchStatusT (ReaderT MatcherEnv m (MatchStatus a))
  -- runMatchStatusT
  -- ReaderT MatcherEnv m (MatchStatus a)
  -- runReaderT
  -- MatcherEnv -> m (MatchStatus a)
  conn <- MatchStatusT $ do
    a <- asks redisConn
    return $ (return a)

  let dataKey = T.encodeUtf8 $ T.concat [db, ":", collection, ":", va]
  let resultKey = T.encodeUtf8 $ T.concat [db, ":", collection, "Results:", va]
  v <- liftIO $ Redis.runRedis conn $ do
     hello <- Redis.get $ dataKey
     return $ hello
  v' <- case v of
    Left e -> matchFailure "redis fail"
    Right e -> return e
  v'' <- case v' of
    Nothing -> matchFailure "redis fail"
    Just e -> return e
  vr <- case decode $ BL.fromStrict v'' of
    Nothing -> matchFailure "decode fail"
    Just e -> return (e :: Value)

  liftIO $ print $ "read: " ++ va
  matchPattern' fa r vr

matchPattern' fa (MatchGetFromFile filename r) v = do
  fdata <- liftIO $ ((fmap decode $ BL.readFile (T.unpack filename)) :: IO (Maybe Value))
  vr <- case fdata of
    Just x -> return x
    Nothing -> matchFailure "can't decode file"
    

  matchPattern' fa r vr

matchPattern' fa (MatchGetFromIORef m) v = do
  va <- (m2mst $ matchFailure "Redis should see ObjectId") $ asString v
  ref <- MatchStatusT $ do
    a <- asks dataRef
    return $ (return a)

  v <- liftIO $ readIORef ref

  vr <- case KM.lookup (fromText va) v of
    Just x -> return x
    _ -> matchFailure "ref error"

  matchPattern' fa m vr

-- default ca
matchPattern' fa m a = noMatch ("bottom reached:\n" ++ (T.pack $ show m) ++ "\n" ++ (T.pack $ show a))

matchPattern'' :: (Show r, MonadIO m) => (MatchResultF r -> MatchStatusT m r) -> MatchPattern -> Value -> MatchStatusT m r
matchPattern'' fma p v = fma =<< matchPattern' fma p v

traceFAlgebra :: MonadIO m => MatchResultF MatchResult -> MatchStatusT m MatchResult
traceFAlgebra x = do
  let e = embed x
  liftIO $ print $ matchResultToPattern e
  liftIO $ BL.putStr $ encode $ matchResultToValue e
  liftIO $ print ""
  liftIO $ print ""
  return $ e

-- MatchResultF a2 -> a2
-- TODO: better playaround with recursion schemes
matchToFunnel :: MonadIO m => MatchPattern -> Value -> MatchStatusT m (V.Vector Value)
matchToFunnel = matchPattern'' gatherFunnelFAlgebra

matchPattern :: MonadIO m => MatchPattern -> Value -> MatchStatusT m MatchResult
matchPattern = matchPattern'' $ return . embed

matchToThin :: MonadIO m => MatchPattern -> Value -> MatchStatusT m (Maybe Value)
matchToThin = matchPattern'' matchResultToThinValueFAlgebra

--ff1 :: (MatchResultF r -> MatchStatusT m r) -> MatchPattern -> MatcherEnv -> Value -> IO (MatchStatus r)
ff1
  :: (Show a, MonadIO m) =>
     (MatchResultF a -> MatchStatusT m a)
     -> MatchPattern -> MatcherEnv -> Value -> IO (m (MatchStatus a))
ff1 fa ms rEnv x = do
    --print "foo"
    x <- liftIO $ return $ runReaderT (runMatchStatusT $ matchPattern'' fa ms x) rEnv
    return x

--contextFreeGrammarResultToGrammar :: (MatchResult -> MatchPattern) -> (ContextFreeGrammarResult (ContextFreeGrammar MatchPattern) MatchResult) -> (ContextFreeGrammar MatchPattern)
--contextFreeGrammarResultToGrammar :: (r -> p) -> (ContextFreeGrammarResult (ContextFreeGrammar p) r) -> (ContextFreeGrammar p)
--contextFreeGrammarResultToGrammar :: (Data.Functor.Foldable.Recursive t1, Data.Functor.Foldable.Base t1 ~ ContextFreeGrammarResultF a t2) => (t2 -> a) -> t1 -> ContextFreeGrammar a
contextFreeGrammarResultToGrammarAlg f = go
  where
    --go :: ContextFreeGrammarResultF (ContextFreeGrammar p) r (ContextFreeGrammar p) -> ContextFreeGrammar p
    go (CharNodeF r) = Char (f r)
    go (SeqNodeF r) = Seq r
    go (StarNodeEmptyF g) = Star g
    go (StarNodeValueF r) = Star (V.head r)
    go (StarNodeIndexedF r _) = Star (V.head r)
    go (PlusNodeF r) = Plus (V.head r)
    go (PlusNodeIndexedF r _) = Plus (V.head r)
    go (OrNodeF g k r) = Or (KM.insert k r g)
    go (OptionalNodeValueF r) = Optional r
    go (OptionalNodeEmptyF g) = Optional g

contextFreeGrammarResultToGrammar f = cata $ contextFreeGrammarResultToGrammarAlg f
  where

contextFreeGrammarResultToSource :: (r -> a) -> ContextFreeGrammarResult g r -> (V.Vector a)
contextFreeGrammarResultToSource f = cata go
  where
    go (CharNodeF r) = [f r]
    go (SeqNodeF r) = vconcat r
    go (StarNodeEmptyF g) = []
    go (StarNodeValueF r) = vconcat r
    go (StarNodeIndexedF r _) = vconcat r
    go (PlusNodeF r) = vconcat r
    go (PlusNodeIndexedF r _) = vconcat r
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
    go (OrNodeF g k r) = [V.concat r]
    go (OptionalNodeValueF r) = [V.concat r]
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
  go (MatchArrayOnlyResultEmptyF g v) = MatchArrayOnly g
  go (MatchArrayOnlyResultSomeF r v) = MatchArrayOnly $ V.head r
  go (MatchStringExactResultF r) = MatchStringExact r
  go (MatchStringRegExpResultF e r) = MatchStringRegExp e
  go (MatchNumberExactResultF r) = MatchNumberExact r
  go (MatchBoolExactResultF r) = MatchBoolExact r
  go (MatchStringAnyResultF r) = MatchStringAny
  go (MatchNumberAnyResultF r) = MatchNumberAny
  go (MatchBoolAnyResultF r) = MatchBoolAny
  go MatchNullResultF = MatchNull
  go (MatchAnyResultF r) = MatchAny
  go (MatchNoneResultF r) = MatchNone
  go (MatchOrResultF m k r) = MatchOr (KM.insert k r m)
  go (MatchNotResultF m _) = MatchNot m
  go (MatchAndResultF r' r) = MatchAnd r' r
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
    go (MatchArrayContextFreeResultF r) = Array $ contextFreeGrammarResultToSource id r
    go (MatchArrayOnlyResultEmptyF g v) = Array $ v
    go (MatchArrayOnlyResultSomeF r v) = rr
      where
        f (r, rr) e = case e of
                               Just x -> (r, V.snoc rr x)
                               Nothing -> let q = V.head r; qq = V.tail r in (qq, V.snoc rr q)
        (_, vv) = L.foldl' f (r, []) v
        rr = Array vv
    go (MatchStringExactResultF r) = String r
    go (MatchStringRegExpResultF m r) = String r
    go (MatchNumberExactResultF r) = Number r
    go (MatchBoolExactResultF r) = Bool r
    go (MatchStringAnyResultF r) = String r
    go (MatchNumberAnyResultF r) = Number r
    go (MatchBoolAnyResultF r) = Bool r
    go MatchNullResultF = Null
    go (MatchAnyResultF r) = r
    go (MatchNoneResultF r) = r
    go (MatchOrResultF m k r) = r
    go (MatchNotResultF m v) = v
    go (MatchAndResultF r' r) = r
    go (MatchIfThenResultF p errorMsg r) = r
    go (MatchFunnelResultF r) = r
    go (MatchFunnelKeysResultF r) = Object r
    go (MatchFunnelKeysUResultF r) = Object r
    go (MatchRefResultF ref r) = r

valueToExactGrammar :: Value -> MatchPattern
valueToExactGrammar = cata go
  where
    go (ObjectF a) = MatchObjectWithDefaults a mempty
    go (ArrayF a) = MatchArrayContextFree $ Seq $ fmap Char a
    go (StringF a) = MatchStringExact a
    go (NumberF a) = MatchNumberExact a
    go (BoolF a) = MatchBoolExact a
    go NullF = MatchNull

--valueToExactResult :: MonadIO m => Value -> MatchStatusT m MatchResult
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

contextFreeGrammarIsWellFormed :: (Monad m, Show a) => (a -> m Bool) -> ContextFreeGrammar a -> m Bool
contextFreeGrammarIsWellFormed f = paraM goM
  where
    --go :: Show a => ContextFreeGrammarF a (ContextFreeGrammar a, Bool) -> Bool
    goM (CharF c) = f c
    goM x = return $ go x

    go (SeqF a) = P.all id (fmap snd a)
    go (OrF a) = P.all id (fmap snd (KM.elems a))
    go (StarF (p, a)) = (not (isStarLike p)) && a
    go (PlusF (p, a)) = (not (isStarLike p)) && a
    go (OptionalF (p, a)) = (not (isStarLike p)) && a

-- is well-formed

matchPatternIsWellFormed :: MonadIO m => MatchPattern -> MatchStatusT m Bool
matchPatternIsWellFormed = cataM goM
  where
    goM (MatchRefF r) = do
      g <- MatchStatusT $ do
        v <- asks grammarMap
        return $ return v
      p <- (m2mst $ matchFailure $ "Non-existant ref: " ++ r) $ KM.lookup (K.fromText r) g
      matchPatternIsWellFormed p
    goM (MatchArrayContextFreeF g) = if not $ isSeq g
                                        then return $ False
                                        else contextFreeGrammarIsWellFormed return g
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
    go (MatchArrayOnlyF g) = g
    go (MatchStringExactF _) = True
    go (MatchStringRegExpF e) = True
    go (MatchNumberExactF _) = True
    go (MatchBoolExactF _) = True
    go MatchStringAnyF = True
    go MatchNumberAnyF = True
    go MatchBoolAnyF = True
    go MatchNullF = True
    go MatchAnyF = True
    go MatchNoneF = True
    go (MatchOrF g) = P.all id (KM.elems g)
    go (MatchNotF g) = g
    go (MatchAndF g' g) = g' && g
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

allTheSame v = if V.null v then True
                           else let h = V.head v in V.foldl (\a e -> a && (e == h)) True v

--contextFreeGrammarResultIsWellFormed :: (Show g, Show r) => (g -> Bool) -> (r -> Bool) -> ContextFreeGrammarResult g r -> Bool
--contextFreeGrammarResultIsWellFormed :: (Show g, Show r) => (g -> Bool) -> (r -> Bool) -> ContextFreeGrammarResult g r -> Bool
contextFreeGrammarResultIsWellFormed :: (Monad m) => (MatchPattern -> m Bool) -> (Bool -> m Bool) -> ContextFreeGrammarResult MatchPattern (MatchResult, Bool) -> m Bool
contextFreeGrammarResultIsWellFormed gf rf = paraM goM
  where
    --go :: ContextFreeGrammarResultF MatchPattern MatchResult (MatchResult, m Bool) -> m Bool
    goM (CharNodeF (_, r)) = rf r
    goM (StarNodeEmptyF g) = contextFreeGrammarIsWellFormed gf g
    goM (OrNodeF g k (_, r)) = a
      where
        a = do
          v <- P.traverse (contextFreeGrammarIsWellFormed gf) (KM.elems g)
          return $ P.all id v && (not $ KM.member k g) && r
    goM (OptionalNodeEmptyF g) = contextFreeGrammarIsWellFormed gf g
    goM x = return $ go x

    go (SeqNodeF r) = P.all id (fmap snd r)
    go (StarNodeValueF r) =
      (not $ isStarNodeLike (fst $ V.head r))
      && (snd $ V.head r)
      && (allTheSame $ (fmap (contextFreeGrammarResultToGrammar (matchResultToPattern . fst))) $ (fmap fst r))
    go (PlusNodeF r) =
      (not $ isStarNodeLike (fst $ V.head r))
      && (snd $ V.head r)
      && (allTheSame $ (fmap (contextFreeGrammarResultToGrammar (matchResultToPattern . fst))) $ (fmap fst r))
    go (OptionalNodeValueF r) = (not $ isStarNodeLike (fst r)) && (snd r)

matchResultIsWellFormed :: MonadIO m => MatchResult -> MatchStatusT m Bool
matchResultIsWellFormed = paraM checkM
  where
    checkM (MatchArrayOnlyResultEmptyF g v) = matchPatternIsWellFormed g
    checkM (MatchArrayOnlyResultSomeF g v) = return $ P.all snd g
    checkM (MatchObjectFullResultF g r) = a
      where
        f acc (KeyOpt (_, x)) = acc && x
        f acc (KeyReq (_, x)) = acc && x
        f acc (KeyExt _) = False
        rc = L.foldl' f True (KM.elems r)
        nck = S.null $ S.intersection (S.fromList $ KM.keys g) (S.fromList $ KM.keys r)
        a = do
          gc' <- sequenceA $ fmap matchPatternIsWellFormed (KM.elems g)
          let gc = P.all id gc'
          return $ gc && rc && nck
    checkM (MatchObjectPartialResultF g r) = a
      where
        f acc (KeyOpt (_, x)) = acc && x
        f acc (KeyReq (_, x)) = acc && x
        f acc (KeyExt _) = False
        rc = L.foldl' f True (KM.elems r)
        nck = S.null $ S.intersection (S.fromList $ KM.keys g) (S.fromList $ KM.keys r)
        a = do
          gc' <- sequenceA $ fmap matchPatternIsWellFormed (KM.elems g)
          let gc = P.all id gc'
          return $ gc && rc && nck
    checkM (MatchArrayContextFreeResultF g) = contextFreeGrammarResultIsWellFormed matchPatternIsWellFormed return g
    checkM (MatchOrResultF g k (_, r)) = a
      where
        a = do                                      
          v <- P.traverse matchPatternIsWellFormed (KM.elems g)
          return $ P.all id v && (not $ KM.member k g) && r
    checkM x = return $ check x

    check (MatchRefResultF ref (_, r)) = r
    check (MatchStringExactResultF _) = True
    check (MatchNumberExactResultF _) = True
    check (MatchBoolExactResultF _) = True
    check (MatchStringAnyResultF _) = True
    check (MatchNumberAnyResultF _) = True
    check (MatchBoolAnyResultF _) = True
    check MatchNullResultF = True
    check (MatchAnyResultF _) = True
    check (MatchNoneResultF _) = True
    check (MatchIfThenResultF _ _ _) = False -- TODO
    check (MatchFunnelResultF _) = True
    check (MatchFunnelKeysResultF _) = True
    check (MatchFunnelKeysUResultF _) = True

-- is movable


contextFreeGrammarIsMovable :: MonadIO m => (a -> MatchStatusT m Bool) -> ContextFreeGrammar a -> MatchStatusT m Bool
contextFreeGrammarIsMovable f = cataM go'
  where
    go' (CharF a) = f a
    go' x = return $ go x

    go (SeqF a) = P.any id a
    go (OrF a) = True --P.any id (KM.elems a)
    go (StarF a) = True
    go (PlusF a) = True
    go (OptionalF a) = True

contextFreeGrammarResultIsMovable :: (MonadIO m) => (g -> m Bool) -> (r -> m Bool) -> ContextFreeGrammarResult g r -> m Bool
contextFreeGrammarResultIsMovable gf rf = cataM go'
  where
    go' (CharNodeF r) = rf r
    go' x = return $ go x

    go (SeqNodeF r) = P.any id r
    go (StarNodeEmptyF g) = True
    go (StarNodeValueF r) = True
    go (PlusNodeF r) = True
    go (OrNodeF g k r) = True -- r || P.any (contextFreeGrammarIsMovable gf) (KM.elems g)
    go (OptionalNodeValueF r) = True
    go (OptionalNodeEmptyF g) = True

liftObjectKeyMatch :: (KeyMap (ObjectKeyMatch (MatchStatus a))) -> MatchStatus (KeyMap (ObjectKeyMatch a))
liftObjectKeyMatch m = L.foldl' f (MatchSuccess mempty) (KM.keys m)
  where --f :: (MatchStatus (KeyMap (ObjectKeyMatch a))) -> Key -> (MatchStatus (KeyMap (ObjectKeyMatch a)))
        f acc' k = do
          acc <- acc'
          v <- (m2ms $ MatchFailure "impossible") $ KM.lookup k m
          case v of
               --KeyExt (MatchSuccess x) -> KM.insert k (KeyExt x) acc
               KeyOpt (MatchSuccess x) -> return $ KM.insert k (KeyOpt x) acc
               KeyReq (MatchSuccess x) -> return $ KM.insert k (KeyReq x) acc
               KeyOpt (MatchFailure s) -> MatchFailure s
               KeyReq (MatchFailure s) -> MatchFailure s
               KeyOpt (NoMatch s) -> NoMatch s
               KeyReq (NoMatch s) -> NoMatch s


matchPatternIsMovable :: MonadIO m => MatchPattern -> MatchStatusT m Bool
matchPatternIsMovable = cataM goM
  where
    goM (MatchRefF r) = do
      g <- MatchStatusT $ do
        v <- asks grammarMap
        return $ return v
      p <- (m2mst $ matchFailure $ "Non-existant ref: " ++ r) $ KM.lookup (K.fromText r) g
      --matchPatternIsMovable g p
      return $ True --ehhh
    goM (MatchArrayContextFreeF g) = contextFreeGrammarIsMovable return g
    goM x = return $ go x

    go (MatchObjectFullF g) = L.foldl' f False (KM.elems g)
      where
        f acc (KeyOpt _) = True
        f acc (KeyReq x) = x || acc
        f acc (KeyReq x) = error $ "must not be here"
    go (MatchObjectWithDefaultsF g _) = getAny $ mconcat $ P.map Any (KM.elems g)
    go (MatchObjectOnlyF g) = getAny $ mconcat $ P.map Any (KM.elems g)
    go (MatchObjectPartialF g) = True -- may have ext --P.any (extractObjectKeyMatch $ error "must not be here") (KM.elems g)
    go (MatchArrayOnlyF g) = True
    go (MatchStringExactF _) = False
    go (MatchStringRegExpF _) = True
    go (MatchNumberExactF _) = False
    go (MatchBoolExactF _) = False
    go MatchStringAnyF = True
    go MatchNumberAnyF = True
    go MatchBoolAnyF = True
    go MatchNullF = False
    go MatchAnyF = True
    go MatchNoneF = False
    go (MatchOrF g) = True --P.any id (KM.elems g)
    go (MatchNotF _) = True
    go (MatchAndF g' g) = g' || g
    go (MatchIfThenF _ _ g) = g
    go MatchFunnelF = True
    go MatchFunnelKeysF = True
    go MatchFunnelKeysUF = True

isKeyReq (KeyReq _) = True
isKeyReq _ = False

getKeyReqs :: (V.Vector (ObjectKeyMatch b)) -> (V.Vector b)
getKeyReqs xs = fmap (extractObjectKeyMatch $ error "must not be here697") $ V.filter isKeyReq xs

isKeyOpt (KeyOpt _) = True
isKeyOpt _ = False

getKeyOpts :: (V.Vector (ObjectKeyMatch b)) -> (V.Vector b)
getKeyOpts xs = fmap (extractObjectKeyMatch $ error "must not be here703") $ V.filter isKeyOpt xs

matchResultIsMovable :: MonadIO m => MatchResult -> MatchStatusT m Bool
matchResultIsMovable r = matchPatternIsMovable (matchResultToPattern r)


-- Thick/Thin stuff

tMapK1 k = Object $ KM.fromList [(K.fromText "k", k2s k)]
tMapKV1 k v = Object $ KM.fromList [(K.fromText "k", k2s k), (K.fromText "v", v)]

int2sci :: Integral a => a -> Value
int2sci x = Number $ Sci.scientific (toInteger x) 0

enumerate :: (V.Vector Value) -> (V.Vector Value) -- TODO optimize
enumerate a = V.fromList $ fmap (\(i, a) -> Array $ V.fromList [int2sci i, a]) $ P.zip [1..] (V.toList a)

contextFreeGrammarResultToThinValue :: MonadIO m => ContextFreeGrammarResult MatchPattern (Maybe Value) -> MatchStatusT m (Maybe Value)
contextFreeGrammarResultToThinValue a = do
  isIndexing <- MatchStatusT $ do
    v <- asks indexing
    return $ return v

  let
    doEnumerate = if isIndexing then enumerate else id
    gg = contextFreeGrammarIsMovable $ matchPatternIsMovable
    --go' :: ContextFreeGrammarResultF MatchPattern (Maybe Value) (Maybe Value) -> MatchStatus (Maybe Value)
    go' (StarNodeEmptyF g) = do
      c <- gg g
      return $ Just $ if c
                then Array $ V.fromList ([] :: [Value])
                else Number 0
    go' (OptionalNodeEmptyF g) = do
      c <- gg g
      return $ Just $ if not $ c
                            then Bool False
                            else Array $ V.fromList []
    go' x = return $ go x
    go (CharNodeF r) = r --fmap (tMap "Char") r
    go (SeqNodeF r) = let l = fmap fromJust $ V.filter isJust r in
      if V.null l
        then Nothing
        else if V.length l == 1
                then Just $ V.head l
                else Just $ Array l
    go (StarNodeValueF r) = Just $ if V.head r == Nothing -- aka grammar is trivial
                              then int2sci (V.length r)
                              else Array $ doEnumerate $ V.map fromJust r
    go (StarNodeIndexedF r _) = Just $ if V.head r == Nothing
                              then int2sci (V.length r)
                              else Array $ doEnumerate $ V.map fromJust r
    go (PlusNodeF r) = Just $ if V.head r == Nothing -- aka grammar is trivial
                              then int2sci (V.length r)
                              else Array $ doEnumerate $ V.map fromJust r
    go (PlusNodeIndexedF r _) = Just $ if V.head r == Nothing
                              then int2sci (V.length r)
                              else Array $ doEnumerate $ V.map fromJust r
    go (OrNodeF g k r) = Just $ if r == Nothing
                            then tMapK1 k
                            else tMapKV1 k (fromJust r)
    go (OptionalNodeValueF r) = Just $ if r == Nothing
                            then Bool True
                            else Array $ [(fromJust r)]
  cataM go' a


matchResultToThinValueFAlgebra :: MonadIO m => MatchResultF (Maybe Value) -> MatchStatusT m (Maybe Value)
matchResultToThinValueFAlgebra = goM
  where
    filterEmpty a = (KM.map fromJust (KM.filter isJust a))
    nonEmptyMap m = if KM.null m then Nothing else Just m
    replaceSingleton (Object m) = if (KM.size m) == 1 then P.head (KM.elems m) else Object m
    --goM :: MatchResultF (Maybe Value) -> MatchStatus (Maybe Value)
    goM (MatchObjectFullResultF g r) = u
      where
        f (KeyReq v) = v
        f (KeyOpt v) = case v of
                            Nothing -> Just $ Bool True
                            Just a -> Just a
        f (KeyExt _) = error "must not be here4"
        optf :: Bool -> Maybe Value
        optf x = case x of
                      True -> Nothing
                      False -> Just $ Bool False
        u = do
          g' <- P.traverse matchPatternIsMovable g
          let u' = KM.union (KM.map f r) (fmap optf g')
          return $ fmap (replaceSingleton . Object) $ nonEmptyMap $ filterEmpty $ u'
    goM (MatchObjectPartialResultF g r) = u
      where
        f (KeyReq v) = v
        f (KeyOpt v) = case v of
                            Nothing -> Just $ Bool True
                            Just a -> Just $ a
        f (KeyExt _) = error "must not be here5"
        ff (KeyReq v) = True
        ff (KeyOpt v) = True
        ff (KeyExt v) = False
        optf :: Bool -> Maybe Value
        optf x = case x of
                      True -> Just $ Bool True
                      False -> Just $ Bool False
        u = do
          g' <- P.traverse matchPatternIsMovable g
          let u' = KM.union (KM.map f (KM.filter ff r)) (fmap optf g')
          return $ fmap Object $ Just $ filterEmpty $ u'
    goM (MatchArrayContextFreeResultF r) = contextFreeGrammarResultToThinValue r
    goM (MatchObjectWithDefaultsResultF r d a) = goM (MatchObjectFullResultF (KM.empty) (fmap KeyReq r))
    goM x = return $ go x

    go :: MatchResultF (Maybe Value) -> Maybe Value
    go (MatchObjectOnlyResultF r v) = fmap (replaceSingleton . Object) $ nonEmptyMap $ filterEmpty $ r
    go (MatchArrayOnlyResultEmptyF g r) = Nothing
    go (MatchArrayOnlyResultSomeF g r) = Just $ Array $ catMaybes g -- TODO: when Nothing?
    go (MatchStringExactResultF r) = Nothing
    go (MatchStringRegExpResultF e r) = Just $ String r
    go (MatchNumberExactResultF r) = Nothing
    go (MatchBoolExactResultF r) = Nothing
    go (MatchStringAnyResultF r) = Just $ String r
    go (MatchNumberAnyResultF r) = Just $ Number r
    go (MatchBoolAnyResultF r) = Just $ Bool r
    go MatchNullResultF = Nothing
    go (MatchAnyResultF r) =  Just $ r
    go (MatchNoneResultF r) = Nothing
    go (MatchOrResultF g k r) = Just $ if r == Nothing
                                   then tMapK1 k
                                   else tMapKV1 k (fromJust r)
    go (MatchNotResultF g r) = Just $ r 
    go (MatchAndResultF r' r) = r
    go (MatchIfThenResultF p errorMsg r) = r
    go (MatchFunnelResultF r) = Just $ r
    go (MatchFunnelKeysResultF r) = Just $ Object r
    go (MatchFunnelKeysUResultF r) = Just $ Object r
    go (MatchRefResultF ref r) = r
    --go x = error $ (T.pack $ show x)
    go (MatchObjectFullResultF _ _) = error "MatchObjectFullResultF"
    go (MatchObjectPartialResultF _ _) = error "MatchObjectPartialResultF"
    go (MatchArrayContextFreeResultF _) = error "MatchArrayContextFreeResultF"
    go (MatchDefaultResultF _) = error "MatchDefaultResultF"


matchResultToThinValue :: MonadIO m => MatchResult -> MatchStatusT m (Maybe Value)
matchResultToThinValue = cataM matchResultToThinValueFAlgebra

-- thin pattern
or2 = (MatchOr (KM.fromList [(K.fromText "option1", (MatchNumberExact 1)), (K.fromText "option2", MatchNumberAny)]))


thinSeq as v = do
        gs <- P.traverse (contextFreeGrammarIsMovable matchPatternIsMovable) as
        v <- case P.length (V.filter id gs) of
                  0 ->
                    do
                      return $ []
                  1 ->
                    do
                      return $ [v]
                  _ ->
                    do
                      (m2mst $ matchFailure $ "data error10" ++ (T.pack $ show v)) $ asArray v
        let f acc' (a, gg) = do
                acc <- acc'
                (ii, acc) <- acc'
                let i = V.head ii; is = V.tail ii
                if gg -- movable
                  then fmap (\x -> (is, V.snoc acc x)) (thinContextFreeMatch a (Just i))
                  else fmap (\x -> (ii, V.snoc acc x)) (thinContextFreeMatch a Nothing)

        r <- V.foldl f (return (v, [])) $ V.zip as gs
        _ <- if V.null $ fst r then return () else matchFailure $ "not all consumed" ++ (T.pack $ show (fst r))
        return $ SeqNode (snd r)

throwAwayIndexes :: MonadIO m => MatchStatusT m (V.Vector Value) -> Value -> MatchStatusT m (V.Vector Value)
throwAwayIndexes err (Array a') = do
  a <- return $ V.toList a'
  let f acc' x = do
        acc <- acc'
        x' <- (m2mst err) $ asArray x
        -- array of pairs
        _ <- if V.length x' == 2 then return mempty else err
        return $ V.snoc acc (V.head $ V.tail $ x')
  L.foldl' f (return mempty) a
throwAwayIndexes err _ = err

getIndexes :: MonadIO m => MatchStatusT m a -> Value -> MatchStatusT m (V.Vector Int)
getIndexes ee (Array a') = do
  ee <- ee
  a <- return $ V.toList a'
  let f acc' x = do
        acc <- acc'
        x' <- (m2mst (matchFailure "index problem")) $ asArray x
        -- array of pairs
        _ <- if P.length x' == 2 then return ([] :: (V.Vector Int)) else (matchFailure "index problem")
        let i' :: Value
            i' = V.head x'
        i <- (m2mst $ (matchFailure "index problem")) $ asNumber i'
        return $ V.snoc acc (fromInteger $ Sci.coefficient i)
  L.foldl' f (return mempty) a
getIndexes _ _ = (matchFailure "index problem")

thinContextFreeMatch :: MonadIO m => ContextFreeGrammar MatchPattern -> Maybe Value -> MatchStatusT m (ContextFreeGrammarResult MatchPattern MatchResult)
thinContextFreeMatch (Char a) v = MatchStatusT $ do
  rr <- runMatchStatusT $ thinPattern a v
  runMatchStatusT $ case rr of
       NoMatch s -> noMatch ("no char match: " ++ s)
       MatchFailure s -> matchFailure ("thinContextFreeMatch: " ++ s)
       MatchSuccess r -> return $ CharNode r

thinContextFreeMatch (Seq as) Nothing = do
  vv <- contextFreeGrammarIsMovable matchPatternIsMovable (Seq as)
  if not $ vv
     then thinSeq as (Array [])
     else noMatch "data error5"
thinContextFreeMatch (Seq as) (Just v) = do
  vv <- contextFreeGrammarIsMovable matchPatternIsMovable (Seq as)
  if not $ vv
     then noMatch ("data error6:\n\n" ++ (T.pack $ show as) ++ "\n\n" ++ (T.pack $ show v) ++ "\n\n")
     else thinSeq as v

thinContextFreeMatch (Or ms) (Just (Object v)) = do -- or requires an exsistance of a value (Just)
  itsKey <- (m2mst $ matchFailure ("data error 951: " ++ (T.pack $ show v))) $ KM.lookup (K.fromText "k") v
  itsKey <- (m2mst $ matchFailure ("data error3" ++ (T.pack $ show itsKey))) $ asString itsKey
  let itsK = K.fromText itsKey
  itsMatch <- (m2mst $ matchFailure ("data error4" ++ (T.pack $ show ms))) $ KM.lookup itsK ms
  mch <- thinContextFreeMatch itsMatch (KM.lookup (K.fromText "v") v)
  return $ OrNode (KM.delete itsK ms) itsK mch

thinContextFreeMatch (Star a) (Just itsValue) = do
  --        _ :: (ContextFreeGrammar MatchPattern -> MatchStatusT m14 Bool)
  --             -> ContextFreeGrammar MatchPattern -> Bool
  gg <- contextFreeGrammarIsMovable matchPatternIsMovable a
  if gg
     then -- actual
        do
          is <- (getIndexes $ matchFailure ("data error2" ++ (T.pack $ show itsValue))) $ itsValue
          itsValue <- (throwAwayIndexes $ matchFailure ("data error2" ++ (T.pack $ show itsValue))) $ itsValue
          if P.null itsValue
             then
                return $ StarNodeEmpty a
             else
              do
                aa <- P.traverse (thinContextFreeMatch a) (fmap Just itsValue)
                return $ StarNodeIndexed aa is
      else -- trivial
        do
          itsValue <- (m2mst $ matchFailure ("data error2" ++ (T.pack $ show itsValue))) $ asNumber itsValue
          if itsValue == 0
             then
                return $ StarNodeEmpty $ a
              else
                do
                  aa' <- thinContextFreeMatch a Nothing
                  let aa = V.fromList $ P.take (fromIntegral $ Sci.coefficient itsValue) $ P.repeat aa'
                  return $ StarNodeValue aa

thinContextFreeMatch (Plus a) (Just itsValue) = do
  gg <- contextFreeGrammarIsMovable matchPatternIsMovable a
  if gg
     then -- actual
        do
          is <- (getIndexes $ matchFailure ("data error2" ++ (T.pack $ show itsValue))) $ itsValue
          itsValue <- (throwAwayIndexes $ matchFailure ("data error3" ++ (T.pack $ show itsValue))) $ itsValue
          aa <- P.traverse (thinContextFreeMatch a) (fmap Just itsValue)
          return $ PlusNodeIndexed aa is
      else -- trivial
        do
          itsValue <- (m2mst $ matchFailure ("data error4" ++ (T.pack $ show itsValue))) $ asNumber itsValue
          aa' <- thinContextFreeMatch a Nothing
          let aa = V.fromList $ P.take (fromIntegral $ Sci.coefficient itsValue) $ P.repeat aa'
          return $ PlusNode aa

thinContextFreeMatch (Optional a) (Just itsValue) = do
  gg <- contextFreeGrammarIsMovable matchPatternIsMovable a
  if gg
     then
      do
        itsValue <- (m2mst $ matchFailure ("data error1141" ++ (T.pack $ show itsValue))) $ asArray itsValue
        if not (P.null itsValue)
           then
            do
              r <- thinContextFreeMatch a (Just (V.head itsValue))
              return $ OptionalNodeValue r
           else return $ OptionalNodeEmpty a
     else
      do
        itsValue <- (m2mst $ matchFailure ("data error1144" ++ (T.pack $ show itsValue))) $ asBool itsValue
        if itsValue
           then
            do
              r <- thinContextFreeMatch a Nothing
              return $ OptionalNodeValue r
           else return $ OptionalNodeEmpty a

thinContextFreeMatch a xs = error $ T.unpack ("no match for: " ++ ((T.pack $ show a)) ++ " " ++ ((T.pack $ show xs)))

tObj :: MonadIO m => Bool -> KeyMap (ObjectKeyMatch MatchPattern) -> (KeyMap Value) -> MatchStatusT m (KeyMap MatchPattern, KeyMap (ObjectKeyMatch MatchResult))
tObj keepExt m a = do
  preResult <- L.foldl' (doKeyMatch m a) (return mempty) (keys m)
  L.foldl' f (return preResult) (keys a)
    where
      step k r acc req = case KM.lookup k a of
                      -- KeyOpt means key might be missing
                      Nothing -> if req
                                    then noMatch $ "Required key " ++ (T.pack $ show k) ++ " not found in map"
                                    else return $ first (KM.insert k r) acc
                      -- if it exists, it must match
                      Just n -> MatchStatusT $ do
                                rr <- runMatchStatusT $ thinPattern r (Just n)
                                runMatchStatusT $ case rr of
                                     NoMatch s -> noMatch s
                                     MatchFailure s -> matchFailure s
                                     MatchSuccess s -> return $ second (KM.insert k el) acc
                                        where
                                          el = if req then (KeyReq s) else (KeyOpt s)
      doKeyMatch m a acc' k = do
        acc <- acc'
        v <- (m2mst $ matchFailure "impossible") (KM.lookup k m)
        case v of
            KeyReq r -> step k r acc True
            KeyOpt r -> step k r acc False
            KeyExt _ -> matchFailure "malformed grammar: KeyExt cannot be here"
      f acc' k = do
            acc <- acc'
            case KM.member k m of
                 True -> return acc
                 False -> case keepExt of
                               False -> noMatch "extra key in arg"
                               True -> case KM.lookup k a of
                                            Nothing -> matchFailure "impossible"
                                            Just v -> return $ second (KM.insert k (KeyExt v)) acc


--thinPatternMap m a allowExt = undefined

thinPatternMap allowExt m a = do
  let f1 (KeyReq x) = matchPatternIsMovable x
      f1 (KeyOpt _) = return $ True
      f1 (KeyExt _) = error "must not be here1"
  ms <- P.sequence $ KM.map f1 m
  let mm = P.any id (KM.elems ms)

  let f2 (KeyReq x) = matchPatternIsMovable x
      f2 (KeyOpt x) = matchPatternIsMovable x
      f2 (KeyExt _) = error "must not be here2"
  vs <- P.sequence $ KM.map f2 m

  na <- case (KM.size (KM.filter id ms), allowExt) of
             (0, False) -> do
               case a of
                    Nothing -> return $ KM.empty
                    (Just x) -> matchFailure ("must not be here 1071: " ++ (T.pack $ show x))
             (1, False) -> do -- very special case (replaceSingleton)
                     aa <- (m2mst $ matchFailure ("must not be such 1073: " ++ (T.pack $ show a))) a
                     return $ KM.singleton (P.head (KM.keys (KM.filter id ms))) aa
             _ -> do
                     aa <- (m2mst $ matchFailure ("must not be such 1076: " ++ (T.pack $ show a))) a
                     (m2mst $ matchFailure ("must not be such 1077: " ++ (T.pack $ show a))) $ asKeyMap aa

  let f acc' k = do
        acc <- acc'
        mk <- (m2mst $ matchFailure "impossible") $ KM.lookup k vs
        v <- (m2mst $ matchFailure "impossible") $ KM.lookup k m
        case (v, mk) of
             -- trivial
             (KeyReq v, False) -> case KM.lookup k na of
                                       Nothing -> do
                                         e <- thinPattern v Nothing
                                         return $ second (KM.insert k $ KeyReq e) acc
                                       Just x -> matchFailure ("must not be here 1089: " ++ (T.pack $ show x))
             (KeyOpt v, False) -> do
               vv <- (m2mst $ matchFailure ("doesn't exist1" ++ (T.pack $ show na))) $ KM.lookup k na
               flg <- (m2mst $ matchFailure ("doesn't exist5" ++ (T.pack $ show vv))) $ asBool vv
               case flg of
                    False -> return $ first (KM.insert k v) acc
                    True -> do
                      e <- thinPattern v Nothing
                      return $ second (KM.insert k $ KeyOpt e) acc
             -- movable
             (KeyReq v, True) -> do
               case KM.lookup k na of
                    Nothing -> noMatch ("Key not found: " ++ (T.pack $ show k))
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
             (KeyExt v, _) -> matchFailure ("must not be here" ++ (T.pack $ show v))

  (os, xs) <- L.foldl' f (return mempty) (KM.keys m)
  let rst = KM.filterWithKey (\kk _ -> not $ KM.member kk m) na
  xs <- if allowExt && (not $ KM.null rst)
          then noMatch "might not have extra"
          else return $ KM.union xs $ (KM.map KeyExt) rst

  let c = if allowExt then MatchObjectPartialResult else MatchObjectFullResult
  return $ c os xs

extractKeyReq (KeyReq a) = a
getReqs a = (KM.map extractKeyReq (KM.filter isKeyReq a))

thinPattern :: MonadIO m => MatchPattern -> Maybe Value -> MatchStatusT m MatchResult
thinPattern (MatchObjectFull m) a = thinPatternMap False m a
thinPattern (MatchObjectPartial m) a = thinPatternMap True m a
thinPattern (MatchObjectWithDefaults m d) a = do
  let mm = KM.map KeyReq m
  r <- thinPattern (MatchObjectFull mm) a
  rr <- case r of
             (MatchObjectFullResult _ e) -> return $ e
             _ -> matchFailure "should be impossible"
  return $ MatchObjectWithDefaultsResult (getReqs rr) d (KM.empty)


thinPattern (MatchObjectOnly m) a = do
  gg <- P.traverse matchPatternIsMovable m
  vv <- P.traverse matchPatternIsMovable (KM.elems m)
  let isOne = (P.length $ P.filter id vv) == 1
  let f :: MonadIO m => MatchStatusT m (KeyMap MatchResult) -> Key -> MatchStatusT m (KeyMap MatchResult)
      f acc' k = do
        acc <- acc'
        g <- (m2mst $ matchFailure "impossible") $ KM.lookup k m
        gg' <- (m2mst $ matchFailure "impossible") $ KM.lookup k gg
        let v = if
                  isOne
                  then
                    if gg'
                       then a
                       else Nothing
                    else
                      do
                        a' <- a
                        ka <- asKeyMap a'
                        KM.lookup k ka
        r <- thinPattern g v
        return $ KM.insert k r acc

  rr <- L.foldl' f (return mempty) (KM.keys m)
  return $ MatchObjectOnlyResult rr (KM.empty)


thinPattern (MatchArrayContextFree m) a = MatchStatusT $ do
  rr <- runMatchStatusT $ thinContextFreeMatch m a
  runMatchStatusT $ case rr of
       NoMatch e -> noMatch ("context-free nomatch: " ++ e)
       MatchFailure s -> matchFailure s
       MatchSuccess x -> return $ MatchArrayContextFreeResult x

thinPattern (MatchArrayOnly m) (Just (Array a)) = do
  let f acc' e = do
        acc <- acc'
        MatchStatusT $ do
          rr <- runMatchStatusT $ thinPattern m (Just e)
          runMatchStatusT $ case rr of
              MatchFailure f -> matchFailure f
              NoMatch s -> noMatch s
              MatchSuccess r' -> return $ V.snoc acc r'
  r <- L.foldl' f (return mempty) $ V.toList a
  return $ if P.null r
              then MatchArrayOnlyResultEmpty m []
              else MatchArrayOnlyResultSome r []

thinPattern MatchFunnel (Just v) = return $ MatchFunnelResult v

thinPattern MatchFunnelKeys (Just (Object v)) = return $ MatchFunnelKeysResult v
thinPattern MatchFunnelKeys _ = matchFailure "MatchFunnelKeys met not an Object or met Nothing"

thinPattern MatchFunnelKeysU (Just (Object v)) = return $ MatchFunnelKeysUResult v
thinPattern MatchFunnelKeysU _ = matchFailure "MatchFunnelKeysU met not an Object or met Nothing"

thinPattern (MatchNot m) (Just v) = do
  MatchStatusT $ do
    rr <- runMatchStatusT $ thinPattern m (Just v)
    runMatchStatusT $ case rr of
        NoMatch x -> return $ MatchNotResult m v
        MatchFailure f -> matchFailure f
        MatchSuccess s -> noMatch $ "Not fail"

thinPattern (MatchAnd m' m) v = do
  s' <- thinPattern m' v
  s <- thinPattern m v
  return $ MatchAndResult s' s

thinPattern (MatchIfThen baseMatch failMsg match) v = do
  MatchStatusT $ do
    rr <- runMatchStatusT $ thinPattern baseMatch v
    runMatchStatusT $ case rr of
        NoMatch x -> noMatch x
        MatchFailure f -> matchFailure f
        MatchSuccess _ -> do
          MatchStatusT $ do
            rr' <- runMatchStatusT $ thinPattern match v
            runMatchStatusT $ case rr' of
                              NoMatch x -> matchFailure (failMsg ++ (T.pack $ show x))
                              MatchFailure f -> matchFailure f
                              MatchSuccess s -> return $ MatchIfThenResult baseMatch failMsg s

thinPattern MatchAny (Just a) = return $ MatchAnyResult a
thinPattern MatchNone Nothing = return $ MatchNoneResult Null

thinPattern (MatchOr ms) (Just (Object v)) = do
  itsK <- (m2mst $ matchFailure $ "data error117" ++ (T.pack $ show v)) $ (KM.lookup "k") v
  itsK <- (m2mst $ matchFailure $ "data error117" ++ (T.pack $ show v)) $ asString itsK
  itsK <- return $ K.fromText itsK
  let itsV = KM.lookup "v" v
  aa <- (m2mst $ noMatch $ "Wrong k" ++ (T.pack $ show itsK)) $ (KM.lookup itsK) ms
  r <- thinPattern aa itsV
  rr <- return $ MatchOrResult (KM.delete itsK ms) itsK r
  return $ rr

-- specific (aka exact)
thinPattern (MatchStringExact m) Nothing = return $ MatchStringExactResult m
thinPattern (MatchNumberExact m) Nothing = return $ MatchNumberExactResult m
thinPattern (MatchBoolExact m) Nothing = return $ MatchBoolExactResult m
-- any (of a type)
thinPattern MatchStringAny (Just (String a)) = return $ MatchStringAnyResult a
thinPattern MatchNumberAny (Just (Number a)) = return $ MatchNumberAnyResult a
thinPattern MatchBoolAny (Just (Bool a)) = return $ MatchBoolAnyResult a
-- null is just null
thinPattern MatchNull Nothing = return $ MatchNullResult
-- default ca
thinPattern m a = noMatch ("thinPattern bottom reached:\n" ++ (T.pack $ show m) ++ "\n" ++ (T.pack $ show a))

-- thin pattern R
{-
thinPatternR (MatchObjectFullResult _ _) = error "not implemented"
thinPatternR (MatchObjectPartialResult _ _) = error "not implemented"
--thinPatternR (MatchObjectWithDefaultsResult r d o) = L.foldl' f (MatchStatus mempty) r-}

safeGet :: (V.Vector a) -> Int -> Maybe a
safeGet xs n
  | n < 0     = Nothing
             -- Definition adapted from GHC.List
  | otherwise = V.foldr (\x r k -> case k of
                                   0 -> Just x
                                   _ -> r (k-1)) (const Nothing) xs n

applyOriginalValueDefaultsCF :: ContextFreeGrammarResult MatchPattern MatchResult -> Maybe (ContextFreeGrammarResult MatchPattern MatchResult) -> ContextFreeGrammarResult MatchPattern MatchResult

applyOriginalValueDefaultsCF (CharNode x) (Just (CharNode x')) = CharNode $ applyOriginalValueDefaults x (Just x')
applyOriginalValueDefaultsCF (SeqNode x) (Just (SeqNode x')) = SeqNode $ V.map (\(e, e') -> applyOriginalValueDefaultsCF e (Just e')) $ V.zip x x'
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
    l = StarNodeValue $ V.map (\(e, i) -> applyOriginalValueDefaultsCF e (safeGet m' (i - 1))) $ V.zip m is

applyOriginalValueDefaultsCF o@(StarNodeValue m) (Just (StarNodeValue m')) = l
  where
    l = StarNodeValue $ V.map (\(e, i) -> applyOriginalValueDefaultsCF e (safeGet m' (i - 1))) $ V.zip m [1..]

applyOriginalValueDefaultsCF o@(PlusNodeIndexed m is) (Just (PlusNode m')) = l
  where
    l = PlusNode $ V.map (\(e, i) -> applyOriginalValueDefaultsCF e (safeGet m' (i - 1))) $ V.zip m is

applyOriginalValueDefaultsCF o@(PlusNode m) (Just (PlusNode m')) = l
  where
    l = PlusNode $ V.map (\(e, i) -> applyOriginalValueDefaultsCF e (safeGet m' (i - 1))) $ V.zip m [1..]

applyOriginalValueDefaultsCF (OptionalNodeValue m) (Just (OptionalNodeValue m')) = l
  where
    l = OptionalNodeValue (applyOriginalValueDefaultsCF m (Just m'))
applyOriginalValueDefaultsCF x _ = x

applyOriginalValueDefaults :: MatchResult -> Maybe MatchResult -> MatchResult
applyOriginalValueDefaults (MatchObjectWithDefaultsResult m d _) (Just (MatchObjectWithDefaultsResult m' _ a)) = l --error $ show (m, m', d, a)
  where
    m'' = KM.mapMaybeWithKey (\k e -> Just $ applyOriginalValueDefaults e (KM.lookup k m')) m
    l = MatchObjectWithDefaultsResult m'' d a

applyOriginalValueDefaults (MatchArrayOnlyResultEmpty m v) (Just (MatchArrayOnlyResultEmpty m' v')) = l --error $ show (m, m', d, a)
  where
    l = MatchArrayOnlyResultEmpty m v'

applyOriginalValueDefaults (MatchArrayOnlyResultSome m v) (Just (MatchArrayOnlyResultSome m' v')) = l --error $ show (m, m', d, a)
  where
    m'' = fmap (\(a, b) -> applyOriginalValueDefaults a (Just b)) $ V.zip m m'
    l = MatchArrayOnlyResultSome m'' v'

applyOriginalValueDefaults (MatchObjectOnlyResult m a) (Just (MatchObjectOnlyResult m' a')) = l --error $ show (m, m', d, a)
  where
    m'' = KM.mapMaybeWithKey (\k e -> Just $ applyOriginalValueDefaults e (KM.lookup k m')) m
    l = MatchObjectOnlyResult m' a'
applyOriginalValueDefaults (MatchArrayContextFreeResult m) (Just (MatchArrayContextFreeResult m')) = l
  where
    l = MatchArrayContextFreeResult (applyOriginalValueDefaultsCF m (Just m'))
applyOriginalValueDefaults o@(MatchOrResult ms k m) (Just (MatchOrResult ms' k' m')) = l
  where
    l = if k == k' then MatchOrResult ms k (applyOriginalValueDefaults m (Just m'))
                   else o
applyOriginalValueDefaults o@(MatchAndResult r1' r1) (Just (MatchAndResult r2' r2)) = l
  where
    s' = applyOriginalValueDefaults r1' (Just r2')
    s = applyOriginalValueDefaults r1 (Just r2)
    l = MatchAndResult s' s
applyOriginalValueDefaults (MatchIfThenResult b e m) (Just (MatchOrResult b' e' m')) = l
  where
    l = MatchIfThenResult b e (applyOriginalValueDefaults m (Just m'))
applyOriginalValueDefaults (MatchNoneResult _) (Just (MatchNoneResult v)) = l
  where
    l = (MatchNoneResult v)
applyOriginalValueDefaults x _ = x

-- The most useful
-- Value -> MatchPattern -> MatchResult
-- MatchResult -> Thin Value
-- Thin Value, MatchPattern -> 
-- Thin Value, Original MatchResult -> 
thinPatternWithDefaults :: MonadIO m => MatchResult -> Maybe Value -> MatchStatusT m MatchResult
thinPatternWithDefaults r v = do
  let p = matchResultToPattern r
  vr <- thinPattern p v
  return $ applyOriginalValueDefaults vr (Just r)

-- Match functions end

g00 = (Seq [(Star (Char 1)), (Optional (Char 4))])


{-contextFreeMatchI p v f = runIdentity $ runReaderT (runMatchStatusT $ contextFreeMatch p v f) $ emptyEnvValue

matchPatternI g p v = runIdentity $ runReaderT (runMatchStatusT $ matchPattern g p v) $ emptyEnvValue

main1 = do
  contextFreeMatchI g00 ([1, 1, 1, 4] :: [Int]) ((\a b -> if a == b then return a else noMatch "foo"))

qc1 = do
  quickCheck (\g v -> case (matchPatternI mempty g v) of (MatchSuccess s) -> v == matchResultToValue s; _ -> True)

qc2 = do
  quickCheck (\g v -> case (matchPatternI mempty g v) of (MatchSuccess s) -> g == matchResultToPattern s; _ -> True)


qc3 = do
  quickCheck (\v -> case (matchPatternI mempty (valueToExactGrammar v) v) of MatchSuccess _ -> True; _ -> False)-}

-- TH tricks (read DT)

d1 = reifyDatatype ''MatchPattern
-- TL.unpack . TL.decodeUtf8 . encode . toJ
d2 = $(ddd [''MatchPattern,
            ''MatchResult,
            ''ContextFreeGrammar,
            ''ContextFreeGrammarResult,
            ''ObjectKeyMatch
            ])
--- _ <- TL.writeFile "/home/.../d2.json" (TL.pack d2)

-- constantness

trueOrFail x = case x of
                    MatchSuccess x -> x
                    _ -> True

{-
qc4 = do
  quickCheck True --(not . trueOrFail . (runIdentity $ runReaderT (runMatchStatusT $ matchPatternIsMovable mempty)) . valueToExactGrammar) TODO fix

qc5 = do
  quickCheck True --(\v -> case (runIdentity $ runReaderT (runMatchStatusT $ valueToExactResult v) emptyEnvValue) of MatchSuccess s -> not $ trueOrFail $ matchResultIsMovable mempty s; _ -> False) TODO fix


c6f :: MatchResult -> Bool
c6f r = let
        p = matchResultToPattern r
        t = extract (matchResultToThinValue mempty r)
        r0 = (thinPattern mempty p) t
        r1 = case r0 of
                  NoMatch s -> error ("NoMatch: " ++ s ++ "\n\n" ++ (T.pack $ show p) ++ "\n\n" ++ show (matchResultToValue r))
                  MatchFailure s -> error ("MatchFailure: " ++ s ++ "\n\n" ++ (T.pack $ show p) ++ "\n\n" ++ show (matchResultToValue r))
                  MatchSuccess s -> s
      in r == r1

c6c r = if extract $ matchResultIsWellFormed mempty r then c6f r else True

qc6 = quickCheck c6c
qq = quickCheck (withMaxSuccess 10000 c6c)-}

-- Different matches for or example (trivial and normal)
-- p[attern] v[alue] r[esult] t[hin value]

{-
tVIs :: MatchPattern -> Value -> Expectation
tVIs p v = 
      let r = extract $ matchPatternI mempty p v
          t' = extract $ matchResultToThinValue mempty r
          r' = extract $ thinPattern mempty p t'
          r'' = applyOriginalValueDefaults r' (Just r)
          v2 = matchResultToValue r''
      in r'' `shouldBe` r

tIs :: MatchPattern -> Value -> Maybe Value -> Expectation
tIs p v t = 
      let r = extract $ matchPatternI mempty p v
          t' = extract $ matchResultToThinValue mempty r
      in t' `shouldBe` t

test :: IO ()
test = hspec $ do
  describe "MatchObjectWithDefaults matchPattern works correctly" $ do
    it "handles correctly the empty case" $ do
      let r = matchPatternI mempty (MatchObjectWithDefaults (fromList []) (fromList [])) (Object (fromList []))
      r `shouldBe` MatchSuccess (MatchObjectWithDefaultsResult (fromList []) (fromList []) (fromList []))

    it "handles correctly the case with default value" $ do
      let r = matchPatternI mempty (MatchObjectWithDefaults (fromList [("a", MatchNumberAny)]) (fromList [("w", String " ")])) (Object (fromList [("a", Number 1), ("w", String $ " ")]))
      r `shouldBe` MatchSuccess (MatchObjectWithDefaultsResult (fromList [("a",MatchNumberAnyResult 1.0)]) (fromList [("w", String " ")]) (fromList []))

    it "handles correctly the case with different value" $ do
      let r = matchPatternI mempty (MatchObjectWithDefaults (fromList [("a", MatchNumberAny)]) (fromList [("w", String " ")])) (Object (fromList [("a", Number 1), ("w", String $ "   ")]))
      r `shouldBe` MatchSuccess (MatchObjectWithDefaultsResult (fromList [("a",MatchNumberAnyResult 1.0)]) (fromList [("w",String " ")]) (fromList [("w",String "   ")]))

  describe "handles MatchPattern nodes correctly" $ do
    it "Handles trivial MatchOr correctly. Nothing case" $ do
      let p = (MatchOr (KM.fromList [
            (K.fromText "option1", (MatchNumberExact 1)),
            (K.fromText "option2", (MatchNumberExact 2))]))
          v = Number 1
      tVIs p v
    it "Handles trivial MatchOr correctly. Nothing case" $ do
      let p = (MatchOr (KM.fromList [
            (K.fromText "option1", (MatchNumberExact 1)),
            (K.fromText "option2", (MatchNumberExact 2))]))
          v = Number 2
      tVIs p v
    it "Handles actual MatchOr correctly. Nothing case" $ do
      let p = (MatchOr (KM.fromList [
            (K.fromText "option1", (MatchNumberExact 1)),
            (K.fromText "option2", (MatchNumberAny))]))
          v = Number 1
      tVIs p v
    it "Handles actual MatchOr correctly. Just case" $ do
      let p = (MatchOr (KM.fromList [
            (K.fromText "option1", (MatchNumberExact 1)),
            (K.fromText "option2", (MatchNumberAny))]))
          v = Number 2
      tVIs p v
    it "Handles actual MatchObjectFull correctly. Some nothing, some Just case. Some opts exist, some don't" $ do
      let p = (MatchObjectFull (KM.fromList [
            (K.fromText "a", KeyReq (MatchNumberExact 1))
            , (K.fromText "b", KeyOpt (MatchNumberExact 2))
            , (K.fromText "b1", KeyOpt (MatchNumberExact 3))
            , (K.fromText "c", KeyReq (MatchNumberAny))
            , (K.fromText "d", KeyOpt (MatchNumberAny))
            , (K.fromText "d1", KeyOpt (MatchNumberAny))
            ]))
          v = Object (KM.fromList [
            (K.fromText "a", Number 1)
            , (K.fromText "b", Number 2)
            , (K.fromText "c", Number 4)
            , (K.fromText "d", Number 5)
            ])
      tVIs p v
      --2 + 2 `shouldBe` 4
  describe "matchResultToThinValue works correctly" $ do
    it "case a a" $ do
      let p = (MatchObjectFull (KM.fromList [
            (K.fromText "a", KeyReq (MatchNumberExact 1))
            ]))
          v = Object (KM.fromList [
            (K.fromText "a", Number 1)
            ])
          t = Nothing
      tIs p v t
    it "case c" $ do
      let p = (MatchObjectFull (KM.fromList [
            (K.fromText "c", KeyReq MatchNumberAny)
            ]))
          v = Object (KM.fromList [
            (K.fromText "c", Number 1)
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
  describe "Handles Defaults correctly" $ do
    it "Handles actual MatchObjectWithDefaults correctly default" $ do
      let a x = MatchArrayContextFree (Seq [(Star $ Char x)])
          p = a $ MatchObjectWithDefaults (fromList [("a", MatchStringAny), ("b", MatchNumberAny)]) (fromList [("w", String " ")])
          v = Array $ V.fromList [Object (fromList [("a", String "hello"), ("b", Number 5)])]
      tVIs p v
    it "Handles actual MatchObjectWithDefaults correctly same as default" $ do
      let a x = MatchArrayContextFree (Seq [(Star $ Char x)])
          p = a $ MatchObjectWithDefaults (fromList [("a", MatchStringAny), ("b", MatchNumberAny)]) (fromList [("w", String " ")])
          v = Array $ V.fromList [Object (fromList [("a", String "hello"), ("b", Number 5), ("w", String " ")])]
      tVIs p v
    it "Handles actual MatchObjectWithDefaults correctly different" $ do
      let a x = MatchArrayContextFree (Seq [(Star $ Char x)])
          p = a $ MatchObjectWithDefaults (fromList [("a", MatchStringAny), ("b", MatchNumberAny)]) (fromList [("w", String " ")])
          v = Array $ V.fromList [Object (fromList [("a", String "hello"), ("b", Number 5), ("w", String "  ")])]
      tVIs p v
  describe "Handles Only correctly" $ do
    it "Handles actual MatchObjectOnly correctly default" $ do
      let a x = MatchArrayContextFree (Seq [(Star $ Char x)])
          p = a $ MatchObjectOnly (fromList [("a", MatchStringAny), ("b", MatchNumberAny)])
          v = Array $ V.fromList [Object (fromList [("a", String "hello"), ("b", Number 5)])]
      tVIs p v
    it "Handles actual MatchObjectOnly correctly same as default" $ do
      let a x = MatchArrayContextFree (Seq [(Star $ Char x)])
          p = a $ MatchObjectOnly (fromList [("a", MatchStringAny), ("b", MatchNumberAny)])
          v = Array $ V.fromList [Object (fromList [("a", String "hello"), ("b", Number 5), ("w", String " ")])]
      tVIs p v
    it "Handles actual MatchObjectOnly correctly different" $ do
      let a x = MatchArrayContextFree (Seq [(Star $ Char x)])
          p = a $ MatchObjectOnly (fromList [("a", MatchStringAny), ("b", MatchNumberAny)])
          v = Array $ V.fromList [Object (fromList [("a", String "hello"), ("b", Number 5), ("w", String "  ")])]
      tVIs p v

demo1 = do
  let p = (MatchObjectFull (KM.fromList [
        (K.fromText "a", KeyReq (MatchNumberExact 1))
        , (K.fromText "b", KeyOpt (MatchNumberExact 2))
        , (K.fromText "b1", KeyOpt (MatchNumberExact 3))
        , (K.fromText "c", KeyReq (MatchNumberAny))
        , (K.fromText "d", KeyOpt (MatchNumberAny))
        , (K.fromText "d1", KeyOpt (MatchNumberAny))
        ]))
      v = Object (KM.fromList [
        (K.fromText "a", Number 1)
        , (K.fromText "b", Number 2)
        , (K.fromText "c", Number 4)
        , (K.fromText "d", Number 5)
        ])
      r = extract $ matchPatternI mempty p v
      t = extract $ matchResultToThinValue mempty r
  putStrLn $ show $ r
  putStrLn $ show $ t
  putStrLn $ show $ extract $ thinPattern mempty p t

w1 p v = 
      let r = extract $ matchPatternI mempty p v
          t' = matchResultToThinValue mempty r
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
-- TODO fix
thinWithDefaults1 = do
  let v = Array [
            (Object (fromList [("type", String "Node"), ("value", Number 10), ("ws", String " ")])),
            (Object (fromList [("type", String "Node"), ("value", Number 20), ("ws", String "  ")])),
            (Object (fromList [("type", String "Node"), ("value", Number 30), ("ws", String "   ")]))]
  let p = MatchArrayContextFree $ Seq [Star $ Char $ MatchObjectWithDefaults (fromList [("type", MatchStringExact "Node"), ("value", MatchNumberAny)]) (fromList [("ws", String " ")])]
  r <- matchPatternI mempty p v
  let t = Just (Array [Array [Number 1.0,Number 10.0],Array [Number 2.0,Number 20.0],Array [Number 0,Number 50.0],Array [Number 3.0,Number 30.0]])
  --return $ thinPattern p t
  r' <- thinPatternWithDefaults mempty r t
  return $ matchResultToValue r'

thinWithDefaults2 = do
  let v = Array [
            (Object (fromList [("type", String "Node"), ("value", Number 10), ("ws", String " ")])),
            (Object (fromList [("type", String "Node"), ("value", Number 10), ("ws", String "  ")])),
            (Object (fromList [("type", String "Node"), ("value", Number 10), ("ws", String "   ")]))]
  let p = MatchArrayContextFree $ Seq [Star $ Char $ MatchObjectWithDefaults (fromList [("type", MatchStringExact "Node"), ("value", MatchNumberExact 10.0)]) (fromList [("ws", String " ")])]
  r <- matchPatternI mempty p v
  --return $ matchResultToThinValue r
  let t = Just $ Number 5.0
  r' <- thinPatternWithDefaults mempty r t
  return $ matchResultToValue r'


ex1 = do
	let a = (fromList [("element", MatchArrayContextFree $ Star (Seq [(Char (MatchRef "element"))]))])
	let v = StarNodeEmpty (Char (MatchRef "element"))
	contextFreeGrammarResultToThinValue a v-}


mdb :: IO ()
mdb = do
  let p = MatchFromMongoDB "logicore" "products" $ MatchObjectOnly (fromList [(fromText "item", MatchStringExact "card"), (fromText "qty", MatchNumberAny)])
  let v = String "657aa1c7ec43193e13182e9e"
  a <- liftIO $ runReaderT (runMatchStatusT $ matchPattern p v) emptyEnvValue
  return ()
  --print a


rdb :: IO ()
rdb = do
  let p = MatchFromRedis "logicore" "products" $ MatchObjectOnly (fromList [(fromText "item", MatchStringExact "card"), (fromText "qty", MatchNumberAny)])
  let v = String "hello"
  conn <- liftIO $ Redis.connect Redis.defaultConnectInfo
  a <- liftIO $ runReaderT (runMatchStatusT $ matchPattern p v) $ MatcherEnv { redisConn = conn }
  --print a
  return ()


loadFigma :: IO ()
loadFigma = do
  conn <- liftIO $ Redis.connect Redis.defaultConnectInfo
  undefined
