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


module Logicore.Matcher.Python where

import Prelude as P hiding ((++))

import qualified Data.Vector.Generic
import qualified Data.Set
import qualified Data.List        as L
import GHC.Generics
import Data.Aeson
--import Data.ByteString            as B
import qualified Data.ByteString.Lazy       as BL hiding (putStrLn)
import qualified Data.Text                  as T
import qualified Data.Text.Encoding         as T
--import Data.Text.IO               as T
import qualified Data.Text.Lazy             as TL
import qualified Data.Text.Lazy.Encoding    as TL
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

import System.IO.Unsafe (unsafePerformIO)

-- local...
import Logicore.Matcher.Core

-- cleanup keys

pythonWSKeys :: KeyMap [Key]
pythonWSKeys = fromList [
  -- ("", ["", ""])
  ]

pythonGlobalWSKeys :: [T.Text]
pythonGlobalWSKeys = ["lpar", "rpar", "semicolon", "leading_lines", "footer", "header", "comment", "newline", "indent", "comma", "equal"]

pythonRemoveGlobalWSKeys :: KM.KeyMap a -> KM.KeyMap a
pythonRemoveGlobalWSKeys a = KM.filterWithKey pred a where
  pred k _ = let
                t = (toText k)
             in not (("whitespace" `T.isInfixOf` t) || (elem t pythonGlobalWSKeys))

cleanUpPythonWSKeys :: KeyMap (Value, MatchPattern) -> KeyMap (Value, MatchPattern)
cleanUpPythonWSKeys a = case KM.lookup "type" a of
  Nothing -> a
  Just ((String t), _) -> pythonRemoveGlobalWSKeys $ case KM.lookup (fromText t) pythonWSKeys of
    Nothing -> a
    Just ks -> a
  Just _ -> a

-- process

special_if = MatchObjectOnly (fromList [("body",MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Star $ Char MatchAny])),("type",MatchStringExact "IndentedBlock")])),("orelse",MatchNull),("test",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringAny)])),("type",MatchStringExact "If")])

special_v = MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringAny)])

getMatch p v = case matchPatternI p v of
  MatchSuccess r -> extract $ matchResultToThinValueI r
  _ -> Nothing


extractSeq body = case pythonModValueToGrammar body of
                          MatchArrayContextFree a -> a
                          _ -> error "must not be here"

processArrayItem :: Value -> MatchPattern -> ContextFreeGrammar MatchPattern
processArrayItem v p = case getMatch special_if v of
  Just s -> let
    rr = do
      t' <- asKeyMap s
      test <- KM.lookup "test" t'
      test' <- asString test
      body <- KM.lookup "body" t'
      return $ case test' of
        "__star" -> Star $ extractSeq body
        "__plus" -> Plus $ extractSeq body
        "__maybe" -> Optional $ extractSeq body
        "__seq" -> Char $ MatchArrayContextFree $ extractSeq body
        _ -> Char p
    in case rr of
        Just rr -> rr
        Nothing -> error "shouldn't be this"
  _ -> Char p

pythonValueToExactGrammar :: Value -> MatchPattern
pythonValueToExactGrammar = para go
  where
    go (ObjectF a) = MatchObjectOnly (KM.map snd $ cleanUpPythonWSKeys a)
    go (ArrayF a) = MatchArrayContextFree $ Seq $ fmap (Char . snd) a
    go (StringF a) = MatchStringExact a
    go (NumberF a) = MatchNumberExact a
    go (BoolF a) = MatchBoolExact a
    go NullF = MatchNull


pythonModValueToGrammar :: Value -> MatchPattern
pythonModValueToGrammar = para go
  where
    go (ObjectF a) = let
                        
                     in MatchObjectOnly (KM.map snd $ cleanUpPythonWSKeys a)
    go (ArrayF a) = MatchArrayContextFree $ Seq $ fmap (uncurry processArrayItem) a
    go (StringF a) = MatchStringExact a
    go (NumberF a) = MatchNumberExact a
    go (BoolF a) = MatchBoolExact a
    go NullF = MatchNull

e1 = (fromJust $ decode $ TL.encodeUtf8 $ TL.pack $ unsafePerformIO (readFile "../star1.json")) :: Value

r1 = P.putStrLn $ TL.unpack $ TL.decodeUtf8 $ encode $ extract $ matchResultToThinValueI $ extract $ matchPatternI special_if e1
