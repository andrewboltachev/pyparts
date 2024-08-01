{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
{-# LANGUAGE RankNTypes #-}


module Logicore.Matcher.Functions where
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
import qualified Data.Set
import qualified Data.List        as L
import GHC.Generics
import Data.Aeson
import Data.Either
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
import Data.Char
import qualified Data.Set                     as S

import Control.Lens hiding (indexing)
import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
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


splitPascalCase :: Value -> Value -> Either T.Text Value
splitPascalCase (String s) _ = do
  let lastIsEmpty xs = if V.null xs
                          then False
                          else (V.last xs) == (String "")
      h (String s) newChar = String $ T.snoc s newChar
      g newChar acc idx elt = if idx == (V.length acc) - 1 then h elt newChar else elt
      f acc' e = do
        acc <- acc'
        let nextAcc = if (isUpper e) && (not $ lastIsEmpty acc)
                    then V.snoc acc (String "")
                    else acc
        return $ V.imap (g e nextAcc) nextAcc
  v <- V.foldl' f (return $ [String ""]) ((V.fromList . T.unpack) s)
  return $ Array v
splitPascalCase _ _ = Left "splitPascalCase needs a string" 


matchFunctions :: KeyMap (Value -> Value -> Either T.Text Value)
matchFunctions = fromList [
  ("splitPascalCase", splitPascalCase)
  ]
