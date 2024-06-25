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
{-# LANGUAGE QuasiQuotes #-}


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
import Control.Monad.Trans.Identity
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

option_match = MatchObjectOnly (fromList [
  ("cases",MatchArray (MatchObjectOnly (fromList [
                                          ("body",MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Char $ MatchAny])),("type",MatchStringExact "IndentedBlock")])),
                                          ("guard",MatchNull),
                                          ("pattern",MatchObjectOnly (fromList [("type",MatchStringExact "MatchAs"),("name",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringAny)]))])),("type",MatchStringExact "MatchCase")]))),
  ("subject",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringExact "__o")])),
  ("type",MatchStringExact "Match")])

vars_match = MatchObjectOnly (fromList [
  ("cases",
    MatchArrayContextFree (Seq [(Star (Char (MatchObjectOnly (fromList [
                                          ("body",MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Char $ MatchAny])),("type",MatchStringExact "IndentedBlock")])),
                                          ("guard",MatchNull),
                                          ("pattern",MatchObjectOnly (fromList [("type",MatchStringExact "MatchAs"),("name",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringAny)]))])),("type",MatchStringExact "MatchCase")])))),
    (Char (MatchObjectOnly (fromList [
                                          ("body",
                                            MatchObjectOnly (fromList [("body", MatchAny),("type",MatchStringExact "IndentedBlock")])
                                              ),
                                          ("guard",MatchNull),
                                          ("pattern",MatchObjectOnly (fromList [("type",MatchStringExact "MatchAs"),("name",MatchNull)])),("type",MatchStringExact "MatchCase")])))
    ])),
  ("subject",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringExact "__vars")])),
  ("type",MatchStringExact "Match")])

vars_block = MatchArrayContextFree (Seq [Char vars_match])

simple_ref = MatchObjectOnly (fromList [("args",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("keyword",MatchNull),("star",MatchStringExact ""),("type",MatchStringExact "Arg"),("value",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringAny)]))]))])),("func",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringExact "__ref")])),("type",MatchStringExact "Call")])

ref = MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("type",MatchStringExact "Expr"),("value", simple_ref)]))])),("type",MatchStringExact "SimpleStatementLine")])



simple_l = MatchObjectOnly (fromList [("args",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("keyword",MatchNull),("star",MatchStringExact ""),("type",MatchStringExact "Arg"),("value",MatchAny)]))])),("func",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringExact "__l")])),("type",MatchStringExact "Call")])

simple_var = MatchObjectOnly (fromList [("args",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("keyword",MatchNull),("star",MatchStringExact ""),("type",MatchStringExact "Arg"),("value",v_object)]))])),("func",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringExact "__var")])),("type",MatchStringExact "Call")])

l_expr = MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("type",MatchStringExact "Expr"),("value", simple_l)]))])),("type",MatchStringExact "SimpleStatementLine")])



kw_expr = MatchObjectOnly (fromList [
  ("keyword",MatchNull),
  ("star",MatchStringExact ""),
  ("type",MatchStringExact "Arg"),
  ("value",MatchObjectOnly (fromList [
        ("args",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("keyword",MatchNull),
                                                                             ("star",MatchStringExact ""),
                                                                             ("type",MatchStringExact "Arg"),
                                                                             ("value",MatchAny)]))])),
        ("func",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringExact "__kw")])),
        ("type",MatchStringExact "Call")]))])



getMatch p v = case matchPatternI p v of
  MatchSuccess r -> extract $ matchResultToThinValueI r
  _ -> Nothing


getMatch' p v = case matchPatternI p v of
  MatchSuccess r -> Right $ fromJust $ extract $ matchResultToThinValueI r
  NoMatch e -> Left (p, v)
  --MatchFailure e -> Left 


extractSeq body = do
  rr <- pythonModValueToGrammar body
  return $ case rr of
    MatchArrayContextFree a -> a
    _ -> error "must not be here"

v_object = MatchObjectOnly (fromList [("type", MatchStringExact "Name"), ("value", MatchAny)])

kw_object a = (MatchObjectOnly (fromList [
  ("keyword", MatchOr (fromList [("null", MatchNull), ("keyword", v_object)])),
  ("star",MatchStringExact ""),
  ("type",MatchStringExact "Arg"),
  ("value", a)]))

processArrayItem :: MonadIO m => Value -> MatchPattern -> IdentityT m (ContextFreeGrammar MatchPattern)
processArrayItem v p = r where
  r :: MonadIO m => IdentityT m (ContextFreeGrammar MatchPattern)
  r = case getMatch kw_expr v of
        Just e -> do
            rr <- pythonModValueToGrammar e
            return $ Star $ Char $ kw_object rr
        _ -> case getMatch special_if v of
          Just s -> let
            rr = do
              t' <- asKeyMap s
              test <- KM.lookup "test" t'
              test' <- asString test
              body <- KM.lookup "body" t'
              return $ case test' of
                "__star" -> fmap Star $ extractSeq body
                "__plus" -> fmap Plus $ extractSeq body
                "__maybe" -> fmap Optional $ extractSeq body
                "__seq" -> fmap (Char . MatchArrayContextFree) $ extractSeq body
                _ -> return $ Char p
            in case rr of
                Just rr -> rr
                Nothing -> error "shouldn't be this"
          _ -> return $ Char p

pythonValueToExactGrammar :: Value -> MatchPattern
pythonValueToExactGrammar = para go
  where
    go (ObjectF a) = MatchObjectOnly (KM.map snd $ cleanUpPythonWSKeys a)
    go (ArrayF a) = MatchArrayContextFree $ Seq $ fmap (Char . snd) a
    go (StringF a) = MatchStringExact a
    go (NumberF a) = MatchNumberExact a
    go (BoolF a) = MatchBoolExact a
    go NullF = MatchNull


handle_m1 :: Value -> [(Key, Value)]
handle_m1 m' = V.toList $ fmap (\x -> let m = fromJust $ asKeyMap x in (K.fromText $ fromJust $ asString =<< KM.lookup "pattern" m, (fromJust $ KM.lookup "body" m))) (fromJust $ asArray m')


line_a = MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("type",MatchStringExact "Expr"),("value",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringAny)]))]))])),("type",MatchStringExact "SimpleStatementLine")])
--line_a = MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("type",MatchStringExact "Expr"),("value", (MatchObjectOnly (fromList [("type", MatchStringExact "Name", "value", MatchStringExact "__a")])))]))])),("type",MatchStringExact "SimpleStatementLine")])
--line_f = MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("type",MatchStringExact "Expr"),("value",MatchFunnel)]))])),("type",MatchStringExact "SimpleStatementLine")])

line_if = MatchObjectOnly (fromList [("body",MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("body",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("type",MatchStringExact "Pass")]))])),("type",MatchStringExact "SimpleStatementLine")]))])),("type",MatchStringExact "IndentedBlock")])),("orelse",MatchNull),("test",MatchObjectOnly (fromList [("args",MatchArrayContextFree (Seq [Char (MatchObjectOnly (fromList [("keyword",MatchNull),("star",MatchStringExact ""),("type",MatchStringExact "Arg"),("value", MatchAny)]))])),("func",MatchObjectOnly (fromList [("type",MatchStringExact "Name"),("value",MatchStringExact "__if")])),("type",MatchStringExact "Call")])),("type",MatchStringExact "If")])

pythonModValueToGrammar :: MonadIO m => Value -> IdentityT m MatchPattern
pythonModValueToGrammar = paraM go
  where
    go :: MonadIO m => (ValueF (Value, MatchPattern)) -> IdentityT m MatchPattern
    go (ObjectF a) = do
      case getMatch simple_var (Object (KM.map fst a)) of
              Just (String l) -> return $ MatchVar l
              _ -> case getMatch l_expr (Object (KM.map fst a)) of
                    Just l -> pythonModValueToGrammar l
                    _ -> case getMatch ref (Object (KM.map fst a)) of
                          Just n -> return $ MatchRef (fromJust $ asString n)
                          _ -> case getMatch simple_ref (Object (KM.map fst a)) of
                                Just n -> return $ MatchRef (fromJust $ asString n)
                                _ -> case getMatch line_a (Object (KM.map fst a)) of
                                      Just "__a" -> return $ MatchAny
                                      Just "__f" -> return $ MatchFunnel
                                      _ ->
                                          case getMatch special_v (Object (KM.map fst a)) >>= asString of
                                            Just r -> case r of
                                              "__f" -> return $ MatchFunnel
                                              "__v" -> return $ v_object
                                              "__s" -> return $ MatchObjectOnly (fromList [("type", MatchStringExact "SimpleString"), ("value", MatchAny)])
                                              "__n" -> return $ MatchObjectOnly (fromList [("type", MatchStringExact "Integer"), ("value", MatchAny)])
                                              "__a" -> return $ MatchAny
                                              _ -> return $ MatchObjectOnly (KM.map snd $ cleanUpPythonWSKeys a)
                                            Nothing -> do
                                                          --if (KM.lookup "type" (KM.map fst a)) == Just (String "Match") then error $ show $ (Object (KM.map fst a)) else Just ()
                                                          --liftIO $ print line_a
                                                          case getMatch option_match (Object (KM.map fst a)) of
                                                            Just m' -> do
                                                              --liftIO $ BL.putStr $ encode $ m'
                                                              let m'' = KM.fromList $ handle_m1 m'
                                                              rrr <- KM.traverse pythonModValueToGrammar m''
                                                              return $ MatchOr rrr
                                                            _ -> return $ MatchObjectOnly (KM.map snd $ cleanUpPythonWSKeys a)
    go (ArrayF a) = 
      case getMatch' vars_block (Array (V.map fst a)) of
        Right m' -> do
          let m'' = fromJust $ asArray m'
              items = fromJust . asArray $ V.head m''
              last = V.head $ V.tail m''
              f1 (Object item) = let pattern = fromJust $ asString $ fromJust $ KM.lookup "pattern" item
                                     body = fromJust $ KM.lookup "body" item
                                  in (K.fromText pattern, body)
              items' = KM.fromList $ V.toList $ V.map f1 $ items
          items'' <- P.traverse pythonModValueToGrammar items'
          last' <- pythonModValueToGrammar last
          --liftIO $ putStrLn "generating MatchLet"
          --liftIO $ print last'
          return $ MatchLet items'' last'
        Left e -> do
          --liftIO $ print e
          rr <- P.traverse (uncurry processArrayItem) a
          return $ MatchArrayContextFree $ Seq $ rr
    go (StringF a) = return $ MatchStringExact a
    go (NumberF a) = return $ MatchNumberExact a
    go (BoolF a) = return $ MatchBoolExact a
    go NullF = return $ MatchNull

e1 = (fromJust $ decode $ TL.encodeUtf8 $ TL.pack $ unsafePerformIO (readFile "../star1.json")) :: Value
o1 = (fromJust $ decode $ TL.encodeUtf8 $ TL.pack $ unsafePerformIO (readFile "../opt1.json")) :: MatchPattern
m1 = (fromJust $ decode $ TL.encodeUtf8 $ TL.pack $ unsafePerformIO (readFile "../match_r.json")) :: Value
v1 = (fromJust $ decode $ TL.encodeUtf8 $ TL.pack $ unsafePerformIO (readFile "../vars_r.json")) :: Value

--r1 = P.putStrLn $ TL.unpack $ TL.decodeUtf8 $ encode $ extract $ matchResultToThinValueI $ extract $ matchPatternI special_if e1
