{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Network.Wai.Handler.Warp (run)
import Web.Twain
import Data.Aeson
import qualified Data.Aeson.KeyMap          as KM
import qualified Data.Aeson.Key             as K
import qualified Data.Vector as V
import qualified Data.Text                  as T
import qualified Data.Text.Encoding         as T
import qualified Data.Text.IO               as T
import qualified Data.Text.Lazy             as TL
import qualified Data.Text.Lazy.Encoding    as TL
import qualified Data.Text.Lazy.IO          as TL

import Logicore.Matcher.Core
import Logicore.Matcher.Additional
import Logicore.Matcher.Python

--import Language.Haskell.TH


main :: IO ()
main = do
  run 3042 $
    foldr ($)
      (notFound missing)
      [ get "/" index
      , post "echo:name" echo
      --, post "python-matcher-1" pythonMatcher1
      --, post "json-matcher-1" jsonMatcher1

      -- fn endpoints
      , post "/matchPattern" (fnEndpoint mkMatchPattern)
      , post "/matchResultToPattern" (fnEndpoint mkMatchResultToPattern)
      , post "/matchResultToValue" (fnEndpoint mkMatchResultToValue)
      , post "/matchResultToThinValue" (fnEndpoint mkMatchResultToThinValue)
      , post "/thinPattern" (fnEndpoint mkThinPattern)
      , post "/valueToExactGrammar" (fnEndpoint mkValueToExactGrammar)
      , post "/valueToExactResult" (fnEndpoint mkValueToExactResult)
      ]


index :: ResponderM a
index = send $ html "Hello World!"

echo :: ResponderM a
echo = do
  name <- param "name"
  send $ html $ "Hello, " <> name


--exp1 = runQ [| \ x -> x  |] >>= putStrLn.pprint

{-

            code <- (m2e "JSON root element must have code") $ KM.lookup (K.fromString "data") e
            grammar <- (m2e "JSON root element must have grammar") $ KM.lookup (K.fromString "grammar") e
            mp <- (m2e "Cannot decode MatchPattern from presented grammar") $ (
              ((decode . encode) grammar) :: Maybe MatchPattern) -- TODO
matchAndCollapse mp return code
-}

mkMatchPattern :: (Object -> MatchStatus Value)
mkMatchPattern e = do
  value <- (m2ms $ MatchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2ms $ MatchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2ms $ MatchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  output <- matchPattern mp value
  outputValue <- (m2ms $ MatchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "result", outputValue)])

mkThinPattern :: (Object -> MatchStatus Value)
mkThinPattern e = do
  thinValue <- return $ KM.lookup (K.fromString "thinValue") e
  pattern <- (m2ms $ MatchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2ms $ MatchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  output <- thinPattern mp thinValue
  outputValue <- (m2ms $ MatchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "result", outputValue)])

mkMatchResultToPattern :: (Object -> MatchStatus Value)
mkMatchResultToPattern e = do
  result <- (m2ms $ MatchFailure "JSON root element must have result") $ KM.lookup (K.fromString "result") e
  mr <- (m2ms $ MatchFailure "Cannot decode MatchResult from presented result") $ (((decode . encode) result) :: Maybe MatchResult) -- TODO
  output <- return $ matchResultToPattern mr
  outputValue <- (m2ms $ MatchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "pattern", outputValue)])

mkMatchResultToValue :: (Object -> MatchStatus Value)
mkMatchResultToValue e = do
  result <- (m2ms $ MatchFailure "JSON root element must have result") $ KM.lookup (K.fromString "result") e
  mr <- (m2ms $ MatchFailure "Cannot decode MatchResult from presented result") $ (((decode . encode) result) :: Maybe MatchResult) -- TODO
  output <- return $ matchResultToValue mr
  return $ Object $ (KM.fromList [(K.fromString "value", output)])

mkMatchResultToThinValue :: (Object -> MatchStatus Value)
mkMatchResultToThinValue e = do
  result <- (m2ms $ MatchFailure "JSON root element must have result") $ KM.lookup (K.fromString "result") e
  mr <- (m2ms $ MatchFailure "Cannot decode MatchResult from presented result") $ (((decode . encode) result) :: Maybe MatchResult) -- TODO
  output <- return $ matchResultToThinValue mr
  let res = case output of
                 Just x -> x
                 Nothing -> Null
  return $ Object $ (KM.fromList [(K.fromString "thinValue", res)])

mkValueToExactGrammar :: (Object -> MatchStatus Value)
mkValueToExactGrammar e = do
  value <- (m2ms $ MatchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  output <- return $ valueToExactGrammar value
  outputValue <- (m2ms $ MatchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "grammar", outputValue)])

mkValueToExactResult :: (Object -> MatchStatus Value)
mkValueToExactResult e = do
  value <- (m2ms $ MatchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  output <- valueToExactResult value
  outputValue <- (m2ms $ MatchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "result", outputValue)])

fnEndpoint :: (Object -> MatchStatus Value) -> ResponderM b
fnEndpoint f = do
    b <- (fromBody :: ResponderM Value)
    let a = do
            e <- (m2e "JSON root element must be a map") $ asKeyMap b
            r <- case f e of
                    MatchFailure s -> Left ("MatchFailure: " ++ s)
                    NoMatch x -> Left ("NoMatch: " ++ x)
                    MatchSuccess r -> Right $ r
            return r
    send $ Web.Twain.json $ case a of
        Left e -> Object (KM.fromList [(K.fromString "error", (String . T.pack) ("Error: " ++ e))])
        Right x -> x

{-
jsonMatcher1 :: ResponderM a
jsonMatcher1 = do
  b <- (fromBody :: ResponderM Value)
  let a = do
          e <- (m2e "JSON root element must be a map") $ asKeyMap b
          code <- (m2e "JSON root element must have code") $ KM.lookup (K.fromString "data") e
          grammar <- (m2e "JSON root element must have grammar") $ KM.lookup (K.fromString "grammar") e
          mp <- (m2e "Cannot decode MatchPattern from presented grammar") $ (
            ((decode . encode) grammar) :: Maybe MatchPattern) -- TODO
          r <- case matchAndCollapse mp return code of
                  MatchFailure s -> Left ("MatchFailure: " ++ s)
                  NoMatch x -> Left ("NoMatch: " ++ x)
                  MatchSuccess (f, r) -> Right $ (KM.fromList [
                    (K.fromString "funnel", (Array . V.fromList) f),
                    (K.fromString "result", r)])
          return (Object r)
  send $ Web.Twain.json $ case a of
       Left e -> Object (KM.fromList [(K.fromString "error", (String . T.pack) ("Error: " ++ e))])
       Right x -> x

pythonMatcher1 :: ResponderM a
pythonMatcher1 = do
  b <- (fromBody :: ResponderM Value)
  let a = do
          e <- (m2e "JSON root element must be a map") $ asKeyMap b
          code <- (m2e "JSON root element must have code") $ KM.lookup (K.fromString "data") e
          grammar <- (m2e "JSON root element must have grammar") $ KM.lookup (K.fromString "grammar") e
          mp <- pythonMatchPattern grammar
          let c = do
                  -- _ <- error $ show $ mp
                  r <- case matchAndCollapse mp return code of
                          MatchFailure s -> Left ("MatchFailure: " ++ s)
                          NoMatch x -> Left ("NoMatch: " ++ x)
                          MatchSuccess (f, r) -> Right $ (KM.fromList [
                            -- (K.fromString "tree", toJSON $ MatchObjectPartialResult (Object (KM.fromList [])) (KM.fromList [])),
                            (K.fromString "grammar", toJSON $ mp),
                            (K.fromString "funnel", (Array . V.fromList) f),
                            (K.fromString "t1", String $ T.pack $ show mp),
                            (K.fromString "t2", String $ T.pack $ show code),
                            (K.fromString "result", r {-(String . T.pack) $ (show r) ++ "\n\n" ++ (show mp)-})])
                  return (Object r)
          case c of
              Left e -> Right $ Object (KM.fromList [
                (K.fromString "error", (String . T.pack) ("Error: " ++ e)),
                (K.fromString "result", Null),
                (K.fromString "grammar", toJSON $ mp),
                (K.fromString "funnel", Null),
                (K.fromString "t1", String $ T.pack $ show mp),
                (K.fromString "t2", String $ T.pack $ show code)
                ])
              Right r -> Right r
  let f = case a of
               Left _ -> status (Status {statusCode = 400, statusMessage = "request error"})
               Right _ -> id
  send $ f $ Web.Twain.json $ case a of
       Left e -> Object (KM.fromList [(K.fromString "error", (String . T.pack) ("Error: " ++ e))])
       Right x -> x
-}

missing :: ResponderM a
missing = send $ html "Not found..."
