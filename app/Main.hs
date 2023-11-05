{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Network.Wai.Handler.Warp (runSettings, defaultSettings, setPort, setTimeout)
import Web.Twain
import Data.Aeson
import qualified Data.Aeson.KeyMap          as KM
import Data.Aeson.KeyMap (KeyMap)
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
  let settings = foldr ($) defaultSettings [setTimeout (60 * 60), setPort 3042]
  runSettings settings $
    foldr ($)
      (notFound missing)
      [ get "/" index
      , post "echo:name" echo
      --, post "python-matcher-1" pythonMatcher1
      --, post "json-matcher-1" jsonMatcher1

      -- fn endpoints
      , post "/matchPattern" (fnEndpoint mkMatchPattern)
      , post "/matchPatternWithFunnel" (fnEndpoint mkMatchPatternWithFunnel)
      , post "/matchResultToPattern" (fnEndpoint mkMatchResultToPattern)
      , post "/matchResultToValue" (fnEndpoint mkMatchResultToValue)
      , post "/matchResultToThinValue" (fnEndpoint mkMatchResultToThinValue)
      , post "/thinPattern" (fnEndpoint mkThinPattern)
      , post "/applyOriginalValueDefaults" (fnEndpoint mkApplyOriginalValueDefaults)
      , post "/valueToExactGrammar" (fnEndpoint mkValueToExactGrammar)
      , post "/valueToExactResult" (fnEndpoint mkValueToExactResult)
      , post "/pythonStep1" (fnEndpoint mkPythonStep1)
      , post "/pythonStep2" (fnEndpoint mkPythonStep2)
      , post "/pythonStep0" (fnEndpoint mkPythonStep0)
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

getGrammarArg :: KeyMap Value -> MatchStatus (KeyMap MatchPattern)
getGrammarArg e = case KM.lookup (K.fromString "grammar") e of
                    (Just (Object x)) -> do
                      grammar' <- (m2ms $ MatchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) x) :: Maybe (KM.KeyMap MatchPattern)) -- TODO
                      return $ grammar'
                    (Just _) -> MatchFailure $ "JSON element grammar, when present should be of KeyMap type"
                    Nothing -> return $ mempty

mkMatchPattern :: (Object -> MatchStatus Value)
mkMatchPattern e = do
  grammar <- getGrammarArg e
  value <- (m2ms $ MatchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2ms $ MatchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2ms $ MatchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  output <- matchPattern grammar mp value
  outputValue <- (m2ms $ MatchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "result", outputValue)])

mkMatchPatternWithFunnel :: (Object -> MatchStatus Value)
mkMatchPatternWithFunnel e = do
  grammar <- getGrammarArg e
  value <- (m2ms $ MatchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2ms $ MatchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2ms $ MatchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  output <- matchPattern grammar mp value
  funnelResult <- return $ gatherFunnel output
  outputValue <- (m2ms $ MatchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [
    (K.fromString "result", outputValue),
    (K.fromString "funnel", Array $ V.fromList $ funnelResult)])

mkThinPattern :: (Object -> MatchStatus Value)
mkThinPattern e = do
  grammar <- getGrammarArg e
  thinValue <- return $ KM.lookup (K.fromString "thinValue") e
  pattern <- (m2ms $ MatchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2ms $ MatchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  output <- thinPattern grammar mp thinValue
  outputValue <- (m2ms $ MatchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "result", outputValue)])

mkApplyOriginalValueDefaults :: (Object -> MatchStatus Value)
mkApplyOriginalValueDefaults e = do

  result1 <- (m2ms $ MatchFailure "JSON root element must have result1") $ KM.lookup (K.fromString "result1") e
  r1 <- (m2ms $ MatchFailure "Cannot decode MatchResult from presented pattern") $ (((decode . encode) result1) :: Maybe MatchResult) -- TODO

  result2 <- (m2ms $ MatchFailure "JSON root element must have result2") $ KM.lookup (K.fromString "result2") e
  r2 <- (m2ms $ MatchFailure "Cannot decode MatchResult from presented pattern") $ (((decode . encode) result2) :: Maybe MatchResult) -- TODO

  output <- return $ applyOriginalValueDefaults r1 (Just r2)
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
  grammar <- getGrammarArg e
  result <- (m2ms $ MatchFailure "JSON root element must have result") $ KM.lookup (K.fromString "result") e
  mr <- (m2ms $ MatchFailure "Cannot decode MatchResult from presented result") $ (((decode . encode) result) :: Maybe MatchResult) -- TODO
  output <- matchResultToThinValue grammar mr
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

mkPythonStep0 :: (Object -> MatchStatus Value)
mkPythonStep0 e = do
  grammar <- getGrammarArg e
  pattern <- (m2ms $ MatchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  pattern <- (m2ms $ MatchFailure "err1") $ asKeyMap pattern
  pattern <- (m2ms $ MatchFailure "err2") $ KM.lookup (K.fromString "body") pattern
  pattern <- (m2ms $ MatchFailure "err3") $ asArray pattern
  pattern <- (m2ms $ MatchFailure "err4") $ safeHead pattern
  pattern <- return $ withoutPythonUnsignificantKeys pattern
  mr <- matchPattern grammar pythonStep0Grammar pattern
  rr <- matchResultToThinValue grammar mr
  return $ Object $ case rr of
    Just x -> KM.fromList [(K.fromString "thinValue", x)]
    Nothing -> KM.empty

mkPythonStep1 :: (Object -> MatchStatus Value)
mkPythonStep1 e = do
  grammar <- getGrammarArg e
  value <- (m2ms $ MatchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2ms $ MatchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  pattern <- return $ withoutPythonUnsignificantKeys pattern
  value <- return $ withoutPythonUnsignificantKeys value
  pattern <- return $ valueToPythonGrammar pattern
  --_ <- error $ show pattern ++ "\n\n\n" ++ show value
  mp <- (m2ms $ MatchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  mr <- matchPattern mempty mp value
  rr <- matchResultToThinValue grammar mr
  return $ Object $ case rr of
                         Just x -> KM.fromList [(K.fromString "thinValue", x)]
                         Nothing -> KM.empty

mkPythonStep2 :: (Object -> MatchStatus Value)
mkPythonStep2 e = do
  grammar <- getGrammarArg e
  thinValue <- (m2ms $ MatchFailure "JSON root element must have thin grammar") $ KM.lookup (K.fromString "thinValue") e
  pattern <- (m2ms $ MatchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  pattern <- return $ withoutPythonUnsignificantKeys pattern
  pattern <- return $ valueToPythonGrammar pattern
  mp <- (m2ms $ MatchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  --mr <- matchPattern mempty mp value
  return $ Object $ case thinPattern grammar mp (Just thinValue) of
                         MatchSuccess s -> (KM.singleton "code" $ matchResultToValue $ s)
                         NoMatch s -> (KM.singleton "error" $ (String . T.pack) $ "NoMatch: " ++ s)
                         MatchFailure s -> (KM.singleton "error" $ (String . T.pack) $ "MatchFailure: " ++ s)

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
