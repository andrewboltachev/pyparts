{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Network.Wai.Handler.Warp (runSettings, defaultSettings, setPort, setTimeout, Settings)
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
import qualified Data.ByteString.Lazy       as BL
import Data.Maybe
import Data.Either
import Data.Aeson.Text (encodeToLazyText)
import qualified Data.List as L

import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State hiding (get)
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.IO.Class (liftIO, MonadIO)

import Logicore.Matcher.Core hiding ((++))
import Logicore.Matcher.Python
import Logicore.Matcher.Additional
import qualified Database.Redis as Redis
import Data.IORef
--import Logicore.Matcher.Python

--import Language.Haskell.TH


main :: IO ()
main = do
  let settings = L.foldr ($) defaultSettings ([setTimeout (5 * 60), setPort 3042] :: [Settings -> Settings])
  theRef <- newIORef mempty
  runSettings settings $
    foldr ($)
      (notFound missing)
      ([ get "/" index
      , post "echo:name" echo
      , get "load" (load theRef)
      --, post "python-matcher-1" pythonMatcher1
      --, post "json-matcher-1" jsonMatcher1

      -- fn endpoints
      , post "/matchPattern" (fnEndpoint mkMatchPattern theRef)
      --, post "/matchPatternWithFunnel" (fnEndpoint mkMatchPatternWithFunnel theRef)
      --, post "/matchPatternWithFunnelFile" matchPatternWithFunnelFile
      , post "/matchToFunnel" (fnEndpoint mkMatchToFunnel theRef)
      , post "/matchToFunnelOptimized" (fnEndpoint mkMatchToFunnelOptimized theRef)
      , post "/matchToFunnelSuggestions" (fnEndpoint mkMatchToFunnelSuggestions theRef)
      , post "/matchToThin" (fnEndpoint mkMatchToThin theRef)
      , post "/matchResultToPattern" (fnEndpoint mkMatchResultToPattern theRef)
      , post "/matchResultToValue" (fnEndpoint mkMatchResultToValue theRef)
      , post "/matchResultToThinValue" (fnEndpoint mkMatchResultToThinValue theRef)
      , post "/thinPattern" (fnEndpoint mkThinPattern theRef)
      , post "/applyOriginalValueDefaults" (fnEndpoint mkApplyOriginalValueDefaults theRef)
      , post "/valueToExactGrammar" (fnEndpoint mkValueToExactGrammar theRef)
      , post "/pythonValueToExactGrammar" (fnEndpoint mkPythonValueToExactGrammar theRef)
      , post "/pythonModValueToGrammar" (fnEndpoint mkPythonModValueToGrammar theRef)
      , post "/valueToExactResult" (fnEndpoint mkValueToExactResult theRef)
      --, post "/pythonStep1" (fnEndpoint mkPythonStep1 theRef)
      --, post "/pythonStep2" (fnEndpoint mkPythonStep2 theRef)
      --, post "/pythonStep0" (fnEndpoint mkPythonStep0 theRef)
      ] :: [Application -> Application])


index :: ResponderM a
index = send $ html "Hello World!"

echo :: ResponderM a
echo = do
  name <- param "name"
  send $ html $ "Hello, " <> name

load :: IORef (KeyMap Value) -> ResponderM a
load theRef = do
  conn <- liftIO $ Redis.connect Redis.defaultConnectInfo
  ks <- liftIO $ Redis.runRedis conn $ Redis.keys $ "logicore:figma:*"
  vv <- case ks of
     Right ks' -> do
                    let ff acc k = do
                                 let kk = (K.fromText (T.replace "logicore:figma:" "" (T.decodeUtf8 k)))
                                 liftIO $ print k
                                 acc' <- acc
                                 r <- liftIO $ Redis.runRedis conn $ Redis.get $ k
                                 return $ KM.insert kk ((fromJust $ decode $ BL.fromStrict $ fromJust $ either (error "foo") id r) :: Value) acc'
                    L.foldl' ff (return mempty) ks'
     Left e -> error $ "keys error"
  liftIO $ writeIORef theRef vv
  send $ html $ "Read ok"




--exp1 = runQ [| \ x -> x  |] >>= putStrLn.pprint

{-

            code <- (m2e "JSON root element must have code") $ KM.lookup (K.fromString "data") e
            grammar <- (m2e "JSON root element must have grammar") $ KM.lookup (K.fromString "grammar") e
            mp <- (m2e "Cannot decode MatchPattern from presented grammar") $ (
              ((decode . encode) grammar) :: Maybe MatchPattern) -- TODO
matchAndCollapse mp return code
-}

getGrammarArg :: MonadIO m => KeyMap Value -> ExceptT String m (KeyMap MatchPattern)
getGrammarArg e = case KM.lookup (K.fromString "grammar") e of
                    (Just (Object x)) -> do
                      grammar' <- ExceptT $ return $ (maybe (Left "error") Right) $ (((decode . encode) x) :: Maybe (KM.KeyMap MatchPattern)) -- TODO
                      return $ grammar'
                    (Just _) -> ExceptT $ return $ Left $ "JSON element grammar, when present should be of KeyMap type"
                    Nothing -> return $ mempty

getToFileArg :: KeyMap Value -> Maybe String
getToFileArg e = (KM.lookup (K.fromString "toFile") e) >>= asString >>= return . T.unpack

mkMatchPattern :: (Object -> MatchStatusT IO Value)
mkMatchPattern e = do
  value <- (m2mst $ matchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  output <- matchPattern mp value
  outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "result", outputValue)])

{-mkMatchPatternWithFunnel :: (Object -> MatchStatusT IO Value)
mkMatchPatternWithFunnel e = do
  value <- (m2mst $ matchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  output <- matchPattern mp value
  funnelResult <- return $ gatherFunnel output
  outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [
    (K.fromString "result", outputValue),
    (K.fromString "funnel", Array $ V.fromList $ funnelResult)])-}

mkMatchToFunnel :: (Object -> MatchStatusT IO Value)
mkMatchToFunnel e = do
  value <- (m2mst $ matchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  funnelResult <- matchToFunnel mp value
  return $ Object $ (KM.fromList [
    (K.fromString "funnel", Array $ funnelResult)])

mkMatchToFunnelOptimized :: (Object -> MatchStatusT IO Value)
mkMatchToFunnelOptimized e = do
  value <- (m2mst $ matchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  funnelResult <- matchToFunnelOptimized mp value
  return $ Object $ (KM.fromList [
    (K.fromString "funnel", Array $ funnelResult)])

mkMatchToFunnelSuggestions :: (Object -> MatchStatusT IO Value)
mkMatchToFunnelSuggestions e = do
  value <- (m2mst $ matchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  suggestionsResult <- matchToFunnelSuggestions mp value
  return $ Object $ (KM.fromList [
    (K.fromString "funnelSuggestions", suggestionsResult)])

mkMatchToThin :: (Object -> MatchStatusT IO Value)
mkMatchToThin e = do
  value <- (m2mst $ matchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  funnelResult <- matchToThin mp value
  return $ Object $ (KM.fromList [
    (K.fromString "thinValue", maybe Null id funnelResult)]) -- TODO replace null

--matchPatternWithFunnelFile :: (Object -> MatchStatusT IO Value) -> ResponderM b
-- TODO study monad transformers *FACEPALM*
{-matchPatternWithFunnelFile = do
    let err e = send $ Web.Twain.json $ Object (KM.fromList [(K.fromString "error", (String . T.pack) ("Error: " ++ e))])
    b <- (fromBody :: ResponderM Value)
    let e = do
        e' <- (m2e "JSON root element must be a map") $ asKeyMap b
        value'' <- (m2e "JSON root element must have value") $ KM.lookup (K.fromString "value") e'
        value' <- (m2e "value key should be String") $ asString value''
        return $ value'

    case e of
        Left e -> err e
        Right x -> do
            fdata <- liftIO $ ((fmap decode $ BL.readFile (T.unpack x)) :: IO (Maybe Value))
            case fdata of
                Nothing -> err "JSON parsing error"
                (Just x) -> do
                    let f :: MatchStatusT IO Value
                        f = do
                            e' <- (m2mst $ matchFailure "JSON root element must be a map") $ asKeyMap b
                            pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e'
                            mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
                            funnelResult <- return $ gatherFunnel output
                            outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
                            return $ Object $ (KM.fromList [
                                (K.fromString "result", outputValue),
                                (K.fromString "funnel", Array $ V.fromList $ funnelResult)])

                    let a = do
                        r <- case f of
                            MatchFailure s -> Left ("MatchFailure: " ++ s)
                            NoMatch x -> Left ("NoMatch: " ++ x)
                            MatchSuccess r -> Right $ r
                        return r
                    send $ Web.Twain.json $ case a of
                        Left e -> Object (KM.fromList [(K.fromString "error", (String . T.pack) ("Error: " ++ e))])
                        Right x -> x-}

mkThinPattern :: (Object -> MatchStatusT IO Value)
mkThinPattern e = do
  thinValue <- return $ KM.lookup (K.fromString "thinValue") e
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  output <- thinPattern mp thinValue
  outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "result", outputValue)])

mkApplyOriginalValueDefaults :: (Object -> MatchStatusT IO Value)
mkApplyOriginalValueDefaults e = do

  result1 <- (m2mst $ matchFailure "JSON root element must have result1") $ KM.lookup (K.fromString "result1") e
  r1 <- (m2mst $ matchFailure "Cannot decode MatchResult from presented pattern") $ (((decode . encode) result1) :: Maybe MatchResult) -- TODO

  result2 <- (m2mst $ matchFailure "JSON root element must have result2") $ KM.lookup (K.fromString "result2") e
  r2 <- (m2mst $ matchFailure "Cannot decode MatchResult from presented pattern") $ (((decode . encode) result2) :: Maybe MatchResult) -- TODO

  output <- return $ applyOriginalValueDefaults r1 (Just r2)
  outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "result", outputValue)])

mkMatchResultToPattern :: (Object -> MatchStatusT IO Value)
mkMatchResultToPattern e = do
  result <- (m2mst $ matchFailure "JSON root element must have result") $ KM.lookup (K.fromString "result") e
  mr <- (m2mst $ matchFailure "Cannot decode MatchResult from presented result") $ (((decode . encode) result) :: Maybe MatchResult) -- TODO
  output <- return $ matchResultToPattern mr
  outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "pattern", outputValue)])

mkMatchResultToValue :: (Object -> MatchStatusT IO Value)
mkMatchResultToValue e = do
  result <- (m2mst $ matchFailure "JSON root element must have result") $ KM.lookup (K.fromString "result") e
  mr <- (m2mst $ matchFailure "Cannot decode MatchResult from presented result") $ (((decode . encode) result) :: Maybe MatchResult) -- TODO
  output <- return $ matchResultToValue mr
  return $ Object $ (KM.fromList [(K.fromString "value", output)])

mkMatchResultToThinValue :: (Object -> MatchStatusT IO Value)
mkMatchResultToThinValue e = do
  result <- (m2mst $ matchFailure "JSON root element must have result") $ KM.lookup (K.fromString "result") e
  mr <- (m2mst $ matchFailure "Cannot decode MatchResult from presented result") $ (((decode . encode) result) :: Maybe MatchResult) -- TODO
  output <- matchResultToThinValue mr
  let res = case output of
                 Just x -> x
                 Nothing -> Null
  return $ Object $ (KM.fromList [(K.fromString "thinValue", res)])

mkValueToExactGrammar :: (Object -> MatchStatusT IO Value)
mkValueToExactGrammar e = do
  value <- (m2mst $ matchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  output <- return $ valueToExactGrammar value
  outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "grammar", outputValue)])

mkPythonValueToExactGrammar :: (Object -> MatchStatusT IO Value)
mkPythonValueToExactGrammar e = do
  pythonValue <- (m2mst $ matchFailure "JSON root element must have pythonValue") $ KM.lookup (K.fromString "pythonValue") e
  output <- return $ pythonValueToExactGrammar pythonValue
  -- outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "grammar", String $ T.pack $ show output)])

mkPythonModValueToGrammar :: (Object -> MatchStatusT IO Value)
mkPythonModValueToGrammar e = do
  pythonModValue <- (m2mst $ matchFailure "JSON root element must have pythonModValue") $ KM.lookup (K.fromString "pythonModValue") e
  output <- liftIO $ runIdentityT $ pythonModValueToGrammar pythonModValue
  outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "grammar", outputValue)])

mkValueToExactResult :: (Object -> MatchStatusT IO Value)
mkValueToExactResult e = do
  value <- (m2mst $ matchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  output <- valueToExactResult value
  outputValue <- (m2mst $ matchFailure "decode error") $ decode $ encode $ output
  return $ Object $ (KM.fromList [(K.fromString "result", outputValue)])

{-mkPythonStep0 :: (Object -> MatchStatusT IO Value)
mkPythonStep0 e = do
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  pattern <- (m2mst $ matchFailure "err1") $ asKeyMap pattern
  pattern <- (m2mst $ matchFailure "err2") $ KM.lookup (K.fromString "body") pattern
  pattern <- (m2mst $ matchFailure "err3") $ asArray pattern
  pattern <- (m2mst $ matchFailure "err4") $ safeHead pattern
  pattern <- return $ withoutPythonUnsignificantKeys pattern
  mr <- matchPattern pythonStep0Grammar pattern
  rr <- matchResultToThinValue mr
  return $ Object $ case rr of
    Just x -> KM.fromList [(K.fromString "thinValue", x)]
    Nothing -> KM.empty

mkPythonStep1 :: (Object -> MatchStatusT IO Value)
mkPythonStep1 e = do
  value <- (m2mst $ matchFailure "JSON root element must have value") $ KM.lookup (K.fromString "value") e
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  pattern <- return $ withoutPythonUnsignificantKeys pattern
  value <- return $ withoutPythonUnsignificantKeys value
  pattern <- return $ valueToPythonGrammar pattern
  --_ <- error $ show pattern ++ "\n\n\n" ++ show value
  mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  mr <- matchPattern mempty mp value
  rr <- matchResultToThinValue mr
  return $ Object $ case rr of
                         Just x -> KM.fromList [(K.fromString "thinValue", x)]
                         Nothing -> KM.empty

mkPythonStep2 :: (Object -> MatchStatusT IO Value)
mkPythonStep2 e = do
  thinValue <- (m2mst $ matchFailure "JSON root element must have thin grammar") $ KM.lookup (K.fromString "thinValue") e
  pattern <- (m2mst $ matchFailure "JSON root element must have pattern") $ KM.lookup (K.fromString "pattern") e
  pattern <- return $ withoutPythonUnsignificantKeys pattern
  pattern <- return $ valueToPythonGrammar pattern
  mp <- (m2mst $ matchFailure "Cannot decode MatchPattern from presented pattern") $ (((decode . encode) pattern) :: Maybe MatchPattern) -- TODO
  --mr <- matchPattern mempty mp value
  return $ Object $ case thinPattern mp (Just thinValue) of
                         MatchSuccess s -> (KM.singleton "code" $ matchResultToValue $ s)
                         NoMatch s -> (KM.singleton "error" $ (String . T.pack) $ "NoMatch: " ++ s)
                         MatchFailure s -> (KM.singleton "error" $ (String . T.pack) $ "matchFailure: " ++ s)-}

fnEndpoint :: (Object -> MatchStatusT IO Value) -> IORef (KeyMap Value) -> ResponderM b
fnEndpoint f theRef = do
    --_ <- liftIO $ print "fnEndpoint"
    b <- (fromBody :: ResponderM Value)
    a <- runExceptT $ do
            e <- (m2et "JSON root element must be a map") $ asKeyMap b
            grammar <- getGrammarArg e
            let toFile = getToFileArg e
            conn <- liftIO $ Redis.connect Redis.defaultConnectInfo
            vv <- liftIO $ runReaderT (evalStateT (runMatchStatusT $ f e) mempty) $ MatcherEnv { redisConn = conn, grammarMap = grammar, indexing = False, dataRef = theRef }
            r <- (ExceptT . return) $ case vv of
                    MatchFailure s -> Left ("matchFailureee: " ++ T.unpack s)
                    NoMatch x -> Left ("NoMatch: " ++ T.unpack x)
                    MatchSuccess r -> Right $ r
            case toFile of
                    Just filename -> do
                      liftIO $ TL.writeFile filename (encodeToLazyText r)
                      return $ String "ok"
                    Nothing -> return r
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
                  MatchFailure s -> Left ("matchFailure: " ++ s)
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
                          MatchFailure s -> Left ("matchFailure: " ++ s)
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
