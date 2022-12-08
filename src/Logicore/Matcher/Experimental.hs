{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Logicore.Matcher.Experimental where
import Prelude                    as P
import Data.Aeson
import Logicore.Matcher.Core
import Data.Text                  as T
import Data.Text.Encoding         as T
import Data.Text.IO               as T
import Data.Text.Lazy             as TL
import Data.Text.Lazy.Encoding    as TL
import Data.Text.Lazy.IO          as TL
import Data.Aeson.KeyMap          as KM
import Data.List                  as L
import qualified Data.Vector as V

matchToValueMinimal :: MatchPattern -> Maybe Value
matchToValueMinimal (MatchObject m) = fmap Object $ L.foldl' f (Just mempty) (keys m) -- ifNotEmpty =<< 
  where
    ifNotEmpty m = if KM.null m then Nothing else Just m
    f acc k = do
          acc' <- acc
          v <- KM.lookup k m
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> KM.insert k x acc'
matchToValueMinimal (MatchObjectPartialResult _ m) = fmap Object $ L.foldl' f (Just mempty) (keys m) -- ifNotEmpty =<< 
  where
    ifNotEmpty m = if KM.null m then Nothing else Just m
    f acc k = do
          acc' <- acc
          v <- KM.lookup k m
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> KM.insert k x acc'
matchToValueMinimal (MatchObjectPartialResultU m) = fmap Object $ L.foldl' f (Just mempty) (keys m) -- ifNotEmpty =<< 
  where
    ifNotEmpty m = if KM.null m then Nothing else Just m
    f acc k = do
          acc' <- acc
          v <- KM.lookup k m
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> KM.insert k x acc'
matchToValueMinimal (MatchArraySomeResultU m) = fmap Array $ ifNotEmpty =<< L.foldl' f (Just (V.empty :: V.Vector Value)) arr
  where
    arr = V.fromList $ fmap snd m
    ifNotEmpty m = if V.null m then Nothing else Just m
    f acc v = do
          acc' <- acc
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> V.snoc acc' x
matchToValueMinimal (MatchSimpleOrResult m) = matchToValueMinimal m
matchToValueMinimal (MatchString m) = Just (String m)
matchToValueMinimal (MatchNumber m) = Just (Number m)
matchToValueMinimal (MatchBool m) = Just (Bool m)
matchToValueMinimal MatchNull = Just Null
matchToValueMinimal (MatchAnyResult a) = Just a
matchToValueMinimal MatchIgnoreResult = Nothing -- TODO
--matchToValueMinimal (MatchArrayResult a) = (Array $ V.fromList) $ catMaybes $ fmap matchToValueMinimal a
matchToValueMinimal (MatchArrayResult m) = fmap Array $ ifNotEmpty =<< L.foldl' f (Just (V.empty :: V.Vector Value)) arr
  where
    arr = V.fromList $ m
    ifNotEmpty m = if V.null m then Nothing else Just m
    f acc v = do
          acc' <- acc
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> V.snoc acc' x
matchToValueMinimal MatchLiteral = Just $ String "sovpal aga" -- TODO
matchToValueMinimal (MatchFunnelResult v) = Just v
matchToValueMinimal (MatchFunnelResultM v) = Just v
matchToValueMinimal (MatchArrayContextFreeResult a) = do
  case a of
       SeqNode a -> fmap (Array . V.fromList) $ P.traverse (matchToValueMinimal . MatchArrayContextFreeResult) a
       StarNode a -> fmap (Array . V.fromList) $ P.traverse (matchToValueMinimal . MatchArrayContextFreeResult) a
       PlusNode a -> fmap (Array . V.fromList) $ P.traverse (matchToValueMinimal . MatchArrayContextFreeResult) a
       OptionalNodeValue a -> (matchToValueMinimal . MatchArrayContextFreeResult) a
       OptionalNodeEmpty -> Just Null
       OrNode _ a -> (matchToValueMinimal . MatchArrayContextFreeResult) a
       CharNode a -> matchToValueMinimal a
       x -> error $ "no option: " ++ show x
matchToValueMinimal (MatchArrayOneResult a) = matchToValueMinimal a {-do
  v <- matchToValueMinimal a
  return $ Array $ V.fromList [v]-}
matchToValueMinimal x = error $ show x

matchToValueMinimal' x = (m2mp $ MatchFailure $ "matchToValueMinimal error " ++ show x) $ (matchToValueMinimal x)
