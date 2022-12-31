module Logicore.Matcher.Additional where

import Data.Aeson
import Logicore.Matcher.Core
import qualified Control.Monad.Trans.Writer.Lazy as W

{-
matchPatternPlus :: MatchPattern -> Value -> W.Writer [(MatchPattern, Value, MatchResult MatchPattern)] (MatchResult MatchPattern)
matchPatternPlus m v = do
  let x = matchPattern' matchPattern m v
  W.tell [(m, v, x)]
  return x

resetUnsignificant (MatchObjectPartialResult _ a) = MatchObjectPartialResultU (fmap resetUnsignificant a)
resetUnsignificant (MatchArraySomeResult _ a) = MatchArraySomeResultU ((fmap . fmap) resetUnsignificant a)
resetUnsignificant (MatchSimpleOrResult m) = resetUnsignificant m
resetUnsignificant a = a

matchAndCollapse :: MatchPattern -> (Value -> MatchResult Value) -> Value -> MatchResult ([Value], Value)
matchAndCollapse grammar collapse value = do
  r' <- matchPattern grammar value
  r <- return $ resetUnsignificant r'
  r <- return $ toJSON r
  r'' <- collapse r
  return (gatherFunnel [] r', r'')

matchWithFunnel :: MatchPattern -> Value -> MatchResult ([Value], Value)
matchWithFunnel grammar value = matchAndCollapse grammar return value
-}
