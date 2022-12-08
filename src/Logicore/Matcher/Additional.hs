module Logicore.Matcher.Additional where

import Data.Aeson
import Logicore.Matcher.Core

matchAndCollapse :: MatchPattern -> (Value -> MatchResult Value) -> Value -> MatchResult ([Value], Value)
matchAndCollapse grammar collapse value = do
  r' <- matchPattern grammar value
  r <- return $ resetUnsignificant r'
  r <- return $ toJSON r
  r'' <- collapse r
  return (gatherFunnel [] r', r'')

matchWithFunnel :: MatchPattern -> Value -> MatchResult ([Value], Value)
matchWithFunnel grammar value = matchAndCollapse grammar return value

