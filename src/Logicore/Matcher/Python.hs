{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

module Logicore.Matcher.Python where

import qualified Data.Vector.Generic
--import qualified Data.Set
import qualified Data.List        as L
import GHC.Generics
import Data.Aeson
--import Data.ByteString            as B
--import Data.ByteString.Lazy       as BL
import Data.Text                  as T
--import Data.Text.Encoding         as T
--import Data.Text.IO               as T
import Data.Text.Lazy             as TL
import Data.Text.Lazy.Encoding    as TL
--import Data.Text.Lazy.IO          as TL
--import Data.Map                   as M
import Data.Aeson.KeyMap          as KM
import Data.Aeson.Key             as K
import qualified Data.Scientific as Sci
import qualified Data.Vector as V
import Prelude                    as P
import Control.Monad()
import Control.Comonad
--import qualified Data.ByteString.UTF8       as BLU
--import Logicore.Matcher.Utils
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Functor.Foldable
import Data.Bifunctor
import Data.Maybe (isJust, fromJust)
import Data.Monoid
import qualified Data.Set                     as S

import Test.QuickCheck
import Test.QuickCheck.Gen (oneof)
import Test.Hspec

import Language.Haskell.TH
import Language.Haskell.TH.Datatype as TH.Abs
import Language.Haskell.TH.Datatype.TyVarBndr
import Language.Haskell.TH.Syntax (mkNameG_tc, mkNameG_v)

import Logicore.Matcher.ValueBaseFunctor
import Logicore.Matcher.Core
import Logicore.Matcher.Helpers

import Logicore.Matcher.Additional
import Logicore.Matcher.Experimental
-- python

pythonUnsignificantKeys :: [Key]
pythonUnsignificantKeys = fmap fromString [
  "lpar",
  "rpar",
  "first_line",
  "empty_lines",
  "indent",
  "newline",
  "lpar",
  "rpar",
  "colon",
  "header",
  "footer",
  "leading_lines",
  "lines_after_decorators",
  "leading_whitespace",
  "previous_whitespace_state",
  "trailing_whitespace",
  "whitespace",
  "whitespace_after",
  "whitespace_after_arg",
  "whitespace_after_as",
  "whitespace_after_assert",
  "whitespace_after_at",
  "whitespace_after_await",
  "whitespace_after_case",
  "whitespace_after_class",
  "whitespace_after_cls",
  "whitespace_after_colon",
  "whitespace_after_def",
  "whitespace_after_del",
  "whitespace_after_else",
  "whitespace_after_equal",
  "whitespace_after_except",
  "whitespace_after_expression",
  "whitespace_after_for",
  "whitespace_after_from",
  "whitespace_after_func",
  "whitespace_after_global",
  "whitespace_after_if",
  "whitespace_after_import",
  "whitespace_after_in",
  "whitespace_after_indicator",
  "whitespace_after_kwds",
  "whitespace_after_lambda",
  "whitespace_after_match",
  "whitespace_after_name",
  "whitespace_after_nonlocal",
  "whitespace_after_param",
  "whitespace_after_raise",
  "whitespace_after_return",
  "whitespace_after_star",
  "whitespace_after_test",
  "whitespace_after_value",
  "whitespace_after_walrus",
  "whitespace_after_while",
  "whitespace_after_with",
  "whitespace_after_yield",
  "whitespace_before",
  "whitespace_before_args",
  "whitespace_before_as",
  "whitespace_before_colon",
  "whitespace_before_else",
  "whitespace_before_equal",
  "whitespace_before_expression",
  "whitespace_before_from",
  "whitespace_before_if",
  "whitespace_before_import",
  "whitespace_before_in",
  "whitespace_before_indicator",
  "whitespace_before_name",
  "whitespace_before_params",
  "whitespace_before_patterns",
  "whitespace_before_rest",
  "whitespace_before_test",
  "whitespace_before_value",
  "whitespace_before_walrus",
  "whitespace_between"]


withoutPythonUnsignificantKeys :: Value -> Value
withoutPythonUnsignificantKeys = cata go
  where
    go (ObjectF a) = Object $ KM.filterWithKey (\k v -> not $ P.elem k pythonUnsignificantKeys) a
    go (ArrayF a) = Array a
    go (StringF a) = String a
    go (NumberF a) = Number a
    go (BoolF a) = Bool a
    go NullF = Null
  

valueToPythonGrammar :: Value -> MatchPattern
valueToPythonGrammar = cata go
  where
    go (ObjectF a) = MatchObjectFull (fmap KeyReq a)
    go (ArrayF a) = MatchArrayContextFree $ Seq $ (fmap Char) $ V.toList a
    go (StringF a) = MatchStringExact a
    go (NumberF a) = MatchNumberExact a
    go (BoolF a) = MatchBoolExact a
    go NullF = MatchNull

--

matchArrayOne x = MatchArrayContextFree $ Seq [Char x]

if_arg = (fromString "args", KeyReq $ matchArrayOne $ MatchObjectFull (fromList [
    (fromString "comma", KeyReq $ MatchStringExact "MaybeSentinel.DEFAULT")
  , (fromString "equal", KeyReq $ MatchStringExact "MaybeSentinel.DEFAULT")
  , (fromString "keyword", KeyReq $ MatchNull)
  , (fromString "star", KeyReq $ MatchStringExact "")
  , (fromString "type", KeyReq $ MatchStringExact "Arg")
  , (fromString "value", KeyReq $ MatchObjectFull (fromList [
      (fromString "type", KeyReq $ MatchStringExact "SimpleString")
      , (fromString "value", KeyReq $ MatchStringAny)
  ]))
  ]))

simple_or_grammar = MatchObjectFull (fromList [
    (fromString "type", KeyReq $ MatchStringExact $ T.pack "If"), -- top
    (fromString "orelse", KeyReq $ MatchNull), -- bottom
    (fromString "test",
      KeyReq $ MatchObjectFull (fromList [ -- top
        (fromString "type", KeyReq $ MatchStringExact $ T.pack "Call")
        , (fromString "func", KeyReq $ MatchObjectFull (fromList [
          (fromString "type", KeyReq $ MatchStringExact $ T.pack "Name"),
          (fromString "value", KeyReq $ MatchStringExact $ T.pack "__simpleor")
        ]))
        , if_arg -- TODO
      ])
    ),
    (fromString "body",
      KeyReq $ MatchObjectFull (fromList [ -- top
        (fromString "type", KeyReq $ MatchStringExact $ T.pack "IndentedBlock"),
        (fromString "body", KeyReq $ MatchArrayContextFree $ Seq [
          (Plus (Char $ MatchObjectFull (fromList [
              (fromString "type", KeyReq $ MatchStringExact $ T.pack "If"),
              (fromString "orelse", KeyReq $ MatchNull), -- bottom
              (fromString "test",
                KeyReq $ MatchObjectFull (fromList [ -- top
                  (fromString "type", KeyReq $ MatchStringExact $ T.pack "Call"),
                  (fromString "func", KeyReq $ MatchObjectFull (fromList [
                    (fromString "type", KeyReq $ MatchStringExact $ T.pack "Name"),
                    (fromString "value", KeyReq $ MatchStringExact $ T.pack "__option")
                  ]))
                  , if_arg -- TODO
                ])
              ),
              (fromString "body",
                KeyReq $ MatchObjectFull (fromList [
                  (fromString "type", KeyReq $ MatchStringExact $ T.pack "IndentedBlock"),
                  (fromString "body", KeyReq $ MatchAny)
                ]))
            ])
          ))      
        ])
      ])
    )
  ])

pythonStep0Grammar = simple_or_grammar

{-

--  collapse utils begin
selectKey k (Object a) = KM.lookup k a
selectKey _ _ = Nothing

collapse' = selectKey (fromString "body")

doCollapse f v = case f v of
                     Nothing -> MatchFailure ("collapse problem" ++ "\n" ++ ((TL.unpack . TL.decodeUtf8 . encode) v))
                     Just x -> MatchSuccess x

sList f (Array a) = case P.traverse f a of
                     MatchFailure x -> MatchFailure x
                     MatchSuccess x -> MatchSuccess $ Array x
sList _ s = error (show s)

sBody = doCollapse (selectKey (fromString "body"))
-- collapse utils end

simple_or_grammar = MatchObjectPartial (fromList [
    (fromString "type", MatchString $ T.pack "If"), -- top
    (fromString "orelse", MatchNull), -- bottom
    (fromString "test",
      MatchObjectPartial (fromList [ -- top
        (fromString "type", MatchString $ T.pack "Call"),
        (fromString "func", MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "Name"),
          (fromString "value", MatchString $ T.pack "__simpleor")
        ]))
        --,(fromString "args", MatchArrayOne $ MatchAny) -- TODO
      ])
    ),
    (fromString "body",
      MatchObjectPartial (fromList [ -- top
        (fromString "type", MatchString $ T.pack "IndentedBlock"),
        (fromString "body", MatchArray $ MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__option")
              ]))
              --,(fromString "args", MatchArrayOne $ MatchAny) -- TODO
            ])
          ),
          (fromString "body",
            MatchObjectPartial (fromList [
              (fromString "type", MatchString $ T.pack "IndentedBlock"),
              (fromString "body", MatchArrayOne $ MatchAny)
            ]))
        ]))
      ])
    )
  ])

simple_or_collapse = (sBody >=> sBody >=> (sList (sBody >=> sBody)))


or_grammar = MatchObjectPartial (fromList [
    (fromString "type", MatchString $ T.pack "If"), -- top
    (fromString "orelse", MatchNull), -- bottom
    (fromString "test",
      MatchObjectPartial (fromList [ -- top
        (fromString "type", MatchString $ T.pack "Call"),
        (fromString "func", MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "Name"),
          (fromString "value", MatchString $ T.pack "__or")
        ]))
        --,(fromString "args", MatchArrayOne $ MatchAny) -- TODO
      ])
    ),
    (fromString "body",
      MatchObjectPartial (fromList [ -- top
        (fromString "type", MatchString $ T.pack "IndentedBlock"),
        (fromString "body", MatchArray $ MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__option")
              ])),
              -- ["comma","equal","keyword","star","type","value","whitespace_after_arg","whitespace_after_star"]
              (fromString "args", MatchArrayOne $
                MatchObjectPartial (fromList [ -- top
                  (fromString "type", MatchString $ T.pack "Arg"),
                  (fromString "value", MatchObjectPartial (fromList [
                    (fromString "value", MatchLiteral)
                  ]))
                ])
              )
            ])
          ),
          (fromString "body",
            MatchObjectPartial (fromList [
              (fromString "type", MatchString $ T.pack "IndentedBlock"),
              (fromString "body", MatchArray $ MatchAny)
            ]))
        ]))
      ])
    )
  ])

or_collapse = (sBody >=> sBody >=> (sList (sBody >=> sBody)))


star_grammar = MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__star")
              ]))
              --, (fromString "args", MatchArrayOne $ MatchAny) -- TODO
            ])
          ),
          (fromString "body", MatchAny) 
        ])

star_collapse = (sBody >=> sBody) -- :: MatchResult Value

ib_or_module_grammar = MatchObjectPartial (fromList [
          (fromString "type", MatchSimpleOr [
                          MatchString $ T.pack "IndentedBlock",
                          MatchString $ T.pack "Module"
                        ]),
          (fromString "body",
            MatchArray $ MatchAny
          )
        ])

any_grammar = MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__any")
              ]))
              --,(fromString "args", MatchArrayOne $ MatchAny) -- TODO
            ])
          )
        ])

any_collapse x = return x

simple_or_success (Array v) = fmap MatchSimpleOr $ P.traverse pythonMatchPattern (V.toList v)
simple_or_success _ = Left "wrong grammar"

optional_grammar = MatchObjectPartial (fromList [
          (fromString "type", MatchString $ T.pack "If"),
          (fromString "test",
            MatchObjectPartial (fromList [ -- top
              (fromString "type", MatchString $ T.pack "Call"),
              (fromString "func", MatchObjectPartial (fromList [
                (fromString "type", MatchString $ T.pack "Name"),
                (fromString "value", MatchString $ T.pack "__maybe")
              ]))
              --, (fromString "args", MatchArrayOne $ MatchAny) -- TODO
            ])
          ),
          (fromString "body", MatchAny)
        ])

optional_collapse = (sBody >=> sBody) -- :: MatchResult Value

optional_success = pythonMatchContextFreePattern


pythonElementMatches = [
  (optional_grammar, sBody >=> sBody, (\x -> fmap Optional (pythonMatchContextFreePattern x))),
  (star_grammar, sBody >=> sBody, (\x -> fmap Star (pythonMatchContextFreePattern x)))
  ] :: [(MatchPattern, Value -> MatchResult Value, Value -> Either String (ContextFreeGrammar MatchPattern))]

pythonMatchContextFreePattern :: Value -> Either String (ContextFreeGrammar MatchPattern)
pythonMatchContextFreePattern (Array a) = fmap Seq $ L.foldl' f (Right mempty) (V.toList a)
  where f acc' e = do
            acc <- acc'
            --e' <- ((m2e "not a keymap") asKeyMap) e
            let x1 = L.foldr g defaultElementMatch pythonElementMatches
                  where defaultElementMatch = fmap Char (pythonMatchPattern e)
                        g (grammar, collapseFn, successFn) b =
                          case matchAndCollapse' grammar collapseFn e of
                              MatchFailure s -> Left s
                              MatchSuccess (_, s) -> successFn s
                              --MatchSuccess _ -> Left "wrong grammar"
                              NoMatch _ -> b
            e' <- x1
            return $ acc ++ [e']


pythonMatchContextFreePattern x = Left ("pattern error: " ++ show x)

ib_or_module_success :: Value -> Either String MatchPattern
ib_or_module_success v = do
  cfg <- pythonMatchContextFreePattern v
  return $ MatchObjectPartial $ fromList [(fromString "body", MatchArrayContextFree cfg)]

pythonMapMatches = [
    (simple_or_grammar, simple_or_collapse, simple_or_success)
  , (any_grammar, any_collapse, const $ Right MatchAny)
  , (ib_or_module_grammar, sBody, ib_or_module_success)
  ] :: [(MatchPattern, Value -> MatchResult Value, Value -> Either String MatchPattern)]

pythonMatchPattern :: Value -> Either String MatchPattern
pythonMatchPattern (Array a) = fmap MatchArrayExact (L.foldl' f (Right mempty) (V.toList a))
  where f acc e = do
          acc' <- acc
          e' <- pythonMatchPattern e
          return $ acc' ++ [e']

pythonMatchPattern (Object a) = L.foldr f defaultMapMatch pythonMapMatches
  where x = Object a
        defaultMapMatch = fmap MatchObjectPartial $ P.traverse pythonMatchPattern a'

                            where a' = KM.filterWithKey (\k _ -> not ((toString k) `P.elem` pythonUnsignificantKeys)) a
        f (grammar, collapseFn, successFn) b = case matchAndCollapse' grammar collapseFn x of
                                                    MatchFailure s -> Left s
                                                    MatchSuccess (_, s) -> successFn s
                                                    --MatchSuccess _ -> Left "wrong grammar"
                                                    NoMatch _ -> b

pythonMatchPattern (String s) = Right $ MatchString s
pythonMatchPattern (Number s) = Right $ MatchNumber s
pythonMatchPattern (Bool s) = Right $ MatchBool s
pythonMatchPattern Null = Right $ MatchNull
-}
