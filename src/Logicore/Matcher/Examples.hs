{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Logicore.Matcher.Examples where

import Prelude                    as P
import Data.Aeson
import Data.Text                  as T
import Data.Text.Encoding         as T
import Data.Text.IO               as T
import Data.Text.Lazy             as TL
import Data.Text.Lazy.Encoding    as TL
import Data.Text.Lazy.IO          as TL
import Data.Aeson.KeyMap          as KM
import Data.Aeson.Key             as K
import qualified Data.List        as L
import qualified Data.Vector as V
import Data.ByteString.Lazy       as BL
import qualified Data.Set

import Logicore.Matcher.Core
import Logicore.Matcher.Additional
import Logicore.Matcher.Examples.Utils
import Logicore.Matcher.Experimental

{-

getData1 :: IO (Maybe Value)
getData1 = do
  fileData <- BL.readFile "/home/andrey/Work/lc/matcher1.json"
  return $ decode fileData

getData :: IO (Maybe Value)
getData = do
  fileData <- BL.readFile "/home/andrey/Work/lc/matcher.json"
  return $ decode fileData

main_grammar = MatchObjectPartial (fromList [
    (fromString "type", MatchString $ T.pack "ClassDef"),
    (fromString "body", (MatchObjectPartial
                      (fromList [
                        --(fromString "type", MatchString $ T.pack "IndentedBlock"),
                        (fromString "type", MatchString $ T.pack "IndentedBlock"),
                        (fromString "body",
                         MatchArraySome (MatchObjectPartial (fromList [
                          (fromString "type", MatchString $ T.pack "SimpleStatementLine"),
                          (fromString "body",
                            (MatchIfThen
                              (MatchArraySome (MatchObjectPartial (fromList [
                                  (fromString "type", MatchString $ T.pack "AnnAssign")
                              
                                  --(fromString "target", (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name"),
                                  --                                                    (fromString "value", MatchLiteral)])))
                              
                              ])))
                              (MatchArraySome (MatchObjectPartial (fromList [
                                  (fromString "type", MatchString $ T.pack "AnnAssign") ,
                                  (fromString "target", (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name"),
                                                                                      (fromString "value", MatchLiteral)]))),
                                  (fromString "annotation",
                                   (MatchIfThen
                                    (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Annotation")]))
                                    (MatchObjectPartial (fromList [(fromString "annotation",
                                                                  (MatchSimpleOr
                                                                  [
                                                                    (MatchIfThen
                                                                      (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Subscript")]))
                                                                      {-(MatchObjectPartial (fromList [
                                                                                                      (fromString "type", MatchString $ T.pack "Subscript")
                                                                                                      , (fromString "value",
                                                                                                        (MatchObjectPartial (fromList [
                                                                                                          (fromString "type", MatchString $ T.pack "Name")
                                                                                                        , (fromString "value", MatchLiteral)
                                                                                                        ]))
                                                                                                      )
                                                                                                      --,(fromString "slice", MatchAny)
                                                                                                      ]))-}
                                                                      -- ["lbracket","lpar","rbracket","rpar","slice","type","value","whitespace_after_value"]
                                                                      -- lbracket, rbracket - only has whitespace
                                                                      (MatchObjectPartial (fromList [
                                                                        (fromString "value", (MatchObjectPartial (fromList [(fromString "value", MatchLiteral)]))),
                                                                        (fromString "slice",
                                                                          -- ["comma","slice","type" = SubscriptElement]
                                                                          -- comma:
                                                                          --    {"type":"Comma","whitespace_after":{"type":"SimpleWhitespace","value":" "},"whitespace_before":{"type":"SimpleWhitespace","value":""}}
                                                                          --    "MaybeSentinel.DEFAULT"
                                                                         MatchArray $ MatchObjectPartial (fromList [(fromString "slice",
                                                                          -- ["star"=null,"type"="Index","value","whitespace_after_star"=null]
                                                                          MatchObjectPartial (fromList [
                                                                            -- ...
                                                                            --(fromString "type", MatchString $ T.pack "Index"),
                                                                            -- ["lbracket","lpar","rbracket","rpar","slice","type","value","whitespace_after_value"]
                                                                            -- ["lpar","rpar","type","value"]

                                                                            (fromString "value",
                                                                             (MatchSimpleOr
                                                                             [
                                                                              (MatchIfThen
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "SimpleString")]))
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchLiteral), (fromString "value", MatchLiteral)]))
                                                                                "foo..."
                                                                              ),
                                                                              (MatchIfThen
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name")]))
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchLiteral), (fromString "value", MatchLiteral)]))
                                                                                "foo..."
                                                                              ),
                                                                              (MatchIfThen
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Subscript")]))



                                                                          (MatchObjectPartial (fromList [
                                                                            -- ...
                                                                            --(fromString "type", MatchString $ T.pack "Index"),
                                                                            -- ["lbracket","lpar","rbracket","rpar","slice","type","value","whitespace_after_value"]
                                                                            -- ["lpar","rpar","type","value"]

                                                                            (fromString "type", MatchLiteral),
                                                                            (fromString "value",
                                                                             (MatchSimpleOr
                                                                             [
                                                                               -- only Name here on 2nd level
                                                                              (MatchIfThen
                                                                                (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name")]))
                                                                                (MatchObjectPartial (fromList [(fromString "value", MatchLiteral)]))
                                                                                "foo..."
                                                                              )
                                                                              --(MatchObjectPartial (fromList [(fromString "type", MatchFunnel)]))
                                                                             ])
                                                                            
                                                                            )
                                                                          ]))




                                                                                "foo..."
                                                                              )


                                                                             ])
                                                                            
                                                                            )
                                                                          ])
                                                                         )]))
                                                                      ]))
                                                                      --(MatchObjectPartial (fromList [(fromString "value", MatchFunnel)]))

                                                                    "foo1"),
                                                                    (MatchIfThen
                                                                      (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name")]))
                                                                      (MatchObjectPartial (fromList [
                                                                                                    (fromString "type", MatchString $ T.pack "Name"),
                                                                                                    (fromString "value", MatchLiteral)
                                                                                                    ]))
                                                                    "foo2")
                                                                  ])
                                                                  )]))) "iii")
                                ])))
                            "annotation match fail"))

                            --(fromString "annotation", )
                        ]))
                        
                        
                        )
                      ])))
            ])

-- helpers begin

h3 :: [Value] -> [String]
h3 v = catMaybes $ fmap f v
  where f x = do
                x <- asKeyMap x
                x <- KM.lookup (fromString "body") x
                x <- asArray x
                x <- safeHead x
                x <- asKeyMap x
                k <- KM.lookup (fromString "target") x
                k <- asKeyMap k
                k <- KM.lookup (fromString "value") k
                k <- asString k
                -- ...
                v <- KM.lookup (fromString "annotation") x
                return $ T.unpack k ++ "\t\t\t" ++ (TL.unpack . TL.decodeUtf8 $ encode v)


h1 :: Value -> Maybe [Value]
h1 x = do
                x <- asKeyMap x
                x <- KM.lookup (fromString "body") x
                x <- asKeyMap x
                x <- KM.lookup (fromString "body") x
                x <- asArray x
                --k <- KM.lookup (fromString "target") x
                --k <- asKeyMap k
                --k <- KM.lookup (fromString "value") k
                --k <- asString k
                -- ...
                --v <- KM.lookup (fromString "annotation") x
                --return $ (fromText k, v)
                return x

asJust (Just x) = x

h2 (MatchSuccess s) = P.concat $ (fmap (\x -> x ++ "\n")) $ h3 $ asJust (h1 s)
h2 x = show x

catSuccesses xs = L.foldl' f mempty xs
  where f a b = case b of
                     MatchSuccess x -> a ++ [x]
                     _ -> a

-- helpers end


p1 :: IO (Maybe Value) -> IO ()
p1 theData = do
  -- d :: Maybe Value
  d <- theData
  let v = do
        -- d' :: Value
        d' <- d
        -- d'' :: Keymap Value
        d'' <- asKeyMap d'
        let f v = do
              r' <- matchPattern main_grammar v
              -- r' :: MatchResult MatchPattern
              r <- return $ resetUnsignificant r'
              -- r' :: MatchResult MatchPattern
              r <- matchToValueMinimal' r
              return (gatherFunnel [] r', r)
        --let j (k, (_, v)) = (K.toString k) ++ "\n" ++ "\n" ++ "\n" ++ v ++ "\n\n"
        let j (k, v) = (K.toString k) ++ "\n" ++ h2 v ++ "\n" ++ "\n"
        let s1 = (fmap . fmap) f (KM.toList d'')
        let s2 = (fmap . fmap . fmap) snd s1
        let s3 = P.concat $ L.intersperse "\n" $ fmap (TL.unpack . TL.decodeUtf8 . encode) $ (Data.Set.toList) $ (Data.Set.fromList) $ P.concat $ fmap fst $ catSuccesses $ fmap snd s1
        return $ (P.concat $ fmap j s2) ++ "\n\n" ++ s3
  P.putStrLn $ case v of
       Nothing -> "Nothing to see"
       Just a -> a

hh a = P.concat $ fmap f a
  where f x = (TL.unpack . TL.decodeUtf8 . encode) x ++ "\n"


grammar'1 = MatchIfThen (MatchObjectPartial (fromList [
    (fromString "body", MatchFunnelKeys)
  ])) (MatchObjectPartial (fromList [(fromString "orelse", MatchNull)])) "orelse fail"



matchFile a grammar collapse = do
  -- d :: Maybe Value
  d <- getD a
  let v = do
        -- d' :: Value
        d' <- d
        let f v = do
              r' <- matchPattern grammar v
              -- r' :: MatchResult MatchPattern
              r <- return $ resetUnsignificant r'
              -- r' :: MatchResult MatchPattern
              r <- matchToValueMinimal' r
              r <- collapse r
              return $ "Result\n\n" ++ (TL.unpack . TL.decodeUtf8 . encode) r ++ "\n\n\n" ++ "Funnel\n\n" ++ hh (gatherFunnel [] r')
              --return $ (r, gatherFunnel [] r')
        return $ f d'
  P.putStrLn $ case v of
       Nothing -> "Nothing to see"
       Just a -> case a of
                      NoMatch x -> "NoMatch " ++ x
                      MatchFailure s -> "MatchFailure " ++ s
                      MatchSuccess s -> "Success!!!\n\n\n" ++ s



so_grammar = MatchObjectPartial (fromList [("items", MatchArray $ MatchObjectPartial (fromList [("tags", MatchFunnel)]))])
so_collapse x = return x
-}
