{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}


module Logicore.Matcher.RS where

import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Functor.Foldable

data T1 = A1 Bool T1 | A2 deriving (Eq, Show)

makeBaseFunctor ''T1

--main = cata embed $ A1F True $ A1F False $ A2F

{-
this doesn't compile giving:

/home/andrey/Learn/matcher/src/Logicore/Matcher/RS.hs:20:13: error:
    • Couldn't match type ‘Base a0’ with ‘T1F’
      Expected: Base T1 a0 -> a0
        Actual: Base a0 a0 -> a0
      The type variable ‘a0’ is ambiguous
    • In the first argument of ‘cata’, namely ‘embed’
      In the first argument of ‘($)’, namely ‘cata embed’
      In the expression: cata embed $ A1 True $ A1 False $ A2
    • Relevant bindings include
        main :: a0
          (bound at /home/andrey/Learn/matcher/src/Logicore/Matcher/RS.hs:20:1)
   |
20 | main = cata embed $ A1 True $ A1 False $ A2
   |             ^^^^^


-}
