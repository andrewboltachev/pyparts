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

main = cata embed $ T1 True $ T1 False $ T2
