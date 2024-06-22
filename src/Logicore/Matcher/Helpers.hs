{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Logicore.Matcher.Helpers where

import Data.Aeson

import Data.List                  as L
import Data.Text                  as T
import Data.Text.Lazy             as TL
import Data.Text.Lazy.Encoding    as TL

import Data.Aeson.KeyMap          as KM

import Prelude                    as P

import Language.Haskell.TH
import Language.Haskell.TH.Datatype as TH.Abs
import Language.Haskell.TH.Datatype.TyVarBndr
import Language.Haskell.TH.Syntax

import Data.Functor.Foldable
import Data.Functor.Foldable.TH (makeBaseFunctor)

import Data.Aeson.Key             as K
import qualified Data.Vector as V


makeBaseFunctor ''Type

constrs = cata go
  where
    go :: TypeF Value -> Value
    go (VarTF a) = Object $ KM.fromList [(K.fromString "type", s "VarT"), (K.fromString "value", s $ showName a)]
    go (ConTF a) = Object $ KM.fromList [(K.fromString "type", s "ConT"), (K.fromString "value", s $ nameBase $ a)]
    go (AppTF a b) = Object $ KM.fromList [(K.fromString "type", s "AppT"), (K.fromString "target", a), (K.fromString "param", b)]
    go (ForallTF _ _ _) = error "ForallTF"
    go (ForallVisTF _ _) = error "ForallVisTF"
    go (AppKindTF _ _) = error "AppKindTF"
    go (SigTF _ _) = error "SigTF"
    go (PromotedTF _) = error "PromotedTF"
    go (InfixTF _ _ _) = error "InfixTF"
    go (UInfixTF _ _ _) = error "UInfixTF"
    go (ParensTF _) = error "ParensTF"
    go (TupleTF _) = Null --error "TupleTF"
    go (UnboxedTupleTF _) = error "UnboxedTupleTF"
    go (UnboxedSumTF _) = error "UnboxedSumTF"
    go (ArrowTF) = error "ArrowT"
    go (MulArrowTF) = error "MulArrowT"
    go (EqualityTF) = error "EqualityT"
    go (ListTF) = Object $ KM.fromList [(K.fromString "type", s "ListT")]
    go (PromotedTupleTF _) = error "PromotedTupleTF"
    go (PromotedNilTF) = error "PromotedNilT"
    go (PromotedConsTF) = error "PromotedConsT"
    go (StarTF) = error "StarT"
    go (ConstraintTF) = error "ConstraintT"
    go (LitTF _) = error "LitTF"
    go (WildCardTF) = error "WildCardT"
    go (ImplicitParamTF _ _) = error "ImplicitParamTF"

s = (String . T.pack)
arr = (Array . V.fromList)

--J t = (String . T.pack . nameBase . datatypeName) t
ddd1 :: [Name] -> Q Value
ddd1 ds = fmap (Array . V.fromList) $ L.foldl f mempty ds
  where f acc' e = do
          e <- reifyDatatype e
          acc <- acc'
          let vrs x = s $ showName $ case x of
                           PlainTV n _ -> n
                           KindedTV n _ _ -> n
          let ff x = Object $ KM.fromList [
                (K.fromString "tag", s $ nameBase $ constructorName $ x),
                (K.fromString "contents", Array $ V.fromList $ fmap constrs (constructorFields x))
                ]
          let d = Array $ V.fromList $ fmap ff (datatypeCons e)
          return $ acc <> [
            Object $ KM.fromList [(K.fromString "value", ((s . nameBase . datatypeName) e)),
            (K.fromString "vars", arr $ fmap vrs $ datatypeVars e),
            (K.fromString "contents", d)
            ]]

ddd xs = ((stringE . TL.unpack . TL.decodeUtf8 . encode) =<< (ddd1 xs))
