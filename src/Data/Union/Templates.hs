{-# LANGUAGE TemplateHaskell #-}
module Data.Union.Templates
( mkElemInstances
, mkApplyInstance
) where

import Language.Haskell.TH
import Unsafe.Coerce (unsafeCoerce)

mkElemInstances :: Integer -> [Dec]
mkElemInstances paramN = mkInstance <$> [0..pred paramN]
  where mkInstance t = InstanceD Nothing [] (InfixT (mkT t) elemC (typeListT typeParams))
          [ FunD elemNo [ Clause [] (NormalB (AppE (ConE p) (LitE (IntegerL t)))) [] ] ]
        mkT = VarT . mkName . ('f' :) . show
        typeParams = mkT <$> [0..pred paramN]
        [elemC, elemNo, p] = mkName <$> [":<", "elemNo", "P"]

mkApplyInstance :: Integer -> Dec
mkApplyInstance paramN =
  InstanceD Nothing (AppT constraint <$> typeParams) (AppT (AppT (ConT applyC) constraint) (typeListT typeParams))
    [ FunD apply (zipWith mkClause [0..] typeParams) ]
  where typeParams = VarT . mkName . ('f' :) . show <$> [0..pred paramN]
        [applyC, apply, f, r, union] = mkName <$> ["Apply", "apply", "f", "r", "Union"]
        [constraint, a] = VarT . mkName <$> ["constraint", "a"]
        mkClause i nthType = Clause
          [ WildP, VarP f, ConP union [ LitP (IntegerL i), VarP r ] ]
          (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT nthType a))))
          []

typeListT :: [Type] -> Type
typeListT = foldr (AppT . AppT PromotedConsT) PromotedNilT
