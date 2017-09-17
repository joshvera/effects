{-# LANGUAGE TemplateHaskell #-}
module Data.Union.Templates
( mkApplyInstance
) where

import Language.Haskell.TH
import Unsafe.Coerce (unsafeCoerce)

mkApplyInstance :: Integer -> Dec
mkApplyInstance paramN =
  InstanceD Nothing (AppT constraint <$> typeParams) (AppT (AppT (ConT applyC) constraint) (foldr (AppT . AppT PromotedConsT) PromotedNilT typeParams))
    [ FunD apply (zipWith mkClause [0..] typeParams) ]
  where typeParams = VarT . mkName . ('f' :) . show <$> [0..pred paramN]
        [applyC, apply, f, r] = mkName <$> ["Apply", "apply", "f", "r"]
        [constraint, a] = VarT . mkName <$> ["constraint", "a"]
        mkClause i nthType = Clause
          [ WildP, VarP f, ConP union [ LitP (IntegerL i), VarP r ] ]
          (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT nthType a))))
          []

union :: Name
union = mkName "Union"
