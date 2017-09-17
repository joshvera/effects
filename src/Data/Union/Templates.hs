{-# LANGUAGE TemplateHaskell #-}
module Data.Union.Templates
( mkApplyInstance
) where

import Language.Haskell.TH
import Unsafe.Coerce (unsafeCoerce)

mkApplyInstance :: Integer -> Dec
mkApplyInstance paramN =
  InstanceD Nothing (AppT constraint <$> typeParams) (AppT (AppT (ConT applyC) constraint) (foldr (AppT . AppT PromotedConsT) PromotedNilT typeParams))
    [ FunD apply
      [ Clause
        [ WildP, VarP f, ConP union [ VarP n, VarP r ] ]
        (NormalB (CaseE (VarE n)
          (  zipWith mkMatch [0..] typeParams
          ++ [ Match WildP (NormalB (AppE (VarE 'error)
            (InfixE (Just (LitE (StringL "index ")))
            (VarE '(++)) (Just (InfixE (Just (AppE (VarE 'show) (VarE n)))
            (VarE '(++)) (Just (LitE (StringL (" out of union bounds (" ++ show (length typeParams) ++ ")"))))))))) [] ])))
        []
      ]
    ]
  where typeParams = VarT . mkName . ('f' :) . show <$> [0..pred paramN]
        [applyC, apply, f, n, r] = mkName <$> ["Apply", "apply", "f", "n", "r"]
        [constraint, a] = VarT . mkName <$> ["constraint", "a"]
        mkMatch i nthType = Match (LitP (IntegerL i)) (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT nthType a)))) []

union :: Name
union = mkName "Union"
