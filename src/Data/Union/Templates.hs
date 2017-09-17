{-# LANGUAGE TemplateHaskell #-}
module Data.Union.Templates
( mkApplyInstance
) where

import Language.Haskell.TH
import Unsafe.Coerce (unsafeCoerce)

mkApplyInstance :: Integer -> Dec
mkApplyInstance paramN =
  InstanceD Nothing (AppT (VarT constraint) <$> typeParams) (AppT (AppT (ConT applyC) (VarT constraint)) (foldr (AppT . AppT PromotedConsT) PromotedNilT typeParams))
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
        [applyC, constraint, apply, f, n, r, a] = mkName <$> ["Apply", "constraint", "apply", "f", "n", "r", "a"]
        mkMatch i nthType = Match (LitP (IntegerL i)) (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT nthType (VarT a))))) []

union :: Name
union = mkName "Union"
