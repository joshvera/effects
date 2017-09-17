{-# LANGUAGE TemplateHaskell #-}
module Data.Union.Templates
( mkApplyInstance
) where

import Language.Haskell.TH
import Unsafe.Coerce (unsafeCoerce)


mkApplyInstance :: Integer -> Dec
mkApplyInstance paramN =
  InstanceD Nothing (AppT (VarT constraint) <$> typeParams) (AppT (AppT (ConT apply) (VarT constraint)) (foldr (AppT . AppT PromotedConsT) PromotedNilT typeParams))
    [mkApplyFunction typeParams, mkApply2Function typeParams]
  where (apply, constraint) = (mkName "Apply", mkName "constraint")
        typeParams = VarT . mkName . ('f' :) . show <$> [0..pred paramN]

mkApplyFunction :: [Type] -> Dec
mkApplyFunction typeParams =
  FunD apply
    [ Clause
      [ WildP, VarP f, ConP union [ VarP n, VarP r ] ]
      (NormalB (CaseE (VarE n) (zipWith mkMatch [0..] typeParams ++ [ Match WildP (NormalB (AppE (VarE 'error) (InfixE (Just (LitE (StringL "index "))) (VarE '(++)) (Just (InfixE (Just (AppE (VarE 'show) (VarE n))) (VarE '(++)) (Just (LitE (StringL (" out of union bounds (" ++ show (length typeParams) ++ ")"))))))))) [] ])))
      []
    ]
  where mkMatch i nthType = Match (LitP (IntegerL i)) (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT nthType (VarT a))))) []
        [apply, f, n, r, a] = mkName <$> ["apply", "f", "n", "r", "a"]


mkApply2Function :: [Type] -> Dec
mkApply2Function typeParams =
  FunD apply2
    [ Clause
      [ WildP, VarP f, ConP union [ VarP n1, VarP r1 ], ConP union [ VarP n2, VarP r2 ] ]
      (NormalB (CaseE (TupE [ VarE n1, VarE n2 ]) ((zipWith mkMatch [0..] typeParams) ++ [ Match WildP (NormalB (ConE 'Nothing)) [] ])))
      []
    ]
  where mkMatch i nthType = Match (TupP [LitP (IntegerL i), LitP (IntegerL i)]) (NormalB (AppE (ConE 'Just) (AppE (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r1)) (AppT nthType (VarT a)))) (AppE (VarE 'unsafeCoerce) (VarE r2))))) []
        [apply2, f, n1, n2, r1, r2, a] = mkName <$> ["apply2", "f", "n1", "n2", "r1", "r2", "a"]

union :: Name
union = mkName "Union"
