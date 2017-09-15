{-# LANGUAGE TemplateHaskell #-}
module Data.Union.Templates
( mkApplyInstance
, mkApplyInstances
) where

import Control.Monad
import Language.Haskell.TH
import Unsafe.Coerce (unsafeCoerce)

mkApplyInstances :: [Integer] -> Q [Dec]
mkApplyInstances = fmap concat . traverse mkApplyInstance

mkApplyInstance :: Integer -> Q [Dec]
mkApplyInstance paramN = do
  c <- newName "c"
  params <- replicateM (fromIntegral paramN) (newName "f")
  applyD <- mkApplyFunction params
  apply2D <- mkApply2Function params
  pure
    [ InstanceD Nothing (AppT (VarT c) . VarT <$> params) (AppT (AppT (ConT apply) (VarT c)) (foldr (AppT . AppT PromotedConsT . VarT) PromotedNilT params))
      (applyD ++ apply2D)
    ]
  where apply = mkName "Apply"

mkApplyFunction :: [Name] -> Q [Dec]
mkApplyFunction paramNames = do
  clauses <- traverse (mkApplyClause paramNames) [0..pred (fromIntegral (length paramNames))]
  pure [ FunD apply (concat clauses) ]
  where apply = mkName "apply"

mkApplyClause :: [Name] -> Integer -> Q [Clause]
mkApplyClause paramNames n = do
  [f, r, a] <- traverse newName ["f", "r", "a"]
  pure
    [ Clause
      [ WildP, VarP f, ConP union [ LitP (IntegerL n), VarP r ] ]
      (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))))
      []
    ]

mkApply2Function :: [Name] -> Q [Dec]
mkApply2Function paramNames  = do
  clauses <- traverse (mkApply2Clause paramNames) [0..pred (fromIntegral (length paramNames))]
  pure [ FunD apply2 (concat clauses ++ [ Clause [ WildP, WildP, WildP, WildP ] (NormalB (ConE 'Nothing)) [] ]) ]
  where apply2 = mkName "apply2"

mkApply2Clause :: [Name] -> Integer -> Q [Clause]
mkApply2Clause paramNames n = do
  [f, r1, r2, a] <- traverse newName ["f", "r1", "r2", "a"]
  pure
    [ Clause
      [ WildP, VarP f, ConP union [ LitP (IntegerL n), VarP r1 ], ConP union [ LitP (IntegerL n), VarP r2 ] ]
      (NormalB (AppE (ConE 'Just) (AppE (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r1)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))) (AppE (VarE 'unsafeCoerce) (VarE r2)))))
      []
    ]

union :: Name
union = mkName "Union"
