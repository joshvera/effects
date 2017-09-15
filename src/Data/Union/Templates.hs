{-# LANGUAGE TemplateHaskell #-}
module Data.Union.Templates
( mkApply0Instance
, mkApply0Instances
, mkApply1Instance
, mkApply1Instances
) where

import Control.Monad
import Language.Haskell.TH
import Unsafe.Coerce (unsafeCoerce)

mkApply0Instances :: [Int] -> Q [Dec]
mkApply0Instances = fmap concat . traverse mkApply0Instance

mkApply0Instance :: Int -> Q [Dec]
mkApply0Instance paramN = do
  c <- newName "c"
  a <- newName "a"
  params <- replicateM paramN (newName "f")
  apply0D <- mkApply0Function params
  apply0_2D <- mkApply0_2Function params
  pure
    [ InstanceD Nothing (AppT (VarT c) . flip AppT (VarT a) . VarT <$> params) (AppT (AppT (AppT (ConT apply0) (VarT c)) (foldr (AppT . AppT PromotedConsT . VarT) PromotedNilT params)) (VarT a))
      (apply0D ++ apply0_2D)
    ]
  where apply0 = mkName "Apply0"

mkApply0Function :: [Name] -> Q [Dec]
mkApply0Function paramNames = do
  clauses <- traverse (mkApply0Clause paramNames) [0..pred (fromIntegral (length paramNames))]
  pure [ FunD apply0 (concat clauses) ]
  where apply0 = mkName "apply0"

mkApply0Clause :: [Name] -> Integer -> Q [Clause]
mkApply0Clause paramNames n = do
  [f, r, a] <- traverse newName ["f", "r", "a"]
  pure
    [ Clause
      [ WildP, VarP f, ConP union [ LitP (IntegerL n), VarP r ] ]
      (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))))
      []
    ]

mkApply0_2Function :: [Name] -> Q [Dec]
mkApply0_2Function paramNames  = do
  clauses <- traverse (mkApply0_2Clause paramNames) [0..pred (fromIntegral (length paramNames))]
  pure [ FunD apply0_2 (concat clauses ++ [ Clause [ WildP, WildP, WildP, WildP ] (NormalB (ConE 'Nothing)) [] ]) ]
  where apply0_2 = mkName "apply0_2"

mkApply0_2Clause :: [Name] -> Integer -> Q [Clause]
mkApply0_2Clause paramNames n = do
  [f, r1, r2, a] <- traverse newName ["f", "r1", "r2", "a"]
  pure
    [ Clause
      [ WildP, VarP f, ConP union [ LitP (IntegerL n), VarP r1 ], ConP union [ LitP (IntegerL n), VarP r2 ] ]
      (NormalB (AppE (ConE 'Just) (AppE (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r1)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))) (AppE (VarE 'unsafeCoerce) (VarE r2)))))
      []
    ]


mkApply1Instances :: [Integer] -> Q [Dec]
mkApply1Instances = fmap concat . traverse mkApply1Instance

mkApply1Instance :: Integer -> Q [Dec]
mkApply1Instance paramN = do
  c <- newName "c"
  params <- replicateM (fromIntegral paramN) (newName "f")
  apply1D <- mkApply1Function params
  apply1_2D <- mkApply1_2Function params
  pure
    [ InstanceD Nothing (AppT (VarT c) . VarT <$> params) (AppT (AppT (ConT apply1) (VarT c)) (foldr (AppT . AppT PromotedConsT . VarT) PromotedNilT params))
      (apply1D ++ apply1_2D)
    ]
  where apply1 = mkName "Apply1"

mkApply1Function :: [Name] -> Q [Dec]
mkApply1Function paramNames = do
  clauses <- traverse (mkApply1Clause paramNames) [0..pred (fromIntegral (length paramNames))]
  pure [ FunD apply1 (concat clauses) ]
  where apply1 = mkName "apply1"

mkApply1Clause :: [Name] -> Integer -> Q [Clause]
mkApply1Clause paramNames n = do
  [f, r, a] <- traverse newName ["f", "r", "a"]
  pure
    [ Clause
      [ WildP, VarP f, ConP union [ LitP (IntegerL n), VarP r ] ]
      (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))))
      []
    ]

mkApply1_2Function :: [Name] -> Q [Dec]
mkApply1_2Function paramNames  = do
  clauses <- traverse (mkApply1_2Clause paramNames) [0..pred (fromIntegral (length paramNames))]
  pure [ FunD apply1_2 (concat clauses ++ [ Clause [ WildP, WildP, WildP, WildP ] (NormalB (ConE 'Nothing)) [] ]) ]
  where apply1_2 = mkName "apply1_2"

mkApply1_2Clause :: [Name] -> Integer -> Q [Clause]
mkApply1_2Clause paramNames n = do
  [f, r1, r2, a] <- traverse newName ["f", "r1", "r2", "a"]
  pure
    [ Clause
      [ WildP, VarP f, ConP union [ LitP (IntegerL n), VarP r1 ], ConP union [ LitP (IntegerL n), VarP r2 ] ]
      (NormalB (AppE (ConE 'Just) (AppE (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r1)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))) (AppE (VarE 'unsafeCoerce) (VarE r2)))))
      []
    ]

union :: Name
union = mkName "Union"
