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
  [c, f, a, n1, n2, r1, r2, u1, u2, proxy] <- traverse newName ["c", "f", "a", "n1", "n2", "r1", "r2", "u1", "u2", "proxy"]
  params <- replicateM paramN (newName "f")
  apply0'D <- mkApply0'Function params
  pure
    [ InstanceD Nothing (AppT (VarT c) . flip AppT (VarT a) . VarT <$> params) (AppT (AppT (AppT (ConT apply0) (VarT c)) (foldr (AppT . AppT PromotedConsT . VarT) PromotedNilT params)) (VarT a))
      ( apply0'D ++
      [ FunD apply0_2'
        [ Clause
          [ WildP, VarP f, ConP union [ LitP (IntegerL 0), VarP r1 ], ConP union [ LitP (IntegerL 0), VarP r2 ] ]
          (NormalB (AppE (ConE 'Just) (AppE (AppE (AppE (VarE f) (AppE (ConE union) (LitE (IntegerL 0)))) (SigE (AppE (VarE 'unsafeCoerce) (VarE r1)) (AppT (VarT (head params)) (VarT a)))) (AppE (VarE 'unsafeCoerce) (VarE r2)))))
          []
        , Clause
          [ VarP proxy, VarP f, AsP u1 (ConP union [ VarP n1, VarP r1 ]), AsP u2 (ConP union [ VarP n2, VarP r2 ]) ]
          (GuardedB
            [ (NormalG (AppE (AppE (VarE '(==)) (VarE n1)) (VarE n2)), (AppE (AppE (AppE (AppE (VarE apply0_2') (VarE proxy)) (LamE [WildP] (AppE (VarE f) (AppE (ConE union) (VarE n1))))) (AppE (AppE (VarE asStrongerUnionTypeOf) (AppE (AppE (ConE union) (AppE (VarE 'pred) (VarE n1))) (VarE r1))) (VarE u1))) (AppE (AppE (VarE asStrongerUnionTypeOf) (AppE (AppE (ConE union) (AppE (VarE 'pred) (VarE n2))) (VarE r2))) (VarE u2))))
            , (NormalG (VarE 'otherwise), ConE 'Nothing)
            ])
          []
        ]
      ])
    ]
  where apply0 = mkName "Apply0"
        apply0_2' = mkName "apply0_2'"

mkApply0'Function :: [Name] -> Q [Dec]
mkApply0'Function paramNames = do
  clauses <- traverse (mkApply0'Clause paramNames) [0..pred (fromIntegral (length paramNames))]
  pure [ FunD apply0' (concat clauses) ]
  where apply0' = mkName "apply0'"

mkApply0'Clause :: [Name] -> Integer -> Q [Clause]
mkApply0'Clause paramNames n = do
  [f, r, a] <- traverse newName ["f", "r", "a"]
  pure
    [ Clause
      [ WildP, VarP f, ConP union [ LitP (IntegerL n), VarP r ] ]
      (NormalB (AppE (AppE (VarE f) (AppE (ConE union) (LitE (IntegerL n)))) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))))
      []
    ]


mkApply1Instances :: [Integer] -> Q [Dec]
mkApply1Instances = fmap concat . traverse mkApply1Instance

mkApply1Instance :: Integer -> Q [Dec]
mkApply1Instance paramN = do
  c <- newName "c"
  params <- replicateM (fromIntegral paramN) (newName "f")
  apply1'D <- mkApply1'Function params
  apply1_2'D <- mkApply1_2'Function params
  pure
    [ InstanceD Nothing (AppT (VarT c) . VarT <$> params) (AppT (AppT (ConT apply1) (VarT c)) (foldr (AppT . AppT PromotedConsT . VarT) PromotedNilT params))
      (apply1'D ++ apply1_2'D)
    ]
  where apply1 = mkName "Apply1"

mkApply1'Function :: [Name] -> Q [Dec]
mkApply1'Function paramNames = do
  clauses <- traverse (mkApply1'Clause paramNames) [0..pred (fromIntegral (length paramNames))]
  pure [ FunD apply1' (concat clauses) ]
  where apply1' = mkName "apply1'"

mkApply1'Clause :: [Name] -> Integer -> Q [Clause]
mkApply1'Clause paramNames n = do
  [f, r, a] <- traverse newName ["f", "r", "a"]
  pure
    [ Clause
      [ WildP, VarP f, ConP union [ LitP (IntegerL n), VarP r ] ]
      (NormalB (AppE (AppE (VarE f) (AppE (ConE union) (LitE (IntegerL n)))) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))))
      []
    ]

mkApply1_2'Function :: [Name] -> Q [Dec]
mkApply1_2'Function paramNames  = do
  clauses <- traverse (mkApply1_2'Clause paramNames) [0..pred (fromIntegral (length paramNames))]
  pure [ FunD apply1_2' (concat clauses) ]
  where apply1_2' = mkName "apply1_2'"

mkApply1_2'Clause :: [Name] -> Integer -> Q [Clause]
mkApply1_2'Clause paramNames n = do
  [f, r1, r2, a] <- traverse newName ["f", "r1", "r2", "a"]
  pure
    [ Clause
      [ WildP, VarP f, ConP union [ LitP (IntegerL n), VarP r1 ], ConP union [ LitP (IntegerL n), VarP r2 ] ]
      (NormalB (AppE (ConE 'Just) (AppE (AppE (AppE (VarE f) (AppE (ConE union) (LitE (IntegerL n)))) (SigE (AppE (VarE 'unsafeCoerce) (VarE r1)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))) (AppE (VarE 'unsafeCoerce) (VarE r2)))))
      []
    ]

union :: Name
union = mkName "Union"

asStrongerUnionTypeOf :: Name
asStrongerUnionTypeOf = mkName "asStrongerUnionTypeOf"
