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
  [f, n, r, a] <- traverse newName ["f", "n", "r", "a"]
  let mkGuarded n' = (PatG [BindS (LitP (IntegerL n')) (VarE n)], AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT (VarT (paramNames !! fromIntegral n')) (VarT a))))
  pure
    [ FunD apply
      [ Clause
        [ WildP, VarP f, ConP union [ VarP n, VarP r ] ]
        (GuardedB (mkGuarded <$> [0..pred (fromIntegral (length paramNames))]))
        []
      ]
    ]
  where apply = mkName "apply"


mkApply2Function :: [Name] -> Q [Dec]
mkApply2Function paramNames  = do
  [f, n1, n2, r1, r2, a] <- traverse newName ["f", "n1", "n2", "r1", "r2", "a"]
  let mkGuarded n = (PatG [BindS (LitP (IntegerL n)) (VarE n1), BindS (LitP (IntegerL n)) (VarE n2)], (AppE (ConE 'Just) (AppE (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r1)) (AppT (VarT (paramNames !! fromIntegral n)) (VarT a)))) (AppE (VarE 'unsafeCoerce) (VarE r2)))))
  pure
    [ FunD apply2
      [ Clause
        [ WildP, VarP f, ConP union [ VarP n1, VarP r1 ], ConP union [ VarP n2, VarP r2 ] ]
        (GuardedB ((mkGuarded <$> [0..pred (fromIntegral (length paramNames))]) ++ [ (NormalG (VarE 'otherwise), ConE 'Nothing) ]))
        []
      ]
    ]
  where apply2 = mkName "apply2"

union :: Name
union = mkName "Union"
