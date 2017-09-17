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
  typeParams <- map VarT <$> replicateM (fromIntegral paramN) (newName "f")
  applyD <- mkApplyFunction typeParams
  apply2D <- mkApply2Function typeParams
  pure
    [ InstanceD Nothing (AppT (VarT c) <$> typeParams) (AppT (AppT (ConT apply) (VarT c)) (foldr (AppT . AppT PromotedConsT) PromotedNilT typeParams))
      (applyD ++ apply2D)
    ]
  where apply = mkName "Apply"

mkApplyFunction :: [Type] -> Q [Dec]
mkApplyFunction typeParams = do
  pure
    [ FunD apply
      [ Clause
        [ WildP, VarP f, ConP union [ VarP n, VarP r ] ]
        (NormalB (CaseE (VarE n) (zipWith mkMatch [0..] typeParams)))
        []
      ]
    ]
  where mkMatch i nthType = Match (LitP (IntegerL i)) (NormalB (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r)) (AppT nthType (VarT a))))) []
        [apply, f, n, r, a] = mkName <$> ["apply", "f", "n", "r", "a"]


mkApply2Function :: [Type] -> Q [Dec]
mkApply2Function typeParams  = do
  let mkMatch n = Match (TupP [LitP (IntegerL n), LitP (IntegerL n)]) (NormalB (AppE (ConE 'Just) (AppE (AppE (VarE f) (SigE (AppE (VarE 'unsafeCoerce) (VarE r1)) (AppT (typeParams !! fromIntegral n) (VarT a)))) (AppE (VarE 'unsafeCoerce) (VarE r2))))) []
  pure
    [ FunD apply2
      [ Clause
        [ WildP, VarP f, ConP union [ VarP n1, VarP r1 ], ConP union [ VarP n2, VarP r2 ] ]
        (NormalB (CaseE (TupE [ VarE n1, VarE n2 ]) ((mkMatch <$> [0..pred (fromIntegral (length typeParams))]) ++ [ Match WildP (NormalB (ConE 'Nothing)) [] ])))
        []
      ]
    ]
  where [apply2, f, n1, n2, r1, r2, a] = mkName <$> ["apply2", "f", "n1", "n2", "r1", "r2", "a"]

union :: Name
union = mkName "Union"
