{-# LANGUAGE TemplateHaskell #-}
module Data.Union.Templates
( mkElemIndexTypeFamily
) where

import Language.Haskell.TH
import Unsafe.Coerce (unsafeCoerce)

mkElemIndexTypeFamily :: Integer -> Dec
mkElemIndexTypeFamily paramN =
  ClosedTypeFamilyD (TypeFamilyHead elemIndex [KindedTV t functorK, KindedTV ts (AppT ListT functorK)] (KindSig (ConT nat)) Nothing) ((mkEquation <$> [0..pred paramN]) ++ errorCase)
  where [elemIndex, t, ts, nat] = mkName <$> ["ElemIndex", "t", "ts", "Nat"]
        functorK = AppT (AppT ArrowT StarT) StarT
        mkT = VarT . mkName . ('t' :) . show
        mkEquation i = TySynEqn [ mkT i, typeListT WildCardT (mkT <$> [0..i]) ] (LitT (NumTyLit i))
        typeErrN = mkName "TypeError"
        textN = mkName "Text"
        next = mkName ":<>:"
        above = mkName ":$$:"
        shw = mkName "ShowType"
        errorCase = [ TySynEqn
                      [ VarT t , VarT ts ]
                        (AppT
                         (ConT typeErrN)
                         (AppT
                          (AppT (PromotedT above)
                           (AppT (AppT (PromotedT next)
                                  (AppT (AppT
                                         (PromotedT next)
                                         (AppT (PromotedT textN) (LitT (StrTyLit "'"))))
                                               (AppT (PromotedT shw) (VarT t))))
                           (AppT (PromotedT textN) (LitT (StrTyLit "' is not a member of the type-level list")))))
                          (AppT (PromotedT shw) (VarT ts))))
                    ]


typeListT :: Type -> [Type] -> Type
typeListT = foldr (AppT . AppT PromotedConsT)
