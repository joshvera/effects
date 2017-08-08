{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}

-- Only for MemberU below, when emulating Monad Transformers
{-# LANGUAGE FunctionalDependencies, UndecidableInstances #-}

{-|
Module      : Data.Union
Description : Open unions (type-indexed co-products) for extensible effects.
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

All operations are constant-time, and there is no Typeable constraint

This is a variation of OpenUnion5.hs, which relies on overlapping
instances instead of closed type families. Closed type families
have their problems: overlapping instances can resolve even
for unground types, but closed type families are subject to a
strict apartness condition.

This implementation is very similar to OpenUnion1.hs, but without
the annoying Typeable constraint. We sort of emulate it:

Our list r of open union components is a small Universe.
Therefore, we can use the Typeable-like evidence in that
universe.

The data constructors of Union are not exported.
-}

module Data.Union (
  Union,
  decompose,
  weaken,
  inj,
  prj,
  type(:<),
  type(:<:),
  MemberU2,
  Apply0(..),
  apply1,
  apply1_2,
  Apply1(..)
) where

import Data.Functor.Classes (Eq1(..), Show1(..))
import Data.Maybe (fromMaybe)
import Data.Proxy
import Unsafe.Coerce(unsafeCoerce)
import GHC.Exts (Constraint)

infixr 5 :<

-- Strong Sum (Existential with the evidence) is an open union
-- t is can be a GADT and hence not necessarily a Functor.
-- Int is the index of t in the list r; that is, the index of t in the
-- universe r.
data Union (r :: [ k -> * ]) (v :: k) where
  Union :: {-# UNPACK #-} !Int -> t v -> Union r v

{-# INLINE prj' #-}
{-# INLINE inj' #-}
inj' :: Int -> t v -> Union r v
inj' = Union

prj' :: Int -> Union r v -> Maybe (t v)
prj' n (Union n' x) | n == n'   = Just (unsafeCoerce x)
                    | otherwise = Nothing

newtype P t r = P { unP :: Int }

infixr 5 :<:
-- | Find a list of members 'm' in an open union 'r'.
type family m :<: r :: Constraint where
  (t ': c) :<: r = (t :< r, c :<: r)
  '[] :<: r = ()

{-
-- Optimized specialized instance
instance (t :< '[t]) where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj x           = Union 0 x
  prj (Union _ x) = Just (unsafeCoerce x)
-}

-- | Inject a functor into a type-aligned union.
inj :: forall e r v. e :< r => e v -> Union r v
inj = inj' (unP (elemNo :: P e r))
{-# INLINE inj #-}

-- | Maybe project a functor out of a type-aligned union.
prj :: forall e r v. e :< r => Union r v -> Maybe (e v)
prj = prj' (unP (elemNo :: P e r))
{-# INLINE prj #-}


decompose :: Union (t ': r) v -> Either (Union r v) (t v)
decompose (Union 0 v) = Right $ unsafeCoerce v
decompose (Union n v) = Left  $ Union (n-1) v
{-# INLINE [2] decompose #-}


-- | Specialized version of 'decompose'.
decompose0 :: Union '[t] v -> Either (Union '[] v) (t v)
decompose0 (Union _ v) = Right $ unsafeCoerce v
-- No other case is possible
{-# RULES "decompose/singleton"  decompose = decompose0 #-}
{-# INLINE decompose0 #-}

weaken :: Union r w -> Union (any ': r) w
weaken (Union n v) = Union (n+1) v

asStrongerUnionTypeOf :: Union fs a -> Union (f ': fs) a -> Union fs a
asStrongerUnionTypeOf = const

-- Find an index of an element in an `r'.
-- The element must exist, so this is essentially a compile-time computation.
class (t :: * -> *) :< r where
  elemNo :: P t r

instance {-# OVERLAPPING #-} t :< (t ': r) where
  elemNo = P 0

instance {-# OVERLAPPING #-} t :< r => t :< (t' ': r) where
  elemNo = P $ 1 + unP (elemNo :: P t r)


-- | Helper to apply a function to a functor of the nth type in a type list.
class Apply0 (c :: * -> Constraint) (fs :: [k -> *]) (a :: k) where
  apply0' :: proxy c -> (forall g . c (g a) => (forall x. g x -> Union fs x) -> g a -> b) -> Union fs a -> b

  apply0_2' :: proxy c -> (forall g . c (g a) => (forall x. g x -> Union fs x) -> g a -> g b -> d) -> Union fs a -> Union fs b -> Maybe d

apply0 :: Apply0 c fs a => proxy c -> (forall g . c (g a) => g a -> b) -> Union fs a -> b
apply0 proxy f = apply0' proxy (const f)

apply0_2 :: Apply0 c fs a => proxy c -> (forall g . c (g a) => g a -> g b -> d) -> Union fs a -> Union fs b -> Maybe d
apply0_2 proxy f = apply0_2' proxy (const f)

instance (c (f0 a)) => Apply0 c '[f0] a where
  apply0' _ f (Union _ r) = f (Union 0) (unsafeCoerce r :: f0 a)

  apply0_2' _ f (Union _ r1) (Union _ r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))

instance (c (f0 a), c (f1 a)) => Apply0 c '[f0, f1] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a)) => Apply0 c '[f0, f1, f2] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a)) => Apply0 c '[f0, f1, f2, f3] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a)) => Apply0 c '[f0, f1, f2, f3, f4] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a), c (f42 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a), c (f42 a), c (f43 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a), c (f42 a), c (f43 a), c (f44 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a), c (f42 a), c (f43 a), c (f44 a), c (f45 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a), c (f42 a), c (f43 a), c (f44 a), c (f45 a), c (f46 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a), c (f42 a), c (f43 a), c (f44 a), c (f45 a), c (f46 a), c (f47 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a), c (f42 a), c (f43 a), c (f44 a), c (f45 a), c (f46 a), c (f47 a), c (f48 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a), c (f42 a), c (f43 a), c (f44 a), c (f45 a), c (f46 a), c (f47 a), c (f48 a), c (f49 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)

instance (c (f0 a), c (f1 a), c (f2 a), c (f3 a), c (f4 a), c (f5 a), c (f6 a), c (f7 a), c (f8 a), c (f9 a), c (f10 a), c (f11 a), c (f12 a), c (f13 a), c (f14 a), c (f15 a), c (f16 a), c (f17 a), c (f18 a), c (f19 a), c (f20 a), c (f21 a), c (f22 a), c (f23 a), c (f24 a), c (f25 a), c (f26 a), c (f27 a), c (f28 a), c (f29 a), c (f30 a), c (f31 a), c (f32 a), c (f33 a), c (f34 a), c (f35 a), c (f36 a), c (f37 a), c (f38 a), c (f39 a), c (f40 a), c (f41 a), c (f42 a), c (f43 a), c (f44 a), c (f45 a), c (f46 a), c (f47 a), c (f48 a), c (f49 a), c (f50 a)) => Apply0 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50] a where
  apply0' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply0' proxy f u@(Union n r) = apply0' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply0_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply0_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2) = apply0_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)


class Apply1 (c :: (k -> *) -> Constraint) (fs :: [k -> *]) where
  apply1' :: proxy c -> (forall g . c g => (forall x. g x -> Union fs x) -> g a -> b) -> Union fs a -> b

  apply1_2' :: proxy c -> (forall g . c g => (forall x. g x -> Union fs x) -> g a -> g b -> d) -> Union fs a -> Union fs b -> Maybe d

apply1 :: Apply1 c fs => proxy c -> (forall g . c g => g a -> b) -> Union fs a -> b
apply1 proxy f = apply1' proxy (const f)

apply1_2 :: Apply1 c fs => proxy c -> (forall g . c g => g a -> g b -> d) -> Union fs a -> Union fs b -> Maybe d
apply1_2 proxy f = apply1_2' proxy (const f)

instance (c f0) => Apply1 c '[f0] where
  apply1' _ f (Union _ r) = f (Union 0) (unsafeCoerce r :: f0 a)

  apply1_2' _ f (Union _ r1) (Union _ r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))

instance (c f0, c f1) => Apply1 c '[f0, f1] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2) => Apply1 c '[f0, f1, f2] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3) => Apply1 c '[f0, f1, f2, f3] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4) => Apply1 c '[f0, f1, f2, f3, f4] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5) => Apply1 c '[f0, f1, f2, f3, f4, f5] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41, c f42) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41, c f42, c f43) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41, c f42, c f43, c f44) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41, c f42, c f43, c f44, c f45) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41, c f42, c f43, c f44, c f45, c f46) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41, c f42, c f43, c f44, c f45, c f46, c f47) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41, c f42, c f43, c f44, c f45, c f46, c f47, c f48) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41, c f42, c f43, c f44, c f45, c f46, c f47, c f48, c f49) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

instance (c f0, c f1, c f2, c f3, c f4, c f5, c f6, c f7, c f8, c f9, c f10, c f11, c f12, c f13, c f14, c f15, c f16, c f17, c f18, c f19, c f20, c f21, c f22, c f23, c f24, c f25, c f26, c f27, c f28, c f29, c f30, c f31, c f32, c f33, c f34, c f35, c f36, c f37, c f38, c f39, c f40, c f41, c f42, c f43, c f44, c f45, c f46, c f47, c f48, c f49, c f50) => Apply1 c '[f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50] where
  apply1' _ f (Union 0 r) = f (Union 0) (unsafeCoerce r :: f0 a)
  apply1' proxy f u@(Union n r) = apply1' proxy (\ toU -> f (weaken . toU)) (Union (pred n) r `asStrongerUnionTypeOf` u)

  apply1_2' _ f (Union 0 r1) (Union 0 r2) = Just (f (Union 0) (unsafeCoerce r1 :: f0 a) (unsafeCoerce r2))
  apply1_2' proxy f u1@(Union n1 r1) u2@(Union n2 r2)
    | n1 == n2  = apply1_2' proxy (\ toU -> f (weaken . toU)) (Union (pred n1) r1 `asStrongerUnionTypeOf` u1) (Union (pred n2) r2 `asStrongerUnionTypeOf` u2)
    | otherwise = Nothing

type family EQU (a :: k) (b :: k) :: Bool where
  EQU a a = 'True
  EQU a b = 'False

-- This class is used for emulating monad transformers
class (t :< r) => MemberU2 (tag :: k -> * -> *) (t :: * -> *) r | tag r -> t
instance (t1 :< r, MemberU' (EQU t1 t2) tag t1 (t2 ': r)) => MemberU2 tag t1 (t2 ': r)

class (t :< r) =>
      MemberU' (f::Bool) (tag :: k -> * -> *) (t :: * -> *) r | tag r -> t

instance MemberU' 'True tag (tag e) (tag e ': r)
instance (t :< (t' ': r), MemberU2 tag t r) =>
           MemberU' 'False tag t (t' ': r)

instance Apply1 Foldable fs => Foldable (Union fs) where
  foldMap f u = apply1 (Proxy :: Proxy Foldable) (foldMap f) u

instance Apply1 Functor fs => Functor (Union fs) where
  fmap f u = apply1' (Proxy :: Proxy Functor) ((. fmap f)) u

instance (Apply1 Foldable fs, Apply1 Functor fs, Apply1 Traversable fs) => Traversable (Union fs) where
  traverse f u = apply1' (Proxy :: Proxy Traversable) ((. traverse f) . fmap) u

instance Apply0 Eq fs a => Eq (Union fs a) where
  u1 == u2 = fromMaybe False (apply0_2 (Proxy :: Proxy Eq) (==) u1 u2)

instance Apply0 Show fs a => Show (Union fs a) where
  showsPrec d u = apply0 (Proxy :: Proxy Show) (showsPrec d) u

instance Apply1 Eq1 fs => Eq1 (Union fs) where
  liftEq eq u1 u2 = fromMaybe False (apply1_2 (Proxy :: Proxy Eq1) (liftEq eq) u1 u2)


instance Apply1 Show1 fs => Show1 (Union fs) where
  liftShowsPrec sp sl d u = apply1 (Proxy :: Proxy Show1) (liftShowsPrec sp sl d) u
