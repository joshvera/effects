{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, KindSignatures, MultiParamTypeClasses, RankNTypes, RoleAnnotations, ScopedTypeVariables, TypeOperators #-}

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

module Data.Union
( Union
, decompose
, weaken
, strengthen
, inj
, prj
, Member
) where

import Unsafe.Coerce (unsafeCoerce)

type role Union nominal nominal nominal

-- Strong Sum (Existential with the evidence) is an open union
-- t is can be a GADT and hence not necessarily a Functor.
-- Int is the index of t in the list r; that is, the index of t in the
-- universe r.
data Union (r :: [ (* -> *) -> (* -> *) ]) (f :: * -> *) (v :: *) where
  Union :: {-# UNPACK #-} !Int -> t f v -> Union r f v

-- | Inject a functor into a type-aligned union.
inj :: forall e r f v. Member e r => e f v -> Union r f v
inj = inj' (getOffset (offset :: Offset e r))
{-# INLINE inj #-}

-- | Maybe project a functor out of a type-aligned union.
prj :: forall e r f v. Member e r => Union r f v -> Maybe (e f v)
prj = prj' (getOffset (offset :: Offset e r))
{-# INLINE prj #-}


decompose :: Union (t ': r) f v -> Either (Union r f v) (t f v)
decompose (Union 0 v) = Right $ unsafeCoerce v
decompose (Union n v) = Left  $ Union (n-1) v
{-# INLINE [2] decompose #-}


weaken :: Union r f v -> Union (any ': r) f v
weaken (Union n v) = Union (n+1) v

strengthen :: Union '[last] f v -> last f v
strengthen (Union _ t) = unsafeCoerce t


-- Find an index of an element in an `r'.
-- The element must exist, so this is essentially a compile-time computation.
class Member t r where
  offset :: Offset t r

instance Member t (t ': r) where
  offset = Offset 0

instance {-# OVERLAPPABLE #-} Member t r => Member t (t' ': r) where
  offset = Offset $ 1 + getOffset (offset :: Offset t r)


-- Implementation details

inj' :: Int -> t f v -> Union r f v
inj' = Union
{-# INLINE inj' #-}

prj' :: Int -> Union r f v -> Maybe (t f v)
prj' n (Union n' x) | n == n'   = Just (unsafeCoerce x)
                    | otherwise = Nothing
{-# INLINE prj' #-}

newtype Offset (t :: (* -> *) -> (* -> *)) (r :: [(* -> *) -> (* -> *)]) = Offset { getOffset :: Int }


-- | Specialized version of 'decompose'.
decompose0 :: Union '[t] f v -> Either (Union '[] f v) (t f v)
decompose0 (Union _ v) = Right $ unsafeCoerce v
-- No other case is possible
{-# RULES "decompose/singleton"  decompose = decompose0 #-}
{-# INLINE decompose0 #-}
