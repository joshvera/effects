{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances, FunctionalDependencies, GADTs, RankNTypes, ScopedTypeVariables, TypeFamilies, TypeOperators, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-} -- Due to MemberU2

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
  strengthen,
  Delete,
  type (\\),
  split,
  inj,
  prj,
  Member,
  Members,
  MemberU2,
) where

import GHC.Exts (Constraint)
import Unsafe.Coerce (unsafeCoerce)


-- Strong Sum (Existential with the evidence) is an open union
-- t is can be a GADT and hence not necessarily a Functor.
-- Int is the index of t in the list r; that is, the index of t in the
-- universe r.
data Union (r :: [ * -> * ]) (v :: *) where
  Union :: {-# UNPACK #-} !Int -> t v -> Union r v

{-# INLINE prj' #-}
{-# INLINE inj' #-}
inj' :: Int -> t v -> Union r v
inj' = Union

prj' :: Int -> Union r v -> Maybe (t v)
prj' n (Union n' x) | n == n'   = Just (unsafeCoerce x)
                    | otherwise = Nothing

newtype P (t :: * -> *) (r :: [* -> *]) = P { unP :: Int }

-- | Find a list of members 'ms' in an open union 'r'.
type family Members ms r :: Constraint where
  Members (t ': cs) r = (Member t r, Members cs r)
  Members '[] r = ()

-- | Inject a functor into a type-aligned union.
inj :: forall e r v. Member e r => e v -> Union r v
inj = inj' (unP (elemNo :: P e r))
{-# INLINE inj #-}

-- | Maybe project a functor out of a type-aligned union.
prj :: forall e r v. Member e r => Union r v -> Maybe (e v)
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

-- | Weaken a 'Union' by adding another type to the front of the list.
weaken :: Union r w -> Union (any ': r) w
weaken (Union n v) = Union (n+1) v

-- | Strengthen a singleton 'Union' by extracting its value.
strengthen :: Union '[t] a -> t a
strengthen (Union _ t) = unsafeCoerce t


-- | Delete the element @t@ from the list @ts@.
type family Delete (t :: * -> *) (ts :: [* -> *]) :: [* -> *] where
  Delete t (t ': ts) = ts
  Delete t (t' ': ts) = t' ': Delete t ts

class Member t ts => (t \\ ts) (rest :: [* -> *]) | t ts -> rest, ts rest -> t

instance (t \\ (t ': ts)) ts
instance {-# OVERLAPPABLE #-} (t \\ ts) ts' => (t \\ (t' ': ts)) (t' : ts')

-- | Split a 'Union' into 'Either' the selected member, or the 'Union' of the remaining values.
split :: forall t ts a . Member t ts => Union ts a -> Either (Union (Delete t ts) a) (t a)
split (Union n t) = case compare n (unP (elemNo :: P t ts)) of
  LT -> Left  (Union n t)
  EQ -> Right (unsafeCoerce t)
  GT -> Left  (Union (n-1) t)


-- Find an index of an element in an `r'.
-- The element must exist, so this is essentially a compile-time computation.
class Member t r where
  elemNo :: P t r

instance Member t (t ': r) where
  elemNo = P 0

instance {-# OVERLAPPABLE #-} Member t r => Member t (t' ': r) where
  elemNo = P $ 1 + unP (elemNo :: P t r)


type family EQU (a :: * -> *) (b :: * -> *) :: Bool where
  EQU a a = 'True
  EQU a b = 'False

-- This class is used for emulating monad transformers
class Member t r => MemberU2 (tag :: (* -> *) -> * -> *) (t :: * -> *) r | tag r -> t
instance (Member t1 (t2 ': r), MemberU' (EQU t1 t2) tag t1 (t2 ': r)) => MemberU2 tag t1 (t2 ': r)

class Member t r =>
      MemberU' (f::Bool) (tag :: (* -> *) -> * -> *) (t :: * -> *) r | tag r -> t

instance MemberU' 'True tag (tag e) (tag e ': r)
instance (Member t (t' ': r), MemberU2 tag t r) =>
           MemberU' 'False tag t (t' ': r)
