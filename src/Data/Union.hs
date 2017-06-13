{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

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
  MemberU2
) where

import Data.Functor.Classes (Eq1(..), Show1(..))
import Unsafe.Coerce(unsafeCoerce)
import GHC.Exts (Constraint)

infixr 5 :<
-- | Find an functor in a record.
class (FindElem e r) => (e :: * -> *) :< r where
  -- | Inject a functor into a type-aligned union.
  inj :: e v -> Union r v
  -- | Maybe project a functor out of a type-aligned union.
  prj :: Union r v -> Maybe (e v)

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

instance (FindElem t r) => t :< r where
  {-# INLINE inj #-}
  {-# INLINE prj #-}
  inj = inj' (unP (elemNo :: P t r))
  prj = prj' (unP (elemNo :: P t r))


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

-- Find an index of an element in an `r'.
-- The element must exist, so this is essentially a compile-time computation.
class FindElem (t :: * -> *) r where
  elemNo :: P t r

instance {-# OVERLAPPING #-} FindElem t (t ': r) where
  elemNo = P 0

instance {-# OVERLAPPING #-} FindElem t r => FindElem t (t' ': r) where
  elemNo = P $ 1 + unP (elemNo :: P t r)


type family EQU (a :: k) (b :: k) :: Bool where
  EQU a a = 'True
  EQU a b = 'False

-- This class is used for emulating monad transformers
class (t :< r) => MemberU2 (tag :: k -> * -> *) (t :: * -> *) r | tag r -> t
instance (MemberU' (EQU t1 t2) tag t1 (t2 ': r)) => MemberU2 tag t1 (t2 ': r)

class (t :< r) =>
      MemberU' (f::Bool) (tag :: k -> * -> *) (t :: * -> *) r | tag r -> t

instance MemberU' 'True tag (tag e) (tag e ': r)
instance (t :< (t' ': r), MemberU2 tag t r) =>
           MemberU' 'False tag t (t' ': r)

instance (Foldable f, Foldable (Union fs)) => Foldable (Union (f ': fs)) where
  foldMap f u = case decompose u of
    Left u' -> foldMap f u'
    Right r -> foldMap f r

instance Foldable (Union '[]) where
  foldMap _ _ = mempty

instance (Functor f, Functor (Union fs)) => Functor (Union (f ': fs)) where
  fmap f u = case decompose u of
    Left u' -> weaken (fmap f u')
    Right r -> inj (fmap f r)

instance Functor (Union '[]) where
  fmap _ _ = error "fmap over an empty Union"

instance (Traversable f, Traversable (Union fs)) => Traversable (Union (f ': fs)) where
  traverse f u = case decompose u of
    Left u' -> weaken <$> traverse f u'
    Right r -> inj <$> traverse f r

instance Traversable (Union '[]) where
  traverse _ _ = error "traverse over an empty Union"

instance (Eq (f a), Eq (Union fs a)) => Eq (Union (f ': fs) a) where
  u1 == u2 = case (decompose u1, decompose u2) of
    (Left u1', Left u2') -> u1' == u2'
    (Right r1, Right r2) -> r1 == r2
    _ -> False

instance Eq (Union '[] a) where
  _ == _ = False

instance (Show (f a), Show (Union fs a)) => Show (Union (f ': fs) a) where
  showsPrec d u = case decompose u of
    Left u' -> showsPrec d u'
    Right r -> showsPrec d r

instance Show (Union '[] a) where
  showsPrec _ _ = id

instance (Eq1 f, Eq1 (Union fs)) => Eq1 (Union (f ': fs)) where
  liftEq eq u1 u2 = case (decompose u1, decompose u2) of
    (Left u1', Left u2') -> liftEq eq u1' u2'
    (Right r1, Right r2) -> liftEq eq r1 r2

instance Eq1 (Union '[]) where
  liftEq _ _ _ = False

instance (Show1 f, Show1 (Union fs)) => Show1 (Union (f ': fs)) where
  liftShowsPrec sp sl d u = case decompose u of
    Left u' -> liftShowsPrec sp sl d u'
    Right r -> liftShowsPrec sp sl d r

instance Show1 (Union '[]) where
  liftShowsPrec _ _ _ _ = id
