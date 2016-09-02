{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- The following is needed to define MonadPlus instance. It is decidable
-- (there is no recursion!), but GHC cannot see that.
-- TODO: remove once GHC can deduce the decidability of this instance
{-# LANGUAGE UndecidableInstances #-}

{-|
Module      : Control.Monad.Freer.Internal
Description : Mechanisms to make effects work
Copyright   : Alej Cabrera 2015
License     : BSD-3
Maintainer  : cpp.cabrera@gmail.com
Stability   : experimental
Portability : POSIX

Internal machinery for this effects library. This includes:

* Eff data type, for expressing effects
* NonDetEff data type, for nondeterministic effects
* Functions for facilitating the construction of effects and their handlers

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Freer.Internal (
  Eff(..),
  type(:<),
  type(:<:),
  inj,
  prj,
  Arr,
  Arrs,
  Union,

  decomp,
  tsingleton,

  qApp,
  qComp,
  send,
  run,
  runM,
  handleRelay,
  handleRelayS,
  interpose,
) where

import Data.Open.Union
import Data.FTCQueue


-- |
-- An effectful function from 'a' to 'b' that also performs effects
-- denoted by 'eff'.
type Arr effs a b = a -> Eff effs b

-- |
-- An effectful function from 'a' to 'b' that is a composition of
-- several effectful functions. The paremeter 'effs' describes the overall
-- effect. The composition members are accumulated in a type-aligned
-- queue.
type Arrs effs a b = FTCQueue (Eff effs) a b

-- |
-- The Eff representation.
--
-- Status of a coroutine (client):
-- * Val: Done with the value of type a
-- * E  : Sending a request of type Union r with the continuation Arrs r b a
data Eff effs b = Val b
             | forall a. E (Union effs a) (Arrs effs a b)

-- | Function application in the context of an array of effects, Arrs r b w
qApp :: Arrs effs a b -> a -> Eff effs b
qApp q' x =
   case tviewl q' of
   TOne k  -> k x
   k :< t -> case k x of
     Val y -> qApp t y
     E u q -> E u (q >< t)

-- | Composition of effectful arrows
-- Allows for the caller to change the effect environment, as well
qComp :: Arrs effs a b -> (Eff effs b -> Eff effs' c) -> Arr effs' a c
qComp g h a = h $ qApp g a

instance Functor (Eff effs) where
  {-# INLINE fmap #-}
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f))

instance Applicative (Eff effs) where
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}
  pure = Val
  Val f <*> Val x = Val $ f x
  Val f <*> E u q = E u (q |> (Val . f))
  E u q <*> Val x = E u (q |> (Val . ($ x)))
  E u q <*> m     = E u (q |> (`fmap` m))

instance Monad (Eff effs) where
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}
  return = Val
  Val x >>= k = k x
  E u q >>= k = E u (q |> k)

-- | send a request and wait for a reply
send :: (eff :< effs) => eff b -> Eff effs b
send t = E (inj t) (tsingleton Val)

--------------------------------------------------------------------------------
                       -- Base Effect Runner --
--------------------------------------------------------------------------------
-- | Runs a set of Effects. Requires that all effects are consumed.
-- Typically composed as follows:
-- > run . runEff1 eff1Arg . runEff2 eff2Arg1 eff2Arg2 (program)
run :: Eff '[] b -> b
run (Val x) = x
run _       = error "Internal:run - This (E) should never happen"

-- | Runs a set of Effects. Requires that all effects are consumed,
-- except for a single effect known to be a monad.
-- The value returned is a computation in that monad.
-- This is useful for plugging in traditional transformer stacks.
runM :: Monad m => Eff '[m] b -> m b
runM (Val x) = return x
runM (E u q) = case decomp u of
  Right mb -> mb >>= runM . qApp q
  Left _   -> error "Internal:runM - This (Left) should never happen"

-- the other case is unreachable since Union [] a cannot be
-- constructed. Therefore, run is a total function if its argument
-- terminates.

-- | Given a request, either handle it or relay it.
handleRelay :: (a -> Eff effs b) ->
               (forall v. eff v -> Arr effs v b -> Eff effs b) ->
               Eff (eff ': effs) a -> Eff effs b
handleRelay ret h = loop
 where
  loop (Val x)  = ret x
  loop (E u' q)  = case decomp u' of
    Right x -> h x k
    Left  u -> E u (tsingleton k)
   where k = qComp q loop

-- | Parameterized 'handleRelay'
-- Allows sending along some state to be handled for the target
-- effect, or relayed to a handler that can handle the target effect.
handleRelayS :: s ->
                (s -> a -> Eff effs b) ->
                (forall v. s -> eff v -> (s -> Arr effs v b) -> Eff effs b) ->
                Eff (eff ': effs) a -> Eff effs b
handleRelayS s' ret h = loop s'
  where
    loop s (Val x)  = ret s x
    loop s (E u' q)  = case decomp u' of
      Right x -> h s x k
      Left  u -> E u (tsingleton (k s))
     where k s'' x = loop s'' $ qApp q x

-- | Intercept the request and possibly reply to it, but leave it
-- unhandled
interpose :: (eff :< effs) =>
             (a -> Eff effs b) -> (forall v. eff v -> Arr effs v b -> Eff effs b) ->
             Eff effs a -> Eff effs b
interpose ret h = loop
 where
   loop (Val x)  = ret x
   loop (E u q)  = case prj u of
     Just x -> h x k
     _      -> E u (tsingleton k)
    where k = qComp q loop
