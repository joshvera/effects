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
  -- * Constructing and Sending Effects
  Eff(..),
  send,
  -- * Decomposing Unions
  type(:<),
  type(:<:),
  -- | Inserts multiple effects into 'E'.
  inj,
  prj,
  -- * Constructing and Decomposing Arrows
  decomp,
  Arrow,
  tsingleton,
  Arrows,
  Union,
  -- * Composing and Applying Arrows
  apply,
  (<<<),
  (>>>),
  -- * Running Effects
  run,
  runM,
  -- * Relaying and Interposing Effects
  handleRelay,
  handleRelayS,
  interpose,
) where

import Data.Open.Union
import Data.FTCQueue

-- | An effectful computation that returns 'b' and performs 'effects'.
data Eff effects b
  -- | Done with the value of type b.
  = Val b
  -- | Send a request of type 'Union e a' with the 'Arrs e a b' queue.
  | forall a. E (Union effects a) (Arrows effects a b)

-- | A queue of 'effects' from 'a' to 'b'.
type Arrows effects a b = FTCQueue (Eff effects) a b

-- | An effectful function from 'a' to 'b'
--   that also performs 'effects'.
type Arrow effects a b = a -> Eff effects b

-- * Composing and Applying Effects

-- | Returns an effect by applying a given value to a queue of effects.
apply :: Arrows effects a b -> a -> Eff effects b
apply q' x =
   case tviewl q' of
   TOne k  -> k x
   k :< t -> case k x of
     Val y -> t `apply` y
     E u q -> E u (q >< t)

-- | Compose left to right.
(>>>) :: Arrows effects a b
           -> (Eff effects b -> Eff effects' c) -- ^ An function to compose.
           -> Arrow effects' a c
(>>>) arrows f = f . apply arrows

-- | Compose right to left.
(<<<) :: (Eff effects b -> Eff effects' c) -- ^ An function to compose.
           -> Arrows effects a b
           -> Arrow effects' a c
(<<<) f arrows  = f . apply arrows

-- * Sending and Running Effects

-- | Send a request and wait for a reply.
send :: (eff :< e) => eff b -> Eff e b
send t = E (inj t) (tsingleton Val)

-- | Runs an effect whose effects has been consumed.
--
-- Typically composed as follows:
--
-- @
-- run . runEff1 eff1Arg . runEff2 eff2Arg1 eff2Arg2 (program)
-- @
run :: Eff '[] b -> b
run (Val x) = x
run _       = error "Internal:run - This (E) should never happen"
-- the other case is unreachable since Union [] a cannot be
-- constructed. Therefore, run is a total function if its argument
-- terminates.

-- | Runs an effect for which all but one Monad effect has been consumed,
-- and returns an 'm a'.
--
-- This is useful for plugging in traditional transformer stacks.
runM :: Monad m => Eff '[m] a -> m a
runM (Val x) = pure x
runM (E u q) = case decomp u of
  Right m -> m >>= runM . (apply q)
  Left _   -> error "Internal:runM - This (Left) should never happen"

-- | Given an effect request, either handle it with the given 'pure' function,
-- or relay it to the given 'bind' function.
handleRelay :: Arrow e a b -- ^ An 'pure' effectful arrow.
            -- | A function to relay to, that binds a relayed 'eff v' to
            -- an effectful arrow and returns a new effect.
            -> (forall v. eff v -> Arrow e v b -> Eff e b)
            -> Eff (eff ': e) a -- ^ The 'eff' to relay and consume.
            -> Eff e b -- ^ The relayed effect with 'eff' consumed.
handleRelay pure' bind = loop
 where
  loop (Val x)  = pure' x
  loop (E u' q)  = case decomp u' of
    Right x -> bind x k
    Left  u -> E u (tsingleton k)
   where k = q >>> loop

-- | Parameterized 'handleRelay'
-- Allows sending along some state to be handled for the target
-- effect, or relayed to a handler that can handle the target effect.
handleRelayS :: s
                -> (s -> a -> Eff e b)
                -> (forall v. s -> eff v -> (s -> Arrow e v b) -> Eff e b)
                -> Eff (eff ': e) a
                -> Eff e b
handleRelayS s' pure' bind = loop s'
  where
    loop s (Val x)  = pure' s x
    loop s (E u' q)  = case decomp u' of
      Right x -> bind s x k
      Left  u -> E u (tsingleton (k s))
     where k s'' x = loop s'' $ q `apply` x

-- | Intercept the request and possibly reply to it, but leave it
-- unhandled
interpose :: (eff :< e)
             => (a -> Eff e b)
             -> (forall v. eff v -> Arrow e v b -> Eff e b)
             -> Eff e a -> Eff e b
interpose ret h = loop
 where
   loop (Val x)  = ret x
   loop (E u q)  = case prj u of
     Just x -> h x k
     _      -> E u (tsingleton k)
    where k = q >>> loop

-- * Effect Instances

instance Functor (Eff e) where
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f))
  {-# INLINE fmap #-}

instance Applicative (Eff e) where
  pure = Val
  {-# INLINE pure #-}

  Val f <*> Val x = Val $ f x
  Val f <*> E u q = E u (q |> (Val . f))
  E u q <*> Val x = E u (q |> (Val . ($ x)))
  E u q <*> m     = E u (q |> (`fmap` m))
  {-# INLINE (<*>) #-}

instance Monad (Eff e) where
  return = Val
  {-# INLINE return #-}

  Val x >>= k = k x
  E u q >>= k = E u (q |> k)
  {-# INLINE (>>=) #-}
