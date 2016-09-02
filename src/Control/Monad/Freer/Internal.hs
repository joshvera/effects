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
  Arrow,
  Arrows,
  Union,

  decomp,
  tsingleton,

  applyEffs,
  composeEffs,
  send,
  run,
  runM,
  handleRelay,
  handleRelayS,
  interpose,
) where

import Data.Open.Union
import Data.FTCQueue


-- | An effectful arrow from 'a' to 'b'
-- that also performs effects denoted by 'eff'.
type Arrow effs a b = a -> Eff effs b

-- | An effectful function from 'a' to 'b' that is a composition of
-- several effectful functions. The paremeter 'effs' describes the overall
-- effect. The composition members are accumulated in a type-aligned
-- queue.
type Arrows effs a b = FTCQueue (Eff effs) a b

-- | An effectful computation that returns 'b' and performs effects 'effs'.
data Eff effs b
  -- | Done with the value of type b.
  = Val b
  -- | Send a request of type 'Union effs a' with the 'Arrs effs a b' queue.
  | forall a. E (Union effs a) (Arrows effs a b)


-- * Composing and Applying Effects

-- | Returns an effect by applying a given value to a queue of effects.
applyEffs :: Arrows effs a b -> a -> Eff effs b
applyEffs q' x =
   case tviewl q' of
   TOne k  -> k x
   k :< t -> case k x of
     Val y -> applyEffs t y
     E u q -> E u (q >< t)

-- | Returns a queue of effects' from a to c with an updated list of effects,
-- given a queue of effects and a function from effects to effects'.
composeEffs :: Arrows effs a b -> (Eff effs b -> Eff effs' c) -> Arrow effs' a c
composeEffs g h a = h $ applyEffs g a


-- * Sending and Running Effects

-- | Send a request and wait for a reply.
send :: (eff :< effs) => eff b -> Eff effs b
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
-- and returns an 'm b'.
--
-- This is useful for plugging in traditional transformer stacks.
runM :: Monad m => Eff '[m] b -> m b
runM (Val x) = pure x
runM (E u q) = case decomp u of
  Right mb -> mb >>= runM . applyEffs q
  Left _   -> error "Internal:runM - This (Left) should never happen"

-- | Given an effect request, either handle it with the given 'pure' function,
-- or relay it to the given 'bind' function.
handleRelay :: Arrow effs a b -- ^ An 'pure' effectful arrow.
            -- | A function to relay to, that binds a relayed 'eff v' to
            -- an effectful arrow and returns a new effect.
            -> (forall v. eff v -> Arrow effs v b -> Eff effs b)
            -- | The effect to relay.
            -> Eff (eff ': effs) a
            -- The resulting effect with 'eff' consumed.
            -> Eff effs b
handleRelay pure' bind = loop
 where
  loop (Val x)  = pure' x
  loop (E u' q)  = case decomp u' of
    Right x -> bind x k
    Left  u -> E u (tsingleton k)
   where k = composeEffs q loop

-- | Parameterized 'handleRelay'
-- Allows sending along some state to be handled for the target
-- effect, or relayed to a handler that can handle the target effect.
handleRelayS :: s
                -> (s -> a -> Eff effs b)
                -> (forall v. s -> eff v -> (s -> Arrow effs v b) -> Eff effs b)
                -> Eff (eff ': effs) a
                -> Eff effs b
handleRelayS s' pure' bind = loop s'
  where
    loop s (Val x)  = pure' s x
    loop s (E u' q)  = case decomp u' of
      Right x -> bind s x k
      Left  u -> E u (tsingleton (k s))
     where k s'' x = loop s'' $ applyEffs q x

-- | Intercept the request and possibly reply to it, but leave it
-- unhandled
interpose :: (eff :< effs)
             => (a -> Eff effs b)
             -> (forall v. eff v -> Arrow effs v b -> Eff effs b)
             -> Eff effs a -> Eff effs b
interpose ret h = loop
 where
   loop (Val x)  = ret x
   loop (E u q)  = case prj u of
     Just x -> h x k
     _      -> E u (tsingleton k)
    where k = composeEffs q loop

-- * Effect Instances

instance Functor (Eff effs) where
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f))
  {-# INLINE fmap #-}

instance Applicative (Eff effs) where
  pure = Val
  {-# INLINE pure #-}

  Val f <*> Val x = Val $ f x
  Val f <*> E u q = E u (q |> (Val . f))
  E u q <*> Val x = E u (q |> (Val . ($ x)))
  E u q <*> m     = E u (q |> (`fmap` m))
  {-# INLINE (<*>) #-}

instance Monad (Eff effs) where
  return = Val
  {-# INLINE return #-}

  Val x >>= k = k x
  E u q >>= k = E u (q |> k)
  {-# INLINE (>>=) #-}
