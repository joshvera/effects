{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

{-|
Module      : Control.Monad.Effect.State
Description : State effects for computations that carry state
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

Composable handler for State effects.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.State (
  State(..),
  get,
  gets,
  put,
  modify,
  modify',
  runState,
  localState,
  transactionState
) where

import Control.Monad.Effect.Internal
import Data.Proxy

--------------------------------------------------------------------------------
                         -- State, strict --
--------------------------------------------------------------------------------

-- | Run a 'State s' effect given an effect and an initial state.
runState :: Eff (State s ': e) b -> s -> Eff e (b, s)
runState (Val b) s = pure (b, s)
runState (E u q) s = case decompose u of
  Left  u'       -> E u' $ tsingleton (Arrow (flip runState s . apply q))
  Right Get      -> runState (apply q s) s
  Right (Put s') -> runState (apply q ()) s'


-- | Strict State effects: one can either Get values or Put them
data State s v where
  Get :: State s s
  Put :: !s -> State s ()

-- | Retrieve state
get :: Member (State s) e => Eff e s
get = send Get

-- | Retrieve state, modulo a projection.
gets :: Member (State s) e => (s -> a) -> Eff e a
gets f = f <$> get

-- | Store state
put :: Member (State s) e => s -> Eff e ()
put s = send (Put s)

-- | Modify state
modify :: Member (State s) e => (s -> s) -> Eff e ()
modify f = fmap f get >>= put

-- | Modify state strictly
modify' :: Member (State s) e => (s -> s) -> Eff e ()
modify' f = do
  v <- get
  put $! f v

-- |
-- An encapsulated State handler, for transactional semantics
-- The global state is updated only if the transactionState finished
-- successfully
transactionState :: forall s e a. Member (State s) e
                    => Proxy s
                    -> Eff e a
                    -> Eff e a
transactionState _ m = do s <- get; loop s m
 where
   loop :: s -> Eff e a -> Eff e a
   loop s (Val x) = put s >> pure x
   loop s (E (u :: Union e b) q) = case prj u :: Maybe (State s b) of
     Just Get      -> loop s (apply q s)
     Just (Put s') -> loop s'(apply q ())
     _             -> E u (tsingleton k)
      where k = q >>> (loop s)

localState :: forall effects a s. Member (State s) effects => (s -> s) -> Eff effects a -> Eff effects a
localState f effect = do
  original <- get
  put (f original)
  v <- effect
  put original
  pure v
