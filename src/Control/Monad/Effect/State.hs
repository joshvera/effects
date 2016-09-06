{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

{-|
Module      : Control.Monad.Effect.State
Description : State effects, for state-carrying computations.
Copyright   : Alej Cabrera 2015
License     : BSD-3
Maintainer  : cpp.cabrera@gmail.com
Stability   : experimental
Portability : POSIX

Composable handler for State effects.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.State (
  State,
  get,
  put,
  modify,
  runState,

  transactionState
) where

import Control.Monad.Effect.Internal
import Data.Proxy

--------------------------------------------------------------------------------
                         -- State, strict --
--------------------------------------------------------------------------------

-- | Strict State effects: one can either Get values or Put them
data State s v where
  Get :: State s s
  Put :: !s -> State s ()

-- | Retrieve state
get :: (State s :< e) => Eff e s
get = send Get

-- | Store state
put :: (State s :< e) => s -> Eff e ()
put s = send (Put s)

-- | Modify state
modify :: (State s :< e) => (s -> s) -> Eff e ()
modify f = fmap f get >>= put

-- | Handler for State effects
runState :: Eff (State s ': e) w -> s -> Eff e (w, s)
runState (Val x) s = pure (x,s)
runState (E u q) s = case decomp u of
  Right Get      -> runState (apply q s) s
  Right (Put s') -> runState (apply q ()) s'
  Left  u'       -> E u' (tsingleton (\x -> runState (apply q x) s))


-- |
-- An encapsulated State handler, for transactional semantics
-- The global state is updated only if the transactionState finished
-- successfully
transactionState :: forall s e a. (State s :< e)
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
