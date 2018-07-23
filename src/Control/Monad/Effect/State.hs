{-# LANGUAGE DataKinds, KindSignatures #-}
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
runState :: (Effectful m, Effects e) => s -> m (State s ': e) b -> m e (s, b)
runState = raiseHandler . go
  where go s (Return a)         = pure (s, a)
        go s (Effect Get k)     = runState s (k s)
        go _ (Effect (Put s) k) = runState s (k ())
        go s (Other u k)        = liftStatefulHandler (s, ()) (uncurry runState) u k


-- | Strict State effects: one can either Get values or Put them
data State s (m :: * -> *) v where
  Get :: State s m s
  Put :: !s -> State s m ()

-- | Retrieve state
get :: (Member (State s) e, Effectful m) => m e s
get = send Get

-- | Retrieve state, modulo a projection.
gets :: (Member (State s) e, Effectful m) => (s -> a) -> m e a
gets f = raiseEff (f <$> get)

-- | Store state
put :: (Member (State s) e, Effectful m) => s -> m e ()
put s = send (Put s)

-- | Modify state
modify :: (Member (State s) e, Effectful m) => (s -> s) -> m e ()
modify f = raiseEff (fmap f get >>= put)

-- | Modify state strictly
modify' :: (Member (State s) e, Effectful m) => (s -> s) -> m e ()
modify' f = raiseEff $ do
  v <- get
  put $! f v

-- |
-- An encapsulated State handler, for transactional semantics
-- The global state is updated only if the transactionState finished
-- successfully
transactionState :: forall s e a m. (Member (State s) e, Effectful m)
                    => Proxy s
                    -> m e a
                    -> m e a
transactionState _ m = raiseEff $ do s <- get; loop s (lowerEff m)
 where
   loop :: s -> Eff e a -> Eff e a
   loop s (Return x) = put s >> pure x
   loop s (E (u :: Union e (Eff e) b) q) = case prj u :: Maybe (State s (Eff e) b) of
     Just Get      -> loop s (apply q s)
     Just (Put s') -> loop s'(apply q ())
     _             -> E u (tsingleton (Arrow k))
      where k = q >>> (loop s)

localState :: (Member (State s) effects, Effectful m) => (s -> s) -> m effects a -> m effects a
localState f action = raiseEff $ do
  original <- get
  put (f original)
  v <- lowerEff action
  put original
  pure v


instance PureEffect (State s)
instance Effect (State s) where
  handleState c dist (Request Get k) = Request Get (dist . (<$ c) . k)
  handleState c dist (Request (Put s) k) = Request (Put s) (dist . (<$ c) . k)
