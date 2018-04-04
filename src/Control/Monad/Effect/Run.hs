{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, FunctionalDependencies, GADTs, TypeOperators, UndecidableInstances #-}
module Control.Monad.Effect.Run where

import Control.Monad.Effect.Coroutine
import Control.Monad.Effect.Embedded
import Control.Monad.Effect.Exception as Exc
import Control.Monad.Effect.Fail
import Control.Monad.Effect.Fresh
import qualified Control.Monad.Effect.Internal as Eff
import Control.Monad.Effect.NonDet
import Control.Monad.Effect.Reader
import Control.Monad.Effect.Resumable as Resumable
import Control.Monad.Effect.State
import Control.Monad.Effect.Trace
import Control.Monad.Effect.Writer

-- | Elimination of effects.
--
--   Instances provide interpreters, optionally taking arguments and optionally modifying the result type.
class Run effects result function | effects result -> function where
  -- | Interpret the effects in the given computation, possibly taking some arguments, and return the result.
  run :: Eff.Eff effects result -> function


instance Run effects result rest => Run (Yield a b ': effects) result ((a -> b) -> rest) where
  run = fmap run . runCoro

instance Run effects result rest => Run (Embedded effects ': effects) result rest where
  run = run . Eff.relay pure (\ (Embed e) k -> e >>= k)

instance Run effects (Either exc result) rest => Run (Exc exc ': effects) result rest where
  run = run . Exc.runError

instance Run effects (Either String result) rest => Run (Fail ': effects) result rest where
  run = run . runFail

instance Run effects result rest => Run (Fresh ': effects) result (Int -> rest) where
  run = fmap run . runFresh'

instance (Run effects [result] rest) => Run (NonDet ': effects) result rest where
  run = run . runNonDet (:[])

instance Run effects result rest => Run (Reader b ': effects) result (b -> rest) where
  run = fmap run . runReader

instance Run effects (Either (SomeExc exc) result) rest => Run (Resumable exc ': effects) result rest where
  run = run . Resumable.runError

instance Run effects (result, b) rest => Run (State b ': effects) result (b -> rest) where
  run = fmap run . runState

instance Run '[Trace] result (IO result) where
  run = runTrace

instance (Monoid w, Run effects (result, w) rest) => Run (Writer w ': effects) result rest where
  run = run . runWriter

instance Run '[IO] result (IO result) where
  run = Eff.runM

instance Run '[] result result where
  run = Eff.run
