{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, FunctionalDependencies, GADTs, TypeOperators, UndecidableInstances #-}
module Control.Monad.Effect.Run where

import Control.Monad.Effect.Coroutine
import Control.Monad.Effect.Embedded
import Control.Monad.Effect.Exception
import Control.Monad.Effect.Internal as Eff

class Run effects result function | effects result -> function where
  run' :: Eff effects result -> function

instance Run effects result rest => Run (Yield a b ': effects) result ((a -> b) -> rest) where
  run' = fmap run' . runCoro

instance Run effects result rest => Run (Embedded effects ': effects) result rest where
  run' = run' . relay pure (\ (Embed e) k -> e >>= k)

instance Run effects (Either exc result) rest => Run (Exc exc ': effects) result rest where
  run' = run' . runError

instance Run '[] result result where
  run' = Eff.run
