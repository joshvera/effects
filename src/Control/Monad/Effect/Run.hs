{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, FunctionalDependencies, TypeOperators, UndecidableInstances #-}
module Control.Monad.Effect.Run where

import Control.Monad.Effect.Coroutine
import Control.Monad.Effect.Internal as Eff

class Run effects result function | effects result -> function where
  run' :: Eff effects result -> function

instance Run effects result rest => Run (Yield a b ': effects) result ((a -> b) -> rest) where
  run' = fmap run' . runCoro

instance Run '[] result result where
  run' = Eff.run
