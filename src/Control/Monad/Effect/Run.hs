{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, FunctionalDependencies, TypeOperators, UndecidableInstances #-}
module Control.Monad.Effect.Run where

import Control.Monad.Effect.Internal as Eff

class Run effects result function | effects result -> function where
  run' :: Eff effects result -> function
