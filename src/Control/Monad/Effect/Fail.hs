{-# LANGUAGE DataKinds, FlexibleContexts, TypeOperators, UndecidableInstances #-}
module Control.Monad.Effect.Fail
( Fail(..)
, runFail
, MonadFail(..)
) where

import Control.Monad.Effect.Internal
import Control.Monad.Fail

runFail :: Effectful m => m (Fail ': fs) a -> m fs (Either String a)
runFail = raiseHandler (relay (pure . Right) (const . pure . Left . failMessage))
