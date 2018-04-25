{-# LANGUAGE DataKinds, FlexibleContexts, TypeOperators, UndecidableInstances #-}
module Control.Monad.Effect.Fail
( Fail(..)
, runFail
, MonadFail(..)
) where

import Control.Monad.Effect.Internal

runFail :: Eff (Fail ': fs) a -> Eff fs (Either String a)
runFail = relay (pure . Right) (const . pure . Left . failMessage)
