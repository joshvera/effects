{-# LANGUAGE DataKinds, FlexibleContexts, TypeOperators, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Control.Monad.Effect.Fail
( Fail
, runFail
) where

import Control.Monad.Effect
import Control.Monad.Effect.Internal
import Control.Monad.Fail

data Fail a = Fail { failMessage :: String }

runFail :: Eff (Fail ': fs) a -> Eff fs (Either String a)
runFail = relay (pure . Right) (const . pure . Left . failMessage)


instance Fail :< fs => MonadFail (Eff fs) where
  fail = send . Fail
