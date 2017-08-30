{-# LANGUAGE DataKinds, TypeOperators #-}
module Control.Monad.Effect.Fail
( Fail
, runFail
) where

import Control.Monad.Effect
import Control.Monad.Effect.Internal

data Fail a = Fail { failMessage :: String }

runFail :: Eff (Fail ': fs) a -> Eff fs (Either String a)
runFail = relay (pure . Right) (const . pure . Left . failMessage)
