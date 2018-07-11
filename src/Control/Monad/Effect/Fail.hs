{-# LANGUAGE DataKinds, FlexibleContexts, TypeOperators #-}
module Control.Monad.Effect.Fail
( Fail(..)
, runFail
, MonadFail(..)
) where

import Control.Monad.Effect.Internal
import Control.Monad.Fail

runFail :: (Effectful m, Effect (Union effs)) => m (Fail ': effs) a -> m effs (Either String a)
runFail = raiseHandler go
  where go (Return a)          = pure (Right a)
        go (Effect (Fail s) _) = pure (Left s)
        go (Other u k)         = liftStatefulHandler (Right ()) (\act yield -> either (pure . Left) (runFail . (>>= yield)) act) u k
