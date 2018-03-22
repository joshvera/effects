{-# LANGUAGE TypeOperators, TypeApplications, ScopedTypeVariables, GADTs, FlexibleContexts, DataKinds #-}
module Control.Monad.Effect.Resumable (
    Resumable(..)
  , throwError
  , runError
  , resumeError
  , catchError
  ) where

import Control.Monad.Effect.Internal

data Resumable exc v a where
   Resumable :: exc -> Resumable exc v v

throwError :: forall exc v e. (Resumable exc v :< e) => exc -> Eff e v
throwError e = send (Resumable e :: Resumable exc v v)

runError :: Eff (Resumable exc v ': e) a -> Eff e (Either exc a)
runError = relay (pure . Right) (\ (Resumable e) _k -> pure (Left e))

resumeError :: forall v exc e a. (Resumable exc v :< e) =>
        Eff e a -> (Arrow e v a -> exc -> Eff e a) -> Eff e a
resumeError m handle = interpose @(Resumable exc v) pure (\(Resumable e) yield -> handle yield e) m

catchError :: forall v exc e proxy a. (Resumable exc v :< e) =>
        proxy v -> Eff e a -> (exc -> Eff e a) -> Eff e a
catchError _ m handle = resumeError @v m (const handle)


