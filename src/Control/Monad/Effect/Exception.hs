{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

{-|
Module      : Control.Monad.Effect.Exception
Description : An Exception effect and handler.
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

Composable handler for Exception effects. Communicates success/failure
via an Either type.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.Exception (
  Exc(..),
  throwError,
  runError,
  catchError
) where

import Control.Monad.Effect.Internal

--------------------------------------------------------------------------------
                           -- Exceptions --
--------------------------------------------------------------------------------
-- | Exceptions of the type 'exc'; no resumption
newtype Exc exc a = Exc exc

-- | Throws an error carrying information of type 'exc'.
throwError :: (Member (Exc exc) e, Effectful m) => exc -> m e a
throwError e = send (Exc e)

-- | Handler for exception effects
-- If there are no exceptions thrown, returns Right If exceptions are
-- thrown and not handled, returns Left, interrupting the execution of
-- any other effect handlers.
runError :: Effectful m => m (Exc exc ': e) a -> m e (Either exc a)
runError =
   raiseHandler (relay (pure . Right) (\ (Exc e) _ -> pure (Left e)))

-- | A catcher for Exceptions. Handlers are allowed to rethrow
-- exceptions.
catchError :: (Member (Exc exc) e, Effectful m) =>
        m e a -> (exc -> m e a) -> m e a
catchError m handle = raiseHandler (interpose pure (\(Exc e) _k -> lowerEff (handle e))) m
