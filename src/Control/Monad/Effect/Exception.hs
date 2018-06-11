{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, KindSignatures, TypeOperators #-}

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
module Control.Monad.Effect.Exception
( Exc(..)
, throwError
, runError
, catchError
, handleError
) where

import Control.Monad.Effect.Internal

--------------------------------------------------------------------------------
                           -- Exceptions --
--------------------------------------------------------------------------------
-- | Exceptions of the type 'exc'; no resumption
newtype Exc exc (m :: * -> *) a where
  Throw :: exc -> Exc exc m a

-- | Throws an error carrying information of type 'exc'.
throwError :: (Member (Exc exc) e, Effectful m) => exc -> m e a
throwError = send . Throw

-- | Handler for exception effects
-- If there are no exceptions thrown, returns Right If exceptions are
-- thrown and not handled, returns Left, interrupting the execution of
-- any other effect handlers.
runError :: (Effectful m, Effect (Union e)) => m (Exc exc ': e) a -> m e (Either exc a)
runError = raiseHandler go
  where go (Return a)           = pure (Right a)
        go (Effect (Throw e) _) = pure (Left e)
        go (Other r)            = fromRequest (handleState (Right ()) (either (pure . Left) runError) r)

-- | A catcher for Exceptions. Handlers are allowed to rethrow
-- exceptions.
catchError :: (Member (Exc exc) e, Effectful m) =>
        m e a -> (exc -> m e a) -> m e a
catchError = flip handleError

-- | 'catchError', but with its arguments in the opposite order. Useful
-- in situations where the code for the handler is shorter, or when
-- composing chains of handlers together.
handleError :: (Member (Exc exc) e, Effectful m) => (exc -> m e a) -> m e a -> m e a
handleError handler = raiseHandler (interpose pure (\(Throw e) _ -> lowerEff (handler e)))
