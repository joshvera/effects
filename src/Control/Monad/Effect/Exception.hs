{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

{-|
Module      : Control.Monad.Effect.Exception
Description : An Exception effect and handler.
Copyright   : Alej Cabrera 2015
License     : BSD-3
Maintainer  : cpp.cabrera@gmail.com
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
throwError :: (Exc exc :< e) => exc -> Eff e a
throwError e = send (Exc e)

-- | Handler for exception effects
-- If there are no exceptions thrown, returns Right If exceptions are
-- thrown and not handled, returns Left, interrupting the execution of
-- any other effect handlers.
runError :: Eff (Exc exc ': e) a -> Eff e (Either exc a)
runError =
   relay (pure . Right) (\ (Exc e) _k -> pure (Left e))

-- | A catcher for Exceptions. Handlers are allowed to rethrow
-- exceptions.
catchError :: (Exc exc :< e) =>
        Eff e a -> (exc -> Eff e a) -> Eff e a
catchError m handle = interpose pure (\(Exc e) _k -> handle e) m
