{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

{-|
Module      : Control.Monad.Freer.Exception
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
module Control.Monad.Freer.Exception (
  Exc(..),
  throwError,
  runError,
  catchError
) where

import Control.Monad.Freer.Internal

--------------------------------------------------------------------------------
                           -- Exceptions --
--------------------------------------------------------------------------------
-- | Exceptions of the type e; no resumption
newtype Exc e v = Exc e

-- | Throws an error carrying information of type e
throwError :: (Exc exception :< e) => exception -> Eff e a
throwError e = send (Exc e)

-- | Handler for exception effects
-- If there are no exceptions thrown, returns Right If exceptions are
-- thrown and not handled, returns Left, interrupting the execution of
-- any other effect handlers.
runError :: Eff (Exc exception ': e) a -> Eff e (Either exception a)
runError =
   handleRelay (pure . Right) (\ (Exc e) _k -> pure (Left e))

-- | A catcher for Exceptions. Handlers are allowed to rethrow
-- exceptions.
catchError :: (Exc exception :< e) =>
        Eff e a -> (exception -> Eff e a) -> Eff e a
catchError m handle = interpose pure (\(Exc e) _k -> handle e) m
