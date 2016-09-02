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
throwError :: (Exc e :< effs) => e -> Eff effs a
throwError e = send (Exc e)

-- | Handler for exception effects
-- If there are no exceptions thrown, returns Right If exceptions are
-- thrown and not handled, returns Left, interrupting the execution of
-- any other effect handlers.
runError :: Eff (Exc e ': effs) a -> Eff effs (Either e a)
runError =
   handleRelay (return . Right) (\ (Exc e) _k -> return (Left e))

-- | A catcher for Exceptions. Handlers are allowed to rethrow
-- exceptions.
catchError :: (Exc e :< effs) =>
        Eff effs a -> (e -> Eff effs a) -> Eff effs a
catchError m handle = interpose return (\(Exc e) _k -> handle e) m
