{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

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
-- * User-defined exception handling
, throwError
, runError
, catchError
, handleError
-- * Handling impure/IO errors
, catchIO
, handleIO
, rethrowing
-- * Resource management
, bracket
) where

import qualified Control.Exception as Exc
import Control.Monad.IO.Class
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
catchError = flip handleError

-- | 'catchError', but with its arguments in the opposite order. Useful
-- in situations where the code for the handler is shorter, or when
-- composing chains of handlers together.
handleError :: (Member (Exc exc) e, Effectful m) => (exc -> m e a) -> m e a -> m e a
handleError handle = raiseHandler (interpose pure (\(Exc e) _ -> lowerEff (handle e)))

-- | Catch exceptions in 'IO' actions embedded in 'Eff', handling them with the passed function.
--
-- Note that while the type allows 'IO' to occur anywhere within the
-- effect list, it must actually occur at the end to be able to run
-- the computation.
catchIO :: ( Exc.Exception exc
           , Member IO e
           , Effectful m
           )
        => m e a
        -> (exc -> m e a)
        -> m e a
catchIO = flip handleIO

-- | As 'catchIO', but with its arguments in the opposite order.
handleIO :: ( Exc.Exception exc
            , Member IO e
            , Effectful m
            )
        => (exc -> m e a)
        -> m e a
        -> m e a
handleIO handler = raiseHandler (interpose pure (\ go yield -> send (Exc.try go) >>= either (lowerEff . handler) yield))

-- | Lift an 'IO' action into 'Eff', catching and rethrowing any exceptions it throws into an 'Exc' effect.
rethrowing :: ( Member (Exc Exc.SomeException) e
              , Member IO e
              , Effectful m
              , MonadIO (m e)
              )
           => IO a
           -> m e a
rethrowing m = catchIO (liftIO m) (throwError . Exc.toException @Exc.SomeException)

-- | The semantics of @bracket before after handler@ are as follows:
-- * Exceptions in @before@ and @after@ are thrown in IO.
-- * @after@ is called on IO exceptions in @handler@, and then rethrown in IO.
-- * If @handler@ completes successfully, @after@ is called
-- Call 'catchIO' at the call site if you want to recover.
bracket :: ( Member IO e
           , Effectful m
           , MonadIO (m e)
           )
        => IO a
        -> (a -> IO b)
        -> (a -> m e c)
        -> m e c
bracket before after action = do
  a <- liftIO before
  let cleanup = liftIO (after a)
  res <- action a `catchIO` (\e -> cleanup >> liftIO (Exc.throwIO @Exc.SomeException e))
  res <$ cleanup
