{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, KindSignatures, TypeApplications, TypeOperators #-}

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
data Exc exc (m :: * -> *) a where
  Throw :: exc -> Exc exc m a
  Catch :: m a -> (exc -> m a) -> Exc exc m a

-- | Throws an error carrying information of type 'exc'.
throwError :: (Member (Exc exc) e, Effectful m) => exc -> m e a
throwError = send . Throw

-- | Handler for exception effects
-- If there are no exceptions thrown, returns Right If exceptions are
-- thrown and not handled, returns Left, interrupting the execution of
-- any other effect handlers.
runError :: (Effectful m, Effects e) => m (Exc exc ': e) a -> m e (Either exc a)
runError = raiseHandler go
  where go (Return a)             = pure (Right a)
        go (Effect (Throw e) _)   = pure (Left e)
        go (Effect (Catch a h) k) = do
          a' <- runError a
          case a' of
            Left e    -> runError (h e >>= k)
            Right a'' -> runError (k a'')
        go (Other u k)            = liftStatefulHandler (Right ()) (either (pure . Left) runError) u k

-- | A catcher for Exceptions. Handlers are allowed to rethrow
-- exceptions.
catchError :: (Member (Exc exc) e, Effectful m) =>
        m e a -> (exc -> m e a) -> m e a
catchError a h = send (Catch (lowerEff a) (lowerEff . h))

-- | 'catchError', but with its arguments in the opposite order. Useful
-- in situations where the code for the handler is shorter, or when
-- composing chains of handlers together.
handleError :: (Member (Exc exc) e, Effectful m) => (exc -> m e a) -> m e a -> m e a
handleError = flip catchError


instance PureEffect (Exc exc)
instance Effect (Exc exc) where
  handleState c dist (Request (Throw exc) k) = Request (Throw exc) (dist . (<$ c) . k)
  handleState c dist (Request (Catch a h) k) = Request (Catch (dist (a <$ c)) (dist . (<$ c) . h)) (dist . fmap k)

-- | Lift an 'IO' action into 'Eff', catching and rethrowing any exceptions it throws into an 'Exc' effect.
-- If you need more granular control over the types of exceptions caught, use 'catchIO' and rethrow in the handler.
rethrowing :: ( Member (Exc Exc.SomeException) e
              , Member (Lift IO) e
              , Effectful m
              )
           => IO a
           -> m e a
rethrowing m = raiseEff (liftIO (Exc.try m) >>= either (throwError . Exc.toException @Exc.SomeException) pure)

-- | The semantics of @bracket before after handler@ are as follows:
-- * Exceptions in @before@ and @after@ are thrown in IO.
-- * @after@ is called on IO exceptions in @handler@, and then rethrown in IO.
-- * If @handler@ completes successfully, @after@ is called
-- Call 'catchIO' at the call site if you want to recover.
bracket :: ( Member (Lift IO) e
           , Effectful m
           , PureEffects e
           )
        => IO a
        -> (a -> IO b)
        -> (a -> m e c)
        -> m e c
bracket before after action = raiseEff $ do
  a <- liftIO before
  let cleanup = liftIO (after a)
  res <- interpose (\ (Lift m) -> liftIO (Exc.try m) >>= either (\ exc -> cleanup >> liftIO (Exc.throwIO @Exc.SomeException exc)) pure) (lowerEff (action a))
  res <$ cleanup
