{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

{-|
Module      : Control.Monad.Effect.Trace
Description : Composable Trace effects
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

Composable handler for Trace effects. Trace allows one to debug the
operation of sequences of effects by outputing to the console.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.Trace
( Trace(..)
, trace
, runPrintingTrace
, runIgnoringTrace
, runReturningTrace
) where

import Control.Monad.Effect.Internal
import Control.Monad.Effect.State
import Control.Monad.IO.Class
import Data.Bifunctor (first)
import System.IO

-- | A Trace effect; takes a String and performs output
data Trace (m :: * -> *) v where
  Trace :: String -> Trace m ()

-- | Printing a string in a trace
trace :: (Member Trace e, Effectful m) => String -> m e ()
trace = send . Trace

-- | An IO handler for Trace effects. Prints output to stderr.
runPrintingTrace :: (Member (Lift IO) effects, Effectful m, Effect (Union effects)) => m (Trace ': effects) a -> m effects a
runPrintingTrace = raiseHandler (interpret (\ (Trace s) -> liftIO (liftIO (hPutStrLn stderr s))))

-- | Run a 'Trace' effect, discarding the traced values.
runIgnoringTrace :: (Effectful m, Effect (Union effects)) => m (Trace ': effects) a -> m effects a
runIgnoringTrace = raiseHandler go
  where go (Return a)           = pure a
        go (Effect (Trace _) k) = runIgnoringTrace (k ())
        go (Other u k)          = handle runIgnoringTrace u k

-- | Run a 'Trace' effect, accumulating the traced values into a list like a 'Writer'.
runReturningTrace :: (Effectful m, Effect (Union effects)) => m (Trace ': effects) a -> m effects ([String], a)
runReturningTrace = raiseHandler (fmap (first reverse) . runState [] . reinterpret (\ (Trace s) -> modify' (s:)))


instance Effect Trace where
  handleState c dist (Request (Trace s) k) = Request (Trace s) (dist . (<$ c) . k)
