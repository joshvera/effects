{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

{-|
Module      : Control.Monad.Effect.Trace
Description : Composable Trace effects
Copyright   : Alej Cabrera 2015
License     : BSD-3
Maintainer  : cpp.cabrera@gmail.com
Stability   : experimental
Portability : POSIX

Composable handler for Trace effects. Trace allows one to debug the
operation of sequences of effects by outputing to the console.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.Trace (
  Trace,
  trace,
  runTrace
) where

import Control.Monad.Effect.Internal

-- | A Trace effect; takes a String and performs output
data Trace v where
  Trace :: String -> Trace ()

-- | Printing a string in a trace
trace :: (Trace :< e) => String -> Eff e ()
trace = send . Trace

-- | An IO handler for Trace effects
runTrace :: Eff '[Trace] a -> IO a
runTrace (Val x) = return x
runTrace (E u q) = case decompose u of
     Right (Trace s) -> putStrLn s >> runTrace (apply q ())
     Left _          -> error "runTrace:Left - This should never happen"
