{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

{-|
Module      : Control.Monad.Effect.StateRW
Description : State effects in terms of Reader/Writer
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

Composable handler for State effects in terms of Reader/Writer
effects. This module is more a tutorial on how to compose handlers. It
is slightly slower than a dedicated State handler.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.StateRW () where

import Control.Monad.Effect.Reader
import Control.Monad.Effect.Writer
import Control.Monad.Effect.Internal

