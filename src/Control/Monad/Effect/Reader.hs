{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Control.Monad.Effect.Reader
Description : Reader effects for computations that carry an environment
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

Composable handler for Reader effects. Handy for encapsulating an
environment with immutable state for interpreters.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.Reader (
  Reader(..),

  ask,
  asks,
  runReader,
  local
  -- * Example 1: Simple Reader Usage
  -- $simpleReaderExample

  -- * Example 2: Modifying Reader Content With @local@
  -- $localExample

) where

import Control.Monad.Effect.Internal

-- |
data Reader v (m :: * -> *) a where
  Reader :: Reader a m a
  Local :: (v -> v) -> m a -> Reader v m a

-- | Request a value for the environment
ask :: (Member (Reader v) e, Effectful m) => m e v
ask = send Reader

-- | Request a value from the environment and applys as function
asks :: (Member (Reader v) e, Effectful m) => (v -> a) -> m e a
asks f = raiseEff (f <$> ask)

-- | Handler for reader effects
runReader :: (Effectful m, PureEffects e) => v -> m (Reader v ': e) a -> m e a
runReader = raiseHandler . go
  where go :: PureEffects e => v -> Eff (Reader v ': e) a -> Eff e a
        go _ (Return a)             = pure a
        go e (Effect Reader k)      = go e (k e)
        go e (Effect (Local f m) k) = go (f e) (m >>= k)
        go e (Other u k)            = liftHandler (go e) u k

-- |
-- Locally rebind the value in the dynamic environment
-- This function is like a relay; it is both an admin for Reader requests,
-- and a requestor of them
local :: forall v b m e. (Member (Reader v) e, Effectful m) =>
         (v -> v) -> m e b -> m e b
local f m = send (Local f (lowerEff m))


instance PureEffect (Reader r)
instance Effect (Reader r) where
  handleState c dist (Request Reader k) = Request Reader (dist . (<$ c) . k)
  handleState c dist (Request (Local f a) k) = Request (Local f (dist (a <$ c))) (dist . fmap k)


{- $simpleReaderExample

In this example the @Reader@ monad provides access to variable bindings.
Bindings are a @Map@ of integer variables.
The variable @count@ contains number of variables in the bindings.
You can see how to run a Reader effect and retrieve data from it
with 'runReader', how to access the Reader data with 'ask' and 'asks'.

>import Control.Monad.Effect
>import Control.Monad.Effect.Reader
>import Data.Map as Map
>import Data.Maybe
>
>type Bindings = Map String Int
>
>-- Returns True if the "count" variable contains correct bindings size.
>isCountCorrect :: Bindings -> Bool
>isCountCorrect bindings = run $ runReader bindings calc_isCountCorrect
>
>-- The Reader effect, which implements this complicated check.
>calc_isCountCorrect :: Eff '[Reader Bindings] Bool
>calc_isCountCorrect = do
>    count <- asks (lookupVar "count")
>    bindings <- (ask :: Eff '[Reader Bindings] Bindings)
>    return (count == (Map.size bindings))
>
>-- The selector function to  use with 'asks'.
>-- Returns value of the variable with specified name.
>lookupVar :: String -> Bindings -> Int
>lookupVar name bindings = fromJust (Map.lookup name bindings)
>
>sampleBindings :: Map.Map String Int
>sampleBindings = Map.fromList [("count",3), ("1",1), ("b",2)]
>
>main = do
>    putStr $ "Count is correct for bindings " ++ (show sampleBindings) ++ ": "
>    putStrLn $ show (isCountCorrect sampleBindings)
-}

{- $localExample

Shows how to modify Reader content with 'local'.

> import Control.Monad.Effect
> import Control.Monad.Effect.Reader
>
> import Data.Map as Map
> import Data.Maybe
>
> type Bindings = Map String Int
>
> calculateContentLen :: Eff '[Reader String] Int
> calculateContentLen = do
>     content <- (ask :: Eff '[Reader String] String)
>     return (length content)
>
> -- Calls calculateContentLen after adding a prefix to the Reader content.
> calculateModifiedContentLen :: Eff '[Reader String] Int
> calculateModifiedContentLen = local ("Prefix " ++) calculateContentLen
>
> main :: IO ()
> main = do
>     let s = "12345";
>     let modifiedLen = run $ runReader s calculateModifiedContentLen;
>     let len = run $ runReader s calculateContentLen ;
>     putStrLn $ "Modified 's' length: " ++ (show modifiedLen)
>     putStrLn $ "Original 's' length: " ++ (show len)
-}
