{-# LANGUAGE AllowAmbiguousTypes, DataKinds, FlexibleContexts, FlexibleInstances, FunctionalDependencies, GADTs,
             KindSignatures, MultiParamTypeClasses, ScopedTypeVariables, TypeApplications, TypeOperators #-}

module Control.Monad.Effect.Update
  ( Right (..)
  , Update (..)
  , runUpdate
  , update
  , query
  , testcase
  ) where

import Control.Monad.Effect.Internal
import Data.Monoid
import Data.Proxy

-- Based on Ed's article: <https://www.schoolofhaskell.com/user/edwardk/heap-of-successes>

-- The right monoidal action on a set 's'.
-- Laws:
-- > act s mempty = s
-- > act s (mappend m n) = act (act s m) n
class Monoid p => Right s p where
  act :: s -> p -> s

instance Right s (Endo s) where act s (Endo f) = f s
instance Num s => Right s (Sum s) where act n (Sum s) = s + n

-- The update monad is a generalization of State, Writer, and Reader.
-- Rather than allowing a replacement of the state, we allow
-- a monoidal-right-action 'update'.
-- By picking @Right s (Last s)@ for the action, we recover State;
-- by picking @Right () s@, we recover Writer, and @Right () s@
-- gives us Reader.
data Update s p (m :: * -> *) v where
  -- WART #1: I was not able to elide this Proxy, though it can be hidden
  -- by the 'update' client function.
  Apply :: Right s p => Proxy s -> p -> Update s p m ()
  Query :: Update s p m s

runUpdate :: forall m e p s a . (Effectful m, Effects e, Right s p) => s -> m (Update s p ': e) a -> m e (p, a)
runUpdate = raiseHandler . go where
    go :: s -> Eff (Update s p : e) a -> Eff e (p, a)
    go s (Effect (Apply _ x) k) = runUpdate (act s x) (k ())
    go s (Effect Query k)       = runUpdate s (k s)
    go _ (Return a)             = pure (mempty, a)
    go s (Other u k)            = liftStatefulHandler (mempty, ()) (\(v, w) -> runUpdate (act s v) w) u k
                                  -- WART #2: I have _no_ idea whether the above invocation is correct.

-- WART #3 (the worst): I wasn't able to get this to typecheck without AllowAmbiguousTypes.
-- Without it, GHC can't pick the correct @s@ type to update, even with the proxy present
-- in the Apply constructor.
update :: forall s p e m . (Member (Update s p) e, Effectful m, Right s p) => p -> m e ()
update x = send (Apply (Proxy @s) x)

query :: forall s p e m . (Member (Update s p) e, Effectful m) => m e s
query = send (Query @s @p)

testcase :: Int
testcase = snd . run @Eff $ runUpdate (0 :: Int) do
  -- WART #4 (possibly unfixable): look at all these dang type applications. I kinda hate em
  update @Int @(Sum Int) (Sum 5)
  update @Int @(Sum Int) (Sum 10)
  query @Int @(Sum Int)
  --update (Sum (0 :: Int))
