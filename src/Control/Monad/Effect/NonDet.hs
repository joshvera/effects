{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, TypeApplications, TypeOperators, UndecidableInstances #-}

{-|
Module      : Control.Monad.Effect.NonDet
Description : Nondeterministic Choice effects
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX
-}


module Control.Monad.Effect.NonDet (
  NonDet(..),
  runNonDetM,
  gatherM,
  gather,
  runNonDetA,
  runNonDet,
  msplit
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Effect.Internal
import Data.Foldable (asum)

--------------------------------------------------------------------------------
                    -- Nondeterministic Choice --
--------------------------------------------------------------------------------

runNonDetM :: (Monoid b, Effectful m, Effects e)
           => (a -> b)
           -> m (NonDet ': e) a
           -> m e b
runNonDetM unit = raiseHandler (fmap (foldMap unit) . runNonDet)

gatherM :: (Monoid b, Member NonDet e, Effectful m, Effects e)
        => (a -> b) -- ^ A function constructing a 'Monoid'al value from a single computed result. This might typically be @unit@ (for @Reducer@s), 'pure' (for 'Applicative's), or some similar singleton constructor.
        -> m e a    -- ^ The computation to run locally-nondeterministically.
        -> m e b
gatherM unit = raiseHandler (fmap (foldMap unit) . gather)

gather :: (Member NonDet e, Effectful m, Effects e)
       => m e a
       -> m e [a]
gather = raiseHandler go
  where go (Return a) = pure [a]
        go (E u q) = case prj u of
          Just MZero -> pure []
          Just MPlus -> liftA2 (++) (gather (apply q True)) (gather (apply q False))
          Nothing    -> liftStatefulHandler [()] (fmap join . traverse gather) u (apply q)

-- | A handler for nondeterminstic effects
runNonDetA :: (Alternative f, Effectful m, Effects e)
           => m (NonDet ': e) a
           -> m e (f a)
runNonDetA = raiseHandler (fmap (asum . map pure) . runNonDet)

-- | A handler for nondeterminstic effects
runNonDet :: (Effectful m, Effects e)
           => m (NonDet ': e) a
           -> m e [a]
runNonDet = raiseHandler go
  where go (Return a)       = pure [a]
        go (Effect MZero _) = pure []
        go (Effect MPlus k) = liftA2 (++) (runNonDet (k True)) (runNonDet (k False))
        go (Other u k)      = liftStatefulHandler [()] (fmap join . traverse runNonDet) u k

-- FIXME: It would probably be more efficient to define these in terms of a binary tree rather than a list.

msplit :: (Member NonDet e, Effectful m)
       => m e a -> m e (Maybe (a, m e a))
msplit = raiseHandler (fmap (fmap (fmap raiseEff)) . loop [])
  where loop jq (Return x) = pure (Just (x, msum jq))
        loop jq (E u q) =
          case prj u of
            Just MZero ->
              case jq of
                []      -> pure Nothing
                (j:jq') -> loop jq' j
            Just MPlus  -> loop (q `apply` False : jq) (q `apply` True)
            Nothing     -> E u (tsingleton (Arrow k))
              where k = q >>> loop jq
