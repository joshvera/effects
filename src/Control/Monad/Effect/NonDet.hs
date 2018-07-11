{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, TypeApplications, TypeOperators, UndecidableInstances, DeriveFunctor #-}

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
        => (a -> b) -- ^ A function constructing a 'Monoid'al value from a single computed result. This might typically be @unit@ (for @Reducer@s), 'pure' (.hs 'Applicative's), or some similar singleton constructor.
        -> m e a    -- ^ The computation to run locally-nondeterministically.
        -> m e b
gatherM unit = raiseHandler (fmap (foldMap unit) . gather)

gather :: (Member NonDet e, Effectful m, Effects e)
       => m e a
       -> m e [a]
gather = raiseHandler (fmap fst . go [])
  where go state (Return a) = pure (a : state, Just a)
        go state (E u q) = case prj u of
          Just MZero -> pure (state, Nothing)
          Just MPlus -> do
            (xs, a) <- (go state (apply q True))
            (ys, b) <- (go state (apply q False))
            pure (xs ++ ys, a <|> b)
          Nothing    -> runNonDetPair <$> liftStatefulHandler (NonDetPair (state, Just ())) (\(NonDetPair (state', act)) yield -> maybe (pure $ NonDetPair (state', Nothing)) (fmap NonDetPair . go state' . (>>= yield)) act) u (apply q)

-- | A handler for nondeterminstic effects
runNonDetA :: (Alternative f, Effectful m, Effects e)
           => m (NonDet ': e) a
           -> m e (f a)
runNonDetA = raiseHandler (fmap (asum . map pure) . runNonDet)

-- | A handler for nondeterminstic effects
runNonDet :: (Effectful m, Effects e)
           => m (NonDet ': e) a
           -> m e [a]
runNonDet = raiseHandler (fmap fst . go [])
  where go state (Return a)       = pure (a : state, Just a)
        go state (Effect MZero k) = pure (state, Nothing)
        go state (Effect MPlus k) = do
          (xs, a) <- (go state (k True))
          (ys, b) <- (go state (k False))
          pure (xs ++ ys, a <|> b)
        go state (Other u k)      = runNonDetPair <$> liftStatefulHandler (NonDetPair (state, Just ())) (\(NonDetPair (state', act)) yield -> maybe (pure $ NonDetPair (state', Nothing)) (fmap NonDetPair . go state' . (>>= yield)) act) u k

newtype NonDetPair a x = NonDetPair { runNonDetPair :: ([a], Maybe x) }
  deriving (Functor)

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
            Nothing     -> E u (tsingleton k)
              where k = q >>> loop jq
