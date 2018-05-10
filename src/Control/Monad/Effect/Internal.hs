{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- The following is needed to define MonadPlus instance. It is decidable
-- (there is no recursion!), but GHC cannot see that.
-- TODO: remove once GHC can deduce the decidability of this instance
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.Effect.Internal (
  -- * Constructing and Sending Effects
  Eff(..)
  , send
  , NonDet(..)
  , Fail(..)
  -- * Decomposing Unions
  , Member
  , Members
  -- | Inserts multiple effects into 'E'.
  , inj
  , prj
  -- * Constructing and Decomposing Queues of Effects
  , decompose
  , Queue
  , tsingleton
  , Arrow(..)
  , Union
  -- * Composing and Applying Effects
  , apply
  , (<<<)
  , (>>>)
  -- * Running Effects
  , run
  , runM
  -- * Relaying and Interposing Effects
  , relay
  , relayState
  , interpose
  , interposeState
  , interpret
  , reinterpret
) where

import Control.Applicative (Alternative(..))
import qualified Control.Arrow as Arr
import qualified Control.Category as Cat
import Control.Monad (MonadPlus(..), (<=<))
import Control.Monad.Fail (MonadFail(..))
import Control.Monad.IO.Class (MonadIO(..))
import Data.Union
import Data.FTCQueue

-- | An effectful computation that returns 'b' and sends a list of 'effects'.
data Eff effects b
  -- | Done with the value of type `b`.
  = Val b
  -- | Send an union of 'effects' and 'eff a' to handle, and a queues of effects to apply from 'a' to 'b'.
  | forall a. E (Union effects a) (Queue effects a b)

-- | A queue of effects to apply from 'a' to 'b'.
type Queue effects = FTCQueue (Arrow effects)

-- | An effectful function from 'a' to 'b'
--   that also performs a list of 'effects'.
newtype Arrow effects a b = Arrow { runArrow :: a -> Eff effects b }

instance Cat.Category (Arrow effects) where
  id = Arrow pure
  Arrow runB . Arrow runA = Arrow (runB <=< runA)

instance Arr.Arrow (Arrow effects) where
  arr f = Arrow (pure . f)
  Arrow runA *** Arrow runB = Arrow (\ (a, b) -> (,) <$> runA a <*> runB b)

-- * Composing and Applying Effects

-- | Returns an effect by applying a given value to a queue of effects.
apply :: Queue effects a b -> a -> Eff effects b
apply q' x =
   case tviewl q' of
   TAEmptyL -> pure x
   k :< t  -> case runArrow k x of
     Val y -> t `apply` y
     E u q -> E u (q >< t)

-- | Compose queues left to right.
(>>>) :: Queue effects a b
      -> (Eff effects b -> Eff effects' c) -- ^ An function to compose.
      -> Arrow effects' a c
(>>>) queue f = Arrow (f . apply queue)

-- | Compose queues right to left.
(<<<) :: (Eff effects b -> Eff effects' c) -- ^ An function to compose.
      -> Queue effects  a b
      -> Arrow effects' a c
(<<<) f queue  = Arrow (f . apply queue)

-- * Sending and Running Effects

-- | Send a effect and wait for a reply.
send :: Member eff e => eff b -> Eff e b
send t = E (inj t) (tsingleton (Arrow Val))

-- | Runs an effect whose effects has been consumed.
--
-- Typically composed as follows:
--
-- @
-- run . runEff1 eff1Arg . runEff2 eff2Arg1 eff2Arg2 (program)
-- @
run :: Eff '[] b -> b
run (Val x) = x
run _       = error "Internal:run - This (E) should never happen"
-- the other case is unreachable since Union [] a cannot be
-- constructed. Therefore, run is a total function if its argument
-- terminates.

-- | Runs an effect for which all but one Monad effect has been consumed,
-- and returns an 'm a'.
--
-- This is useful for plugging in traditional transformer stacks.
runM :: Monad m => Eff '[m] a -> m a
runM (Val x) = pure x
runM (E u q) = case decompose u of
  Right m -> m >>= runM . apply q
  Left _   -> error "Internal:runM - This (Left) should never happen"

-- | Given an effect request, either handle it with the given 'pure' function,
-- or relay it to the given 'bind' function.
relay :: (a -> Eff e b) -- ^ An 'pure' effectful arrow.
      -- | A function to relay to, that binds a relayed 'eff v' to
      -- an effectful arrow and returns a new effect.
      -> (forall v. eff v -> (v -> Eff e b) -> Eff e b)
      -> Eff (eff ': e) a -- ^ The 'eff' to relay and consume.
      -> Eff e b -- ^ The relayed effect with 'eff' consumed.
relay pure' bind = loop
 where
  loop (Val x)   = pure' x
  loop (E u' q)  = case decompose u' of
    Right x -> bind x (runArrow k)
    Left  u -> E u (tsingleton k)
   where k = q >>> loop

-- | Parameterized 'relay'
-- Allows sending along some state to be handled for the target
-- effect, or relayed to a handler that can handle the target effect.
relayState :: s
           -> (s -> a -> Eff e b)
           -> (forall v. s -> eff v -> (s -> v -> Eff e b) -> Eff e b)
           -> Eff (eff ': e) a
           -> Eff e b
relayState s' pure' bind = loop s'
  where
    loop s (Val x)  = pure' s x
    loop s (E u' q)  = case decompose u' of
      Right x -> bind s x (runArrow . k)
      Left  u -> E u (tsingleton (k s))
     where k s'' = q >>> loop s''

-- | Intercept the request and possibly reply to it, but leave it
-- unhandled
interpose :: Member eff e
          => (a -> Eff e b)
          -> (forall v. eff v -> (v -> Eff e b) -> Eff e b)
          -> Eff e a -> Eff e b
interpose ret h = loop
 where
   loop (Val x) = ret x
   loop (E u q) = case prj u of
     Just x -> h x (runArrow k)
     _      -> E u (tsingleton k)
    where k = q >>> loop

-- | Intercept an effect like 'interpose', but with an explicit state
-- parameter like 'relayState'.
interposeState :: Member eff e
               => s
               -> (s -> a -> Eff e b)
               -> (forall v. s -> eff v -> (s -> v -> Eff e b) -> Eff e b)
               -> Eff e a
               -> Eff e b
interposeState initial ret handler = loop initial
  where
    loop state (Val x) = ret state x
    loop state (E u q) = case prj u of
      Just x -> handler state x (runArrow . k)
      _      -> E u (tsingleton (k state))
      where k state' = q >>> loop state'

-- | Handle the topmost effect by interpreting it into the underlying effects.
interpret :: (forall a. eff a -> Eff effs a) -> Eff (eff ': effs) b -> Eff effs b
interpret f = relay pure (\ eff yield -> f eff >>= yield)

-- | Interpret an effect by replacing it with another effect.
reinterpret :: (forall x. effect x -> Eff (newEffect ': effs) x)
            -> Eff (effect ': effs) a
            -> Eff (newEffect ': effs) a
reinterpret handle = loop
  where loop (Val x)  = pure x
        loop (E u' q) = case decompose u' of
            Right eff -> handle eff >>=  runArrow (q >>> loop)
            Left  u   -> E (weaken u) (tsingleton (q >>> loop))


-- * Effect Instances

instance Functor (Eff e) where
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> Arrow (Val . f))
  {-# INLINE fmap #-}

instance Applicative (Eff e) where
  pure = Val
  {-# INLINE pure #-}

  Val f <*> Val x = Val $ f x
  Val f <*> E u q = E u (q |> Arrow (Val . f))
  E u q <*> m     = E u (q |> Arrow (`fmap` m))
  {-# INLINE (<*>) #-}

instance Monad (Eff e) where
  return = Val
  {-# INLINE return #-}

  Val x >>= k = k x
  E u q >>= k = E u (q |> Arrow k)
  {-# INLINE (>>=) #-}

instance Member IO e => MonadIO (Eff e) where
  liftIO = send
  {-# INLINE liftIO #-}


-- | A data type for representing nondeterminstic choice
data NonDet a where
  MZero :: NonDet a
  MPlus :: NonDet Bool

instance Member NonDet e => Alternative (Eff e) where
  empty = mzero
  (<|>) = mplus

instance Member NonDet a => MonadPlus (Eff a) where
  mzero       = send MZero
  mplus m1 m2 = send MPlus >>= \x -> if x then m1 else m2


-- | An effect representing failure.
newtype Fail a = Fail { failMessage :: String }

instance Member Fail fs => MonadFail (Eff fs) where
  fail = send . Fail
