{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

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
  , Effectful(..)
  , raiseHandler
  -- * Decomposing Unions
  , Member
  -- | Inserts multiple effects into 'E'.
  , inj
  , prj
  -- * Constructing and Decomposing Queues of Effects
  , decompose
  , Queue
  , tsingleton
  , Arrow
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
  , reinterpret2
) where

import Control.Applicative (Alternative(..))
import Control.Monad
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

data Eff2 effects scopes a
  = Pure a
  | forall b . Eff (Union effects b) (Queue2 effects scopes b a)
  | forall b . Scope (Union scopes b) (HQueue2 effects scopes b a)

type Queue2 effects scopes = FTCQueue (Eff2 effects scopes)
type HQueue2 effects scopes = FTCQueue (H (Eff2 effects scopes))

instance Functor (Eff2 effects scopes) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Eff u q) = Eff u (q |> (Pure . f))
  fmap f (Scope u q) = Scope u (q |> (pure . f))

instance Applicative (Eff2 effects scopes) where
  pure = Pure
  {-# INLINE pure #-}

  Pure f <*> Pure x = Pure $ f x
  Pure f <*> m = fmap f m
  Eff u q <*> m     = Eff u (q |> (`fmap` m))
  Scope u q <*> m = Scope u (q |> (H . pure . (`fmap` m)))
  {-# INLINE (<*>) #-}

instance Monad (Eff2 effects scopes) where
  return = Pure
  {-# INLINE return #-}

  Pure x >>= k = k x
  Eff u q >>= k = Eff u (q |> k)
  Scope u q >>= k = Scope u (q |> (H . pure . k))
  {-# INLINE (>>=) #-}

newtype H m a = H { runH :: m (m a) }
  deriving (Functor)

instance Applicative m => Applicative (H m) where
  pure = H . pure . pure
  H f <*> H a = H ((<*>) <$> f <*> a)

instance Monad m => Monad (H m) where
  H m >>= f = H (m >>= (>>= runH . f))


data Choice a where
  No :: Choice a
  Or :: Choice Bool

newtype Once a = Once a

instance Functor Once where
  fmap f (Once a) = Once (f a)

once :: (Member Choice effs, Member Once scopes) => Eff2 effs scopes a -> Eff2 effs scopes a
once = scope . Once

data Ask r a where
  Ask :: Ask r r

data Local r a where
  Local :: (r -> r) -> a -> Local r a

ask :: Member (Ask r) effects => Eff2 effects scopes r
ask = send2 Ask

local :: Member (Local r) scopes => (r -> r) -> Eff2 effects scopes a -> Eff2 effects scopes a
local f = scope . Local f

instance Member Choice effects => Alternative (Eff2 effects scopes) where
  empty = send2 No
  a <|> b = send2 Or >>= \ c -> if c then a else b

send2 :: Member eff e => eff b -> Eff2 e s b
send2 t = Eff (inj t) (tsingleton Pure)

scope :: Member eff s => eff (Eff2 e s b) -> Eff2 e s b
scope t = Scope (inj t) (tsingleton (H . pure))


apply2 :: Queue2 effects scopes a b -> a -> Eff2 effects scopes b
apply2 q' x =
   case tviewl q' of
   TOne k  -> k x
   k :< t -> case k x of
     Pure y -> t `apply2` y
     Eff u q -> Eff u (q >< t)
     Scope u q -> Scope u (q >< tsingleton (H . pure . (t `apply2`)))

-- | Compose queues left to right.
(>>>>) :: Queue2 effects scopes a b
      -> (Eff2 effects scopes b -> Eff2 effects' scopes c) -- ^ An function to compose.
      -> (a -> Eff2 effects' scopes c)
(>>>>) queue f = f . apply2 queue

run2 :: Eff2 '[] '[] b -> b
run2 m = case m of
  Pure x -> x
  _     -> error "Internal:run - This (E) should never happen"

data EffAlg eff effects a b = EffAlg
  { whenPure   :: a -> b
  , whenImpure :: forall v . eff v -> (v -> Eff effects b) -> Eff effects b }

data Nat = Z | S Nat

-- data Alg eff effects scope scopes a b = Alg
--   { handle  :: forall (n :: Nat) v . eff   v -> (v -> Eff2 effects scopes (b    n))  -> b n
--   , demote  :: forall (n :: Nat) v . scope v -> (v -> Eff2 effects scopes (b (S n))) -> b n
--   , promote :: forall (n :: Nat)   .        a    n   -> b (S n)
--   }

relay2 :: Functor scope
       => (a -> Eff2 effects scopes b)
       -> (forall v . eff v -> (v -> Eff2 effects scopes b) -> Eff2 effects scopes b)
       -> (forall v . scope v -> (v -> Eff2 effects scopes (Eff2 effects scopes v)) -> Eff2 effects scopes v)
       -> (forall v . Eff2 effects scopes v -> (v -> Eff2 effects scopes b) -> Eff2 effects scopes (Eff2 effects scopes b))
       -> Eff2 (eff ': effects) (scope : scopes) a
       -> Eff2         effects           scopes  b
relay2 pure' bind demote promote = loop
 where
  loop (Pure x)  = pure' x
  loop (Eff u' q) = case decompose u' of
    Right x -> bind x k
    Left  u -> Eff u (tsingleton k)
    where k = q >>>> loop
  loop (Scope u' q) = case decompose u' of
    Right x -> demote x k
    where k = q >>>> loop

-- | A queue of effects to apply from 'a' to 'b'.
type Queue effects a b = FTCQueue (Eff effects) a b

-- | An effectful function from 'a' to 'b'
--   that also performs a list of 'effects'.
type Arrow m (effects :: [* -> *]) a b = a -> m effects b


-- | Types wrapping 'Eff' actions.
--
--   Most instances of 'Effectful' will be derived using @-XGeneralizedNewtypeDeriving@, with these ultimately bottoming out on the instance for 'Eff' (for which 'raise' and 'lower' are simply the identity). Because of this, types can be nested arbitrarily deeply and still call 'raiseEff'/'lowerEff' just once to get at the (ultimately) underlying 'Eff'.
class Effectful m where
  -- | Raise an action in 'Eff' into an action in @m@.
  raiseEff :: Eff effects a -> m   effects a
  -- | Lower an action in @m@ into an action in 'Eff'.
  lowerEff :: m   effects a -> Eff effects a

instance Effectful Eff where
  raiseEff = id
  lowerEff = id

-- | Raise a handler on 'Eff' to a handler on some 'Effectful' @m@.
raiseHandler :: Effectful m => (Eff effectsA a -> Eff effectsB b) -> m effectsA a -> m effectsB b
raiseHandler handler = raiseEff . handler . lowerEff
{-# INLINE raiseHandler #-}


-- * Composing and Applying Effects

-- | Returns an effect by applying a given value to a queue of effects.
apply :: Queue effects a b -> a -> Eff effects b
apply q' x =
   case tviewl q' of
   TOne k  -> k x
   k :< t -> case k x of
     Val y -> t `apply` y
     E u q -> E u (q >< t)

-- | Compose queues left to right.
(>>>) :: Queue effects a b
      -> (Eff effects b -> Eff effects' c) -- ^ An function to compose.
      -> Arrow Eff effects' a c
(>>>) queue f = f . apply queue

-- | Compose queues right to left.
(<<<) :: (Eff effects b -> Eff effects' c) -- ^ An function to compose.
      -> Queue effects  a b
      -> Arrow Eff effects' a c
(<<<) f queue  = f . apply queue

-- * Sending and Running Effects

-- | Send a effect and wait for a reply.
send :: (Effectful m, Member eff e) => eff b -> m e b
send t = raiseEff (E (inj t) (tsingleton Val))

-- | Runs an effect whose effects has been consumed.
--
-- Typically composed as follows:
--
-- @
-- run . runEff1 eff1Arg . runEff2 eff2Arg1 eff2Arg2 (program)
-- @
run :: Effectful m => m '[] b -> b
run m = case lowerEff m of
  Val x -> x
  _     -> error "Internal:run - This (E) should never happen"
-- the other case is unreachable since Union [] a cannot be
-- constructed. Therefore, run is a total function if its argument
-- terminates.

-- | Runs an effect for which all but one Monad effect has been consumed,
-- and returns an 'm a'.
--
-- This is useful for plugging in traditional transformer stacks.
runM :: (Effectful m, Monad m1) => m '[m1] a -> m1 a
runM m = case lowerEff m of
  Val x -> pure x
  E u q -> case decompose u of
    Right m' -> m' >>= runM . apply q
    Left _   -> error "Internal:runM - This (Left) should never happen"

-- | Given an effect request, either handle it with the given 'pure' function,
-- or relay it to the given 'bind' function.
relay :: Effectful m
      => Arrow m e a b -- ^ An 'pure' effectful arrow.
      -- | A function to relay to, that binds a relayed 'eff v' to
      -- an effectful arrow and returns a new effect.
      -> (forall v. eff v -> Arrow m e v b -> m e b)
      -> m (eff ': e) a -- ^ The 'eff' to relay and consume.
      -> m e b -- ^ The relayed effect with 'eff' consumed.
relay pure' bind = raiseHandler loop
 where
  loop (Val x)  = lowerEff (pure' x)
  loop (E u' q) = case decompose u' of
    Right x -> lowerEff (bind x (raiseEff . k))
    Left  u -> E u (tsingleton k)
   where k = q >>> loop

-- | Parameterized 'relay'
-- Allows sending along some state to be handled for the target
-- effect, or relayed to a handler that can handle the target effect.
relayState :: Effectful m
           => s
           -> (s -> a -> m e b)
           -> (forall v. s -> eff v -> (s -> Arrow m e v b) -> m e b)
           -> m (eff ': e) a
           -> m e b
relayState s' pure' bind = raiseHandler (loop s')
  where
    loop s (Val x)  = lowerEff (pure' s x)
    loop s (E u' q) = case decompose u' of
      Right x -> lowerEff (bind s x (fmap raiseEff . k))
      Left  u -> E u (tsingleton (k s))
     where k s'' = q >>> loop s''

-- | Intercept the request and possibly reply to it, but leave it
-- unhandled
interpose :: (Member eff e, Effectful m)
          => Arrow m e a b
          -> (forall v. eff v -> Arrow m e v b -> m e b)
          -> m e a -> m e b
interpose pure' h = raiseHandler loop
 where
   loop (Val x) = lowerEff (pure' x)
   loop (E u q) = case prj u of
     Just x -> lowerEff (h x (raiseEff . k))
     _      -> E u (tsingleton k)
    where k = q >>> loop

-- | Intercept an effect like 'interpose', but with an explicit state
-- parameter like 'relayState'.
interposeState :: (Member eff e, Effectful m)
               => s
               -> (s -> Arrow m e a b)
               -> (forall v. s -> eff v -> (s -> Arrow m e v b) -> m e b)
               -> m e a
               -> m e b
interposeState initial pure' handler = raiseHandler (loop initial)
  where
    loop state (Val x) = lowerEff (pure' state x)
    loop state (E u q) = case prj u of
      Just x -> lowerEff (handler state x (fmap raiseEff . k))
      _      -> E u (tsingleton (k state))
      where k state' = q >>> loop state'

-- | Handle the topmost effect by interpreting it into the underlying effects.
interpret :: Effectful m => (forall a. eff a -> m effs a) -> m (eff ': effs) b -> m effs b
interpret handler = raiseHandler (relay pure (\ eff yield -> lowerEff (handler eff) >>= yield))

-- | Interpret an effect by replacing it with another effect.
reinterpret :: Effectful m
            => (forall x. effect x -> m (newEffect ': effs) x)
            -> m (effect ': effs) a
            -> m (newEffect ': effs) a
reinterpret handle = raiseHandler loop
  where loop (Val x)  = pure x
        loop (E u' q) = case decompose u' of
            Right eff -> lowerEff (handle eff) >>= q >>> loop
            Left  u   -> E (weaken u) (tsingleton (q >>> loop))

-- | Interpret an effect by replacing it with two new effects.
reinterpret2 :: Effectful m
             => (forall x. effect x -> m (newEffect1 ': newEffect2 ': effs) x)
             -> m (effect ': effs) a
             -> m (newEffect1 ': newEffect2 ': effs) a
reinterpret2 handle = raiseHandler loop
  where loop (Val x)  = pure x
        loop (E u' q) = case decompose u' of
            Right eff -> lowerEff (handle eff) >>= q >>> loop
            Left  u   -> E (weaken (weaken u)) (tsingleton (q >>> loop))


-- * Effect Instances

instance Functor (Eff e) where
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f))
  {-# INLINE fmap #-}

instance Applicative (Eff e) where
  pure = Val
  {-# INLINE pure #-}

  Val f <*> Val x = Val $ f x
  Val f <*> E u q = E u (q |> (Val . f))
  E u q <*> m     = E u (q |> (`fmap` m))
  {-# INLINE (<*>) #-}

instance Monad (Eff e) where
  return = Val
  {-# INLINE return #-}

  Val x >>= k = k x
  E u q >>= k = E u (q |> k)
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
