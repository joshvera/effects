{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Monad.Effect.Embedded (
  Embedded(..),
  Raisable(..),
  embed,
  raiseEmbedded,
  liftEmbedded,
  runEmbedded,
  runEmbeddedAsync
) where

import Control.Concurrent.Async (async)
import Control.Monad
import Control.Monad.Effect.TH
import Control.Monad.Effect.Internal
import Control.Monad.IO.Class


data Embedded ms a where
  Embed :: Eff ms () -> Embedded ms ()

$(makeEff ''Embedded)

class Raisable (ms :: [* -> *]) r where
  raiseUnion :: Effectful m => Union ms a -> m r a

instance Raisable '[] r where
  raiseUnion _ = error "absurd: raiseUnion run on an empty union"

instance (Member e r, Raisable m r) =>  Raisable (e ': m) r where
  raiseUnion u =
    case decompose u of
      Right x -> send x
      Left u' -> raiseUnion u'

raiseEmbedded :: (Raisable e e', Effectful m) => m e a -> m e' a
raiseEmbedded = raiseHandler loop
  where
    loop (Val x)  = pure x
    loop (E u' q) = raiseUnion u' >>= (q >>> loop)

liftEmbedded :: (Raisable e e', Effectful m) => m (Embedded e ': e') a -> m e' a
liftEmbedded = raiseHandler (runEmbedded void)

runEmbedded :: (Raisable e e', Effectful m)
            => (forall v. m e' v -> m e'' ())
            -> m (Embedded e ': e'') a
            -> m e'' a
runEmbedded f = raiseHandler (relay pure (\(Embed e) -> (lowerEff (f (raiseEff (raiseEmbedded e))) >>=)))

runEmbeddedAsync :: (Raisable e e', Member IO e'', Effectful m)
                 => (forall v. m e' v -> IO v)
                 -> m (Embedded e ': e'') a
                 -> m e'' a
runEmbeddedAsync f = raiseHandler (runEmbedded (liftIO . void . async . f . raiseEff))
