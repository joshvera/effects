module Fresh where

import Control.Monad.Effect
import Control.Monad.Effect.Fresh
import Control.Monad.Effect.Trace

traceFresh :: IO ()
traceFresh = runM . runTrace . runFresh 0 $ do
  n <- fresh
  trace $ "Fresh " ++ show n
  n' <- fresh
  trace $ "Fresh " ++ show n'
  n'' <- fresh
  trace $ "Fresh " ++ show n''
{-
Fresh 0
Fresh 1
-}
