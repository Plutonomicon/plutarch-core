{-# LANGUAGE FlexibleInstances #-}

module Plutarch.ULC (ULC(..), ULambda, var, expr, lam, app, err, runULambda) where

import Control.Monad.Trans.Reader
import Control.Arrow ( Arrow(second) )

data ULC
  = App ULC ULC
  | Lam ULC
  | Var Int
  | Error

-- | Last 'Int' is the current level, first is the highest visible level, set by 'expr' 
newtype ULambda = ULambda { unUL :: Reader (Int, Int) ULC }

-- | The 'Int' passed to 'var' is the level counting the nearest 'expr' as the root
var :: Int -> ULambda
var i = ULambda $ Var . (+ i) . fst <$> ask

expr :: ULambda -> ULambda
expr = ULambda . local (\(_, i) -> (i, i)) . unUL

lam :: ULambda -> ULambda
lam = ULambda . fmap Lam . local (second (+ 1)) . unUL

app :: ULambda -> ULambda -> ULambda
app f a = ULambda $ App <$> unUL f <*> unUL a

err :: ULambda
err = ULambda $ pure Error

runULambda :: ULambda -> ULC
runULambda r = runReader (unUL r) (0, 0)
