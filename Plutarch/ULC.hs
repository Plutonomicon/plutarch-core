{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.ULC (ULC (..), compile) where

import Control.Monad.Trans.Reader
import Control.Arrow ( Arrow(second) )

import Plutarch.Core
import Plutarch.PType

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

withTerm :: (Term ULCImpl a -> Term ULCImpl b) -> ULambda -> ULambda
withTerm f = runImpl . unTerm . f . Term . ULCImpl

runULambda :: ULambda -> ULC
runULambda r = runReader (unUL r) (0, 0)

newtype ULCImpl' (a :: PType) = ULCImpl { runImpl :: ULambda }

type ULCImpl = 'PDSLKind ULCImpl'

instance PDSL ULCImpl

instance PConstructable' ULCImpl (a #-> b) where
  pconImpl (PLam t) = ULCImpl $ expr $ lam $ withTerm t $ var 0
  pmatchImpl (ULCImpl t) f =
    f $ PLam \(Term (ULCImpl x)) -> Term . ULCImpl $ app t x

instance PConstructable' ULCImpl (PPair a b) where
  pconImpl (PPair (Term a) (Term b)) =
    ULCImpl $ expr $ lam $ var 0 `app` runImpl a `app` runImpl b
  pmatchImpl (ULCImpl t) f = f $ PPair (Term . ULCImpl $ fst' t) (Term . ULCImpl $ snd' t)
    where
      tru = expr $ lam $ lam $ var 0
      fls = expr $ lam $ lam $ var 1

      fst' p = app p tru
      snd' p = app p fls

instance PUntyped ULCImpl where
  punsafeCoerce (Term (ULCImpl t)) = Term (ULCImpl t)

instance PPartial ULCImpl where
  perror = Term (ULCImpl err)

class
  ( PLC edsl
  , PUntyped edsl
  , PPartial edsl
  , forall a b. PConstructable edsl (PPair a b)
  ) => PULC edsl
instance PULC ULCImpl

compile' :: Term ULCImpl a -> ULC
compile' (Term term) = runULambda (runImpl term)

compile :: forall a. (forall edsl. PULC edsl => Term edsl a) -> ULC
compile t = compile' t
