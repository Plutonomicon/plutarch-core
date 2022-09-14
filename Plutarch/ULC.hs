{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

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
  pmatchImpl (ULCImpl t) f =
    Term . ULCImpl $ expr $ app
      (lam $ runImpl . unTerm $ f $ PPair
        (Term . ULCImpl $ fst' (var 0))
        (Term . ULCImpl $ snd' (var 0))
      )
      t

tru, fls :: ULambda
tru = expr $ lam $ lam $ var 0
fls = expr $ lam $ lam $ var 1

fst', snd' :: ULambda -> ULambda
fst' p = app p tru
snd' p = app p fls

instance PConstructable' ULCImpl (PEither a b) where
  pconImpl e = ULCImpl $ expr $ lam $ app (f (var 0)) t
    where
      (f, t) = case e of 
        PLeft (Term a) -> (fst', runImpl a)
        PRight (Term b) -> (snd', runImpl b)
  pmatchImpl (ULCImpl t) f =
    Term . ULCImpl $
      expr $ 
        t `app`
          (expr $ lam $ runImpl . unTerm . f . PLeft . Term . ULCImpl $ var 0) `app`
          (expr $ lam $ runImpl . unTerm . f . PRight . Term . ULCImpl $ var 0)

instance PConstructable' ULCImpl PUnit where
  pconImpl PUnit = ULCImpl $ expr $ lam $ var 0
  pmatchImpl _ f = f PUnit

instance PConstructable' ULCImpl (PLet a) where
  pconImpl (PLet t) = ULCImpl $ runImpl . unTerm $ t
  pmatchImpl (ULCImpl t) f = f $ PLet (Term (ULCImpl t))

instance PUntyped ULCImpl where
  punsafeCoerce (Term (ULCImpl t)) = Term (ULCImpl t)

instance PPartial ULCImpl where
  perror = Term (ULCImpl err)

class
  ( PLC edsl
  , PUntyped edsl
  , PPartial edsl
  , forall a b. PConstructable edsl (PPair a b)
  , PConstructable edsl PUnit
  , forall a b. PConstructable edsl (PEither a b)
  , forall a. PConstructable edsl (PLet a)
  ) => PULC edsl
instance PULC ULCImpl

compile' :: Term ULCImpl a -> ULC
compile' (Term term) = runULambda (runImpl term)

compile :: forall a. (forall edsl. PULC edsl => Term edsl a) -> ULC
compile t = compile' t
