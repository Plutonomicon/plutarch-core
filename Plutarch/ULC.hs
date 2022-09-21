{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Plutarch.ULC (ULC, ULCImpl,
 compileAp, compile) where

import Data.Proxy

import Plutarch.Core
import Plutarch.PType
import Data.Functor.Compose
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class
import GHC.Stack

data ULC
  = App ULC ULC
  | Lam ULC
  | Var Int
  | Error

-- | Last 'Int' is the current level, first is the highest visible level, set by 'expr' 
newtype ULambda m = ULambda { unUL :: Compose ((->) (Int, Int)) m ULC }

-- | The 'Int' passed to 'var' is the level counting the nearest 'expr' as the root
var :: (Applicative m) => Int -> ULambda m
var i = ULambda $ Var . (+ i) . fst <$> Compose pure

expr :: ULambda m -> ULambda m
expr = ULambda . Compose . (\f (_, lvl) -> f (lvl, lvl)) . getCompose . unUL

lam :: (Functor m) => ULambda m -> ULambda m
-- lam = ULambda . fmap Lam . local (second (+ 1)) . unUL
lam = ULambda . Compose . (\f (top, lvl) -> Lam <$> f (top, lvl + 1)) . getCompose . unUL

app :: (Applicative m) => ULambda m -> ULambda m -> ULambda m
app f a = ULambda $ App <$> unUL f <*> unUL a

err :: (Applicative m) =>  ULambda m
err = ULambda $ pure Error

withTerm :: (Term (ULCImpl m) a -> Term (ULCImpl m) b) -> ULambda m -> ULambda m
withTerm f = runImpl . unTerm . f . Term . ULCImpl

runULambda :: ULambda m -> m ULC
runULambda r = getCompose (unUL r) (0, 0)

newtype ULCImpl' m (a :: PType) = ULCImpl { runImpl :: ULambda m }

type ULCImpl m = 'PDSLKind (ULCImpl' m)

instance PDSL (ULCImpl m)

instance (Applicative m) => PConstructable' (ULCImpl m) (a #-> b) where
  pconImpl (PLam t) = ULCImpl $ expr $ lam $ withTerm t $ var 0
  pmatchImpl (ULCImpl t) f =
    f $ PLam \(Term (ULCImpl x)) -> Term . ULCImpl $ app t x

instance (Applicative m) => PConstructable' (ULCImpl m) (PPair a b) where
  pconImpl (PPair (Term a) (Term b)) =
    ULCImpl $ expr $ lam $ var 0 `app` runImpl a `app` runImpl b
  pmatchImpl (ULCImpl t) f =
    Term . ULCImpl $ expr $ app
      (lam $ runImpl . unTerm $ f $ PPair
        (Term . ULCImpl $ fst' (var 0))
        (Term . ULCImpl $ snd' (var 0))
      )
      t

tru, fls :: (Applicative m) => ULambda m
tru = expr $ lam $ lam $ var 0
fls = expr $ lam $ lam $ var 1

fst', snd' :: (Applicative m) => ULambda m -> ULambda m
fst' p = app p tru
snd' p = app p fls

instance (Applicative m) => PConstructable' (ULCImpl m) (PEither a b) where
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

instance (Applicative m) => PConstructable' (ULCImpl m) PUnit where
  pconImpl PUnit = ULCImpl $ expr $ lam $ var 0
  pmatchImpl _ f = f PUnit

instance (Applicative m) => PConstructable' (ULCImpl m) (PLet a) where
  pconImpl (PLet t) = ULCImpl $ app (expr $ lam $ var 0) (runImpl . unTerm $ t)
  pmatchImpl (ULCImpl t) f = f $ PLet (Term . ULCImpl $ t)

instance PConstructable' (ULCImpl m) (PFix a) where
  pconImpl (PFix t) = unsafeCoerceULC . unTerm $ t
  pmatchImpl t f = f . PFix . Term . unsafeCoerceULC $ t

-- instance PConstructable' (ULCImpl m) (PForall f) where
--   pconImpl (PForall t) = unsafeCoerceULC . unTerm $ t
--   pmatchImpl t f = f . PForall . Term . unsafeCoerceULC $ t

-- instance PConstructable' (ULCImpl m) (PSome f) where
--   pconImpl (PSome t) = unsafeCoerceULC . unTerm $ t
--   pmatchImpl t f = f . PSome . Term . unsafeCoerceULC $ t

instance PConstructable' (ULCImpl m) PAny where
  pconImpl (PAny _ t) = unsafeCoerceULC . unTerm $ t
  pmatchImpl t f = f . PAny Proxy . Term . unsafeCoerceULC $ t

unsafeCoerceULC :: ULCImpl' m a -> ULCImpl' m b
unsafeCoerceULC = ULCImpl . runImpl

instance PUntyped (ULCImpl m) where
  punsafeCoerce = Term . unsafeCoerceULC . unTerm

instance (Applicative m) => PPartial (ULCImpl m) where
  perror = Term (ULCImpl err)

instance (Applicative m) =>  PAp m (ULCImpl m) where
  papr x y = Term . ULCImpl . ULambda $ Compose (const x) *> (unUL . runImpl . unTerm) y
  papl x y = Term . ULCImpl . ULambda $ (unUL . runImpl . unTerm) x <* Compose (const y)

instance (Monad m) => PEmbeds m (ULCImpl m) where
  pembed t =
    Term . ULCImpl . ULambda . Compose . runReaderT $
      lift t >>=
        ReaderT . getCompose . unUL . runImpl . unTerm

class
  ( PLC edsl
  , PUntyped edsl
  , PPartial edsl
  , forall a b. PConstructable edsl (PPair a b)
  , PConstructable edsl PUnit
  , forall a b. PConstructable edsl (PEither a b)
  , forall a. PConstructable edsl (PLet a)
  , forall a. PConstructable edsl (PFix a)
  ) => PULC edsl
instance (Applicative m) => PULC (ULCImpl m)

compile' :: Term (ULCImpl m) a -> m ULC
compile' (Term term) = runULambda (runImpl term)

compileAp :: CompileAp PULC ULC
compileAp _ t = let _unused = callStack in compile' t

compile :: Compile PULC ULC
compile _ t = let _unused = callStack in  compile' t