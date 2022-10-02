{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.ULC (ULC, ULCImpl,
 compileAp, compile, compile') where

import Data.Proxy

import GHC.Stack

import Plutarch.Core
import Plutarch.PType

data ULC
  = App ULC ULC
  | Lam ULC
  | Var Int
  | Error
  deriving stock (Show)

runULambda :: ULCImpl' m a -> m ULC
runULambda r = runImpl r 0

newtype ULCImpl' m (a :: PType) = ULCImpl { runImpl :: Int -> m ULC }

type ULCImpl m = 'PDSLKind (ULCImpl' m)

instance PDSL (ULCImpl m)

instance (Applicative m) => PConstructable' (ULCImpl m) (a #-> b) where
  pconImpl (PLam f) =
    ULCImpl \i ->
      Lam <$> runImpl (unTerm . f . Term $ ULCImpl $ \_ -> pure $ Var i) (i + 1)
  pmatchImpl (ULCImpl t) f =
    f $ PLam \(Term (ULCImpl x)) ->
      Term . ULCImpl $ \lvl -> App <$> t lvl <*> x lvl

instance (Applicative m, IsPType (ULCImpl m) a, IsPType (ULCImpl m) b) => PConstructable' (ULCImpl m) (PPair a b) where
  pconImpl (PPair a b) = unsafeCoerceULC . unTerm $ pcon $ PLam \p -> p # a # b
  pmatchImpl t f = f $ PPair (pfst (Term t)) (psnd (Term t))

tru, fls :: (Applicative m) => Term (ULCImpl m) (a #-> a #-> a)
tru = pcon $ PLam \t -> pcon $ PLam \_ -> t
fls = pcon $ PLam \_ -> pcon $ PLam \f -> f

pfst :: (Applicative m, IsPType (ULCImpl m) a) =>  Term (ULCImpl m) (PPair a b) -> Term (ULCImpl m) a
pfst p = (unsafeCoerceULCTerm p) # tru

psnd :: (Applicative m, IsPType (ULCImpl m) b) =>  Term (ULCImpl m) (PPair a b) -> Term (ULCImpl m) b
psnd p = (unsafeCoerceULCTerm p) # fls

instance (Applicative m, IsPType (ULCImpl m) a, IsPType (ULCImpl m) b) => PConstructable' (ULCImpl m) (PEither a b) where
  pconImpl t = unsafeCoerceULC . unTerm $ pcon $
    PLam \l -> pcon $ PLam \r -> case t of
      PLeft a -> l # a
      PRight b -> r # b

  pmatchImpl t f = unsafeULCTerm t # (pcon . PLam $ f . PLeft) # (pcon . PLam $ f . PRight)

instance (Applicative m) => PConstructable' (ULCImpl m) PUnit where
  pconImpl PUnit = unsafeCoerceULC . unTerm @(ULCImpl m) $ pcon $ PLam id
  pmatchImpl _ f = f PUnit

instance (Applicative m, IsPType (ULCImpl m) a) => PConstructable' (ULCImpl m) (PLet a) where
  pconImpl (PLet t) = unsafeCoerceULC . unTerm $ pcon (PLam id) # t
  pmatchImpl t f = f $ PLet (unsafeULCTerm t)

instance PConstructable' (ULCImpl m) (PFix a) where
  pconImpl (PFix t) = unsafeCoerceULC . unTerm $ t
  pmatchImpl t f = f $ PFix (unsafeULCTerm t)

-- instance PConstructable' (ULCImpl m) (PForall f) where
--   pconImpl (PForall t) = unsafeCoerceULC . unTerm $ t
--   pmatchImpl t f = f . PForall . Term . unsafeCoerceULC $ t

-- instance PConstructable' (ULCImpl m) (PSome f) where
--   pconImpl (PSome t) = unsafeCoerceULC . unTerm $ t
--   pmatchImpl t f = f . PSome . Term . unsafeCoerceULC $ t

instance PConstructable' (ULCImpl m) PAny where
  pconImpl (PAny _ t) = unsafeCoerceULC . unTerm $ t
  pmatchImpl t f = f $ PAny Proxy (unsafeULCTerm t)

unsafeCoerceULC :: ULCImpl' m a -> ULCImpl' m b
unsafeCoerceULC = ULCImpl . runImpl

unsafeULCTerm :: ULCImpl' m a -> Term (ULCImpl m) b
unsafeULCTerm = Term . unsafeCoerceULC

unsafeCoerceULCTerm :: Term (ULCImpl m) a -> Term (ULCImpl m) b
unsafeCoerceULCTerm = unsafeULCTerm . unTerm

instance PUntyped (ULCImpl m) where
  punsafeCoerce = Term . unsafeCoerceULC . unTerm

instance (Applicative m) => PPartial (ULCImpl m) where
  perror = Term (ULCImpl $ const $ pure Error)

instance (Applicative m) =>  PAp m (ULCImpl m) where
  papr x y = Term . ULCImpl $ \i -> x *> runImpl (unTerm y) i
  papl x y = Term . ULCImpl $ \i -> runImpl (unTerm x) i <* y

instance (Monad m) => PEmbeds m (ULCImpl m) where
  pembed mt = Term . ULCImpl $ \i -> mt >>= \t -> runImpl (unTerm t) i

class
  ( PLC edsl
  , PUntyped edsl
  , PPartial edsl
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable edsl (PPair a b)
  , PConstructable edsl PUnit
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable edsl (PEither a b)
  , forall a. (IsPType edsl a) => PConstructable edsl (PLet a)
  , forall a. PConstructable edsl (PFix a)
  ) => PULC edsl
instance
  ( PLC edsl
  , PUntyped edsl
  , PPartial edsl
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable edsl (PPair a b)
  , PConstructable edsl PUnit
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable edsl (PEither a b)
  , forall a. (IsPType edsl a) => PConstructable edsl (PLet a)
  , forall a. PConstructable edsl (PFix a)
  ) => PULC edsl

compile' :: Term (ULCImpl m) a -> m ULC
compile' (Term term) = runULambda term

compileAp :: CompileAp PULC ULC
compileAp t = let _unused = callStack in compile' t

compile :: Compile PULC ULC
compile t = let _unused = callStack in  compile' t
