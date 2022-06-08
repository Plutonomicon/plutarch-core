{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Plutarch.SystemF where
  
import Plutarch.Core
import Plutarch.EType
import Data.Proxy (Proxy (Proxy))
import Data.Kind (Type)

data Nat = N | S Nat
data SNat :: Nat -> Type where
  SN :: SNat N
  SS :: SNat n -> SNat (S n)

class KnownSNat (n :: Nat) where
  snat :: Proxy n -> SNat n

instance KnownSNat N where
  snat _ = SN

instance KnownSNat n => KnownSNat (S n) where
  snat _ = SS (snat (Proxy @n))

snatIn :: SNat n -> (KnownSNat n => a) -> a
snatIn SN x = x
snatIn (SS n') x = snatIn n' x

newtype Lvl = Lvl { unLvl :: Int }

lvlFromSNat :: SNat n -> Lvl
lvlFromSNat SN = Lvl 0
lvlFromSNat (SS n) = Lvl $ unLvl (lvlFromSNat n) + 1

data SFKind
  = SFKindType
  | SFKindFun SFKind SFKind

data SFType
  = SFTyVar Lvl
  | SFTyFun SFType SFType
  | SFTyForall SFKind SFType
  | SFTyLam SFKind SFType
  | SFTyApp SFType SFType
  | SFTyUnit
  | SFTyPair SFType SFType
  | SFTyEither SFType SFType

data SFTerm' (m :: Type -> Type)
  = SFVar' Lvl
  | SFLam' SFType (SFTerm' m)
  | SFApp' (SFTerm' m) (SFTerm' m)
  | SFForall' SFKind (SFTerm' m)
  | SFInst' (SFTerm' m) SFType
  | SFUnit'
  | SFPair' (SFTerm' m) (SFTerm' m)
  | SFLeft' (SFTerm' m) SFType
  | SFRight' SFType (SFTerm' m)
  | SFFst' (SFTerm' m)
  | SFSnd' (SFTerm' m)
  | SFMatch' (SFTerm' m) (SFTerm' m) (SFTerm' m)

data SFTerm
  = SFVar Lvl
  | SFLam SFType SFTerm
  | SFApp SFTerm SFTerm
  | SFForall SFKind SFTerm
  | SFInst SFTerm SFType
  | SFUnit
  | SFPair SFTerm SFTerm
  | SFLeft SFTerm SFType
  | SFRight SFType SFTerm
  | SFFst SFTerm
  | SFSnd SFTerm
  | SFMatch SFTerm SFTerm SFTerm

type ESystemF edsl = (ELC edsl, EPolymorphic edsl, ESOP edsl)

newtype Impl (m :: Type -> Type) (a :: EType) = Impl { runImpl :: forall n. SNat n -> m (SFTerm' m) }


{-

class TypeInfo (a :: EType) where
  typeInfo :: Proxy a -> SNat n -> SFType

data TyVar (n :: Nat) f
instance KnownSNat n => TypeInfo (TyVar n) where
  typeInfo _ _ = SFTyVar . lvlFromSNat $ snat (Proxy @n)

instance TypeInfo EUnit where
  typeInfo _ _ = SFTyUnit

instance (TypeInfo a, TypeInfo b) => TypeInfo (EPair a b) where
  typeInfo _ lvl = SFTyPair (typeInfo (Proxy @a) lvl) (typeInfo (Proxy @b) lvl)

instance (TypeInfo a, TypeInfo b) => TypeInfo (EEither a b) where
  typeInfo _ lvl = SFTyEither (typeInfo (Proxy @a) lvl) (typeInfo (Proxy @b) lvl)

instance (TypeInfo a, TypeInfo b) => TypeInfo (a #-> b) where
  typeInfo _ lvl = SFTyFun (typeInfo (Proxy @a) lvl) (typeInfo (Proxy @b) lvl)

instance (forall a. TypeInfo a => TypeInfo (f a)) => TypeInfo (EForall (IsEType Impl) f) where
  typeInfo _ (lvl :: SNat lvl) = SFTyForall SFKindType (snatIn lvl $ typeInfo (Proxy @(f (TyVar lvl))) (SS lvl))

instance EDSL Impl where
  type IsEType' Impl = TypeInfo
  enamedTerm = enamedTermImpl

instance (TypeInfo a, TypeInfo b) => EConstructable Impl (a #-> b) where
  econ (ELam f) = Term $ Impl \lvl -> SFLam' (typeInfo (Proxy @a) lvl) $ runImpl (unTerm . f . Term $ Impl \_ -> SFVar' (lvlFromSNat lvl)) (SS lvl)
  ematch (Term f) g = g $ ELam \(Term x) -> Term $ Impl \lvl -> runImpl f lvl `SFApp'` runImpl x lvl

instance EConstructable Impl EUnit where
  econ EUnit = Term $ Impl \_ -> SFUnit'
  ematch _ f = f EUnit

instance (TypeInfo a, TypeInfo b) => EConstructable Impl (EPair a b) where
  econ (EPair (Term x) (Term y)) = Term $ Impl \lvl -> SFPair' (runImpl x lvl) (runImpl y lvl)
  ematch (Term t) f = f $ EPair (Term $ Impl \lvl -> SFFst' $ runImpl t lvl) (Term $ Impl \lvl -> SFSnd' $ runImpl t lvl)

instance (TypeInfo a, TypeInfo b) => EConstructable Impl (EEither a b) where
  econ (ELeft (Term x)) = Term $ Impl \lvl -> SFLeft' (runImpl x lvl) (typeInfo (Proxy @b) lvl)
  econ (ERight (Term y)) = Term $ Impl \lvl -> SFRight' (typeInfo (Proxy @a) lvl) (runImpl y lvl)
  ematch (Term t) f = Term $ Impl \lvl ->
    SFMatch' (runImpl t lvl)
      (runImpl (unTerm $ elam \left -> f (ELeft left)) lvl)
      (runImpl (unTerm $ elam \right -> f (ERight right)) lvl)

instance (forall a. TypeInfo a => TypeInfo (f a)) => EConstructable Impl (EForall (IsEType Impl) f) where
  econ t' = Term $ Impl \(lvl :: SNat lvl) -> snatIn lvl $ case t' of
    (EForall (Term (t :: Impl (f (TyVar lvl))))) -> SFForall' SFKindType $ runImpl t (SS lvl)
  ematch (Term t) f =
    let
      applied :: forall a. TypeInfo a => Impl (f a)
      applied = Impl \lvl -> runImpl t lvl `SFInst'` (typeInfo (Proxy @a) lvl)
    in
    f $ EForall $ Term applied

compile' :: forall a. (IsEType Impl a, EConstructable Impl a) => Term Impl a -> (SFTerm', SFType)
compile' (Term t :: Term Impl a) = (runImpl t SN, typeInfo (Proxy @a) SN)

compile :: forall a. (forall edsl. ESystemF edsl => EConstructable edsl a) => (forall edsl. ESystemF edsl => Term edsl a) -> (SFTerm', SFType)
compile t = compile' t

-}
