{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Plutarch.SystemF where
  
import Plutarch.Core
import Plutarch.EType
import Data.Proxy (Proxy (Proxy))
import Data.Kind (Type)
import Data.Fix (Fix)

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

data SFKindF a
  = SFKindType
  | SFKindFun a a

type SFKind = Fix SFKindF

data SFTypeF a
  = SFTyVar Lvl
  | SFTyFun a a
  | SFTyForall SFKind a
  | SFTyLam SFKind a
  | SFTyApp a a
  | SFTyUnit
  | SFTyPair a a
  | SFTyEither a a

type SFType = Fix SFTypeF

data SFTermF a
  = SFVar Lvl
  | SFLam SFType a
  | SFApp a a
  | SFForall SFKind a
  | SFInst a SFType
  | SFUnit
  | SFPair a a
  | SFLeft a SFType
  | SFRight SFType a
  | SFFst a
  | SFSnd a
  | SFMatch a a a

type SFTerm = Fix SFTermF

type ESystemF edsl = (ELC edsl, EPolymorphic edsl, ESOP edsl)

newtype Impl (m :: Type -> Type) (a :: ETypeRepr) = Impl { runImpl :: forall n. SNat n -> m SFTerm }

class TypeInfo' (m :: Type -> Type) (a :: ETypeRepr) where
  typeInfo' :: Proxy m -> Proxy a -> SNat n -> SFType

class TypeInfo' m (ERepr a) => TypeInfo m a
instance TypeInfo' m (ERepr a) => TypeInfo m a

typeInfo :: forall a m. TypeInfo m a => Proxy m -> Proxy a -> SFType
typeInfo m _ = typeInfo' m (Proxy @(ERepr a))

data TyVar (n :: Nat) f
instance KnownSNat n => TypeInfo m (TyVar n) where
  typeInfo _ _ _ = SFTyVar . lvlFromSNat $ snat (Proxy @n)

instance TypeInfo m EUnit where
  typeInfo _ _ _ = SFTyUnit

instance (TypeInfo m a, TypeInfo m b) => TypeInfo m (EPair a b) where
  typeInfo m _ lvl = SFTyPair (typeInfo m (Proxy @a) lvl) (typeInfo m (Proxy @b) lvl)

instance (TypeInfo m a, TypeInfo m b) => TypeInfo m (EEither a b) where
  typeInfo m _ lvl = SFTyEither (typeInfo m (Proxy @a) lvl) (typeInfo m (Proxy @b) lvl)

instance (TypeInfo m a, TypeInfo m b) => TypeInfo m (a #-> b) where
  typeInfo m _ lvl = SFTyFun (typeInfo m (Proxy @a) lvl) (typeInfo m (Proxy @b) lvl)

instance (forall a. TypeInfo a => TypeInfo (f a)) => TypeInfo (EForall (IsEType (Impl m)) f) where
  typeInfo m _ (lvl :: SNat lvl) = SFTyForall SFKindType (snatIn lvl $ typeInfo m (Proxy @(f (TyVar lvl))) (SS lvl))
{-


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
