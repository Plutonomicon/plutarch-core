{-
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.SystemF (ESystemF, SFTerm, SFTermF (..), SFType, SFTypeF (..)) where

import Data.Fix (Fix (Fix))
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Stack (callStack)
import Plutarch.Internal.WithDictHack (unsafeWithDict)
import Plutarch.Experimental (EEq)
import Plutarch.Core
import Plutarch.EType
import qualified Generics.SOP as SOP
import qualified Generics.SOP.GGP as SOPG
import Data.Functor.Const (Const (Const), getConst)

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

newtype Lvl = Lvl {unLvl :: Int}

lvlFromSNat :: SNat n -> Lvl
lvlFromSNat SN = Lvl 0
lvlFromSNat (SS n) = Lvl $ unLvl (lvlFromSNat n) + 1

data SFTermF b t a
  = SFVar Lvl
  | SFLam t a
  | SFApp a a
  | SFForall t a
  | SFInst a t
  | SFUnit
  | SFPair a a
  | SFLeft a t
  | SFRight t a
  | SFFst a
  | SFSnd a
  | SFMatch a a a
  | SFTermTy b
  | SFRefl t t
  | SFReplace t t t a a

data SFTypeF a
  = SFTyFun a a
  | SFTyForall a a
  | SFTyUnit
  | SFTyVoid
  | SFTyPair a a
  | SFTyEither a a
  | SFTyEq a a a
  -- Type in Type
  | SFTyType
  -- Lift a term
  | SFTyTerm (Fix (SFTermF a a))

type SFType = Fix SFTypeF

type SFTerm = Fix (SFTermF () SFType)

type ESystemF edsl = (ELC edsl, EPolymorphic edsl, ESOP edsl)

newtype Impl' (m :: Type -> Type) (a :: EType) = Impl {runImpl :: forall n. SNat n -> m SFTerm}
type Impl m = 'EDSLKind (Impl' m)

instance EDSL (Impl m) where
  type IsEType' (Impl m) = TypeInfo' m

class TypeInfo' (m :: Type -> Type) (a :: k) where
  typeInfo' :: Proxy m -> Proxy a -> SNat n -> SFType

class TypeInfo' m (ERepr a) => TypeInfo m a
instance TypeInfo' m (ERepr a) => TypeInfo m a

typeInfo :: forall m a n. TypeInfo m a => Proxy m -> Proxy a -> SNat n -> SFType
typeInfo m _ n = typeInfo' m (Proxy @(ERepr a)) n

type family EvilHack (k :: Type) (n :: Nat) :: k where

h :: (SNat n -> SFType) -> Proxy m -> Proxy a -> SNat n -> SFType
h f _ _ lvl = f lvl

withEvilHack :: forall m k n a. KnownSNat n => Proxy m -> Proxy k -> Proxy n -> (TypeInfo m (EvilHack k n) => a) -> a
withEvilHack _ _ _ f = unsafeWithDict (Proxy @(TypeInfo m (EvilHack k n))) (g $ lvlFromSNat $ snat (Proxy @n)) f
  where
    g :: forall m a n. Lvl -> Proxy m -> Proxy a -> SNat n -> SFType
    g lvl _ _ _ = Fix $ SFTyTerm $ Fix $ SFVar lvl

instance TypeInfo' m EUnit where
  typeInfo' _ _ _ = Fix SFTyUnit

instance (TypeInfo m a, TypeInfo m b) => TypeInfo' m ((EPair a b)) where
  typeInfo' m _ lvl = Fix $ SFTyPair (typeInfo m (Proxy @a) lvl) (typeInfo m (Proxy @b) lvl)

instance (TypeInfo m a, TypeInfo m b) => TypeInfo' m ((EEither a b)) where
  typeInfo' m _ lvl = Fix $ SFTyEither (typeInfo m (Proxy @a) lvl) (typeInfo m (Proxy @b) lvl)

instance (TypeInfo m a, TypeInfo m b) => TypeInfo' m ((a #-> b)) where
  typeInfo' m _ lvl = Fix $ SFTyFun (typeInfo m (Proxy @a) lvl) (typeInfo m (Proxy @b) lvl)

instance TypeInfo' m 'EUnit where
  typeInfo' _ _ _ = Fix $ SFTyTerm $ Fix $ SFUnit

instance (TypeInfo m x, TypeInfo m y) => TypeInfo' m ('EPair x y) where
  typeInfo' m _ lvl = Fix $ SFTyTerm $ Fix $ SFPair
    (Fix $ SFTermTy $ typeInfo m (Proxy @x) lvl)
    (Fix $ SFTermTy $ typeInfo m (Proxy @y) lvl)

instance forall (ef :: ETypeF) (a :: EType) (b :: EType) (m :: Type -> Type) (x :: ef /$ a).
  (TypeInfo m x, TypeInfo m b) => TypeInfo' m ('ELeft x :: EEither a b ef) where
  typeInfo' m _ lvl = Fix $ SFTyTerm $ Fix $ SFLeft
    (Fix $ SFTermTy $ typeInfo m (Proxy @x) lvl)
    (typeInfo m (Proxy @b) lvl)

instance forall (ef :: ETypeF) (a :: EType) (b :: EType) (m :: Type -> Type) (y :: ef /$ b).
  (TypeInfo m a, TypeInfo m y) => TypeInfo' m ('ERight y :: EEither a b ef) where
  typeInfo' m _ lvl = Fix $ SFTyTerm $ Fix $ SFRight
    (typeInfo m (Proxy @a) lvl)
    (Fix $ SFTermTy $ typeInfo m (Proxy @y) lvl)

gpInfo :: forall (a :: [EType]) m lvl. SOP.All (TypeInfo m) a => Proxy m -> Proxy a -> SNat lvl -> SFType
gpInfo _ _ lvl = getConst $ (SOP.cpara_SList (Proxy @(TypeInfo m)) (Const (Fix SFTyUnit)) go :: Const SFType a)
  where
    go :: forall (y :: EType) ys. TypeInfo m y => Const SFType ys -> Const SFType (y : ys)
    go (Const (Fix SFTyUnit)) = Const $ typeInfo (Proxy @m) (Proxy @y) lvl
    go (Const x) = Const $ Fix $ SFTyPair (typeInfo (Proxy @m) (Proxy @y) lvl) x

gsInfo :: forall (a :: [[EType]]) m lvl. SOP.All2 (TypeInfo m) a => Proxy m -> Proxy a -> SNat lvl -> SFType
gsInfo _ _ lvl = getConst $ (SOP.cpara_SList (Proxy @(SOP.All (TypeInfo m))) (Const (Fix SFTyVoid)) go :: Const SFType a)
  where
    go :: forall (y :: [EType]) ys. (SOP.All (TypeInfo m) y) => Const SFType ys -> Const SFType (y : ys)
    go (Const (Fix SFTyVoid)) = Const $ gpInfo (Proxy @m) (Proxy @y) lvl
    go (Const x) = Const $ Fix $ SFTyEither (gpInfo (Proxy @m) (Proxy @y) lvl) x

mapAll :: forall a b c d. (SOP.All c a, forall a'. c a' => d a') => Proxy a -> Proxy c -> Proxy d -> (SOP.All d a => b) -> b
mapAll _ c d f = case (SOP.sList :: SOP.SList a) of
  SOP.SNil -> f
  SOP.SCons @_ @at -> mapAll (Proxy @at) c d f

mapAll2 :: forall a b c d. (SOP.All2 c a, forall a'. c a' => d a') => Proxy a -> Proxy c -> Proxy d -> (SOP.All2 d a => b) -> b
mapAll2 _ c d f = case (SOP.sList :: SOP.SList a) of
  SOP.SNil -> f
  SOP.SCons @_ @at @ah -> mapAll2 (Proxy @at) c d $ mapAll (Proxy @ah) c d f

helper2 :: forall a b m. SOP.All2 (IsEType (Impl m)) a => Proxy m -> Proxy a -> (SOP.All2 (TypeInfo m) a => b) -> b
helper2 _ _ = mapAll2 (Proxy @a) (Proxy @(IsEType (Impl m))) (Proxy @(TypeInfo m))

instance (EIsSOP (Impl m) a) => TypeInfo' m (ESOPed a) where
  typeInfo' m _ lvl =
    case esop (Proxy @(Impl m)) (Proxy @a) of
      EIsSumR {inner} -> helper2 m inner $ gsInfo m inner lvl

instance (TypeInfo m k, TypeInfo m (a :: k), TypeInfo m (b :: k)) => TypeInfo' m (EEq a b) where
  typeInfo' m _ lvl = Fix $ SFTyEq (typeInfo m (Proxy @k) lvl) (typeInfo m (Proxy @a) lvl) (typeInfo m (Proxy @b) lvl)

instance (TypeInfo m k, forall (a :: k). TypeInfo m a => TypeInfo m (f a)) => TypeInfo' m (f :: k -> l) where
  typeInfo' m _ (lvl :: SNat lvl) = Fix $ SFTyTerm $ Fix $ SFLam (typeInfo m (Proxy @k) lvl) $ Fix $ SFTermTy $
    snatIn lvl $ withEvilHack (Proxy @m) (Proxy @k) (Proxy @lvl) $
      typeInfo m (Proxy @(f (EvilHack k lvl))) (SS lvl)

instance TypeInfo m f => TypeInfo' m (EForall (f :: k -> EType)) where
  typeInfo' m _ (lvl :: SNat lvl) = Fix $ SFTyForall (Fix SFTyType) $ typeInfo m (Proxy @f) (SS lvl)

instance Applicative m => EAp m (Impl m) where
  eapr x y = Term $ Impl \lvl -> x *> runImpl (unTerm $ y) lvl
  eapl x y = Term $ Impl \lvl -> runImpl (unTerm $ x) lvl <* y

instance Monad m => EEmbeds m (Impl m) where
  eembed t = Term $ Impl \lvl -> do
    t' <- t
    runImpl (unTerm $ t') lvl

instance (Applicative m, TypeInfo m a, TypeInfo m b) => EConstructable' (Impl m) (a #-> b) where
  econImpl (ELam f) = Impl \lvl -> fmap Fix $ SFLam (typeInfo (Proxy @m) (Proxy @a) lvl) <$> runImpl (unTerm . f . Term $ Impl \_ -> pure $ Fix $ SFVar (lvlFromSNat lvl)) (SS lvl)
  --ematchImpl f g = g $ ELam \(Term x) -> Term $ Impl \lvl -> runImpl f lvl `SFApp` runImpl x lvl
{-

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

compile' :: forall a m. (Applicative m, IsEType (Impl m) a) => Term (Impl m) a -> m (SFTerm, SFType)
compile' (Term t) = (,) <$> runImpl t SN <*> pure (typeInfo (Proxy @m) (Proxy @a) SN)

compile :: Compile EDSL (SFTerm, SFType)
compile t = let _unused = callStack in compile' t

compileAp :: CompileAp EDSL (SFTerm, SFType)
compileAp t = let _unused = callStack in compile' t
-}
-}
