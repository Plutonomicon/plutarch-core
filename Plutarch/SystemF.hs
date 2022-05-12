module Plutarch.SystemF where

import Plutarch.Core
import Plutarch.EType
import Data.Proxy (Proxy (Proxy))

newtype Lvl = Lvl Int

succLvl :: Lvl -> Lvl
succLvl (Lvl l) = Lvl (l + 1)

data SFKind
  = SFType
  | SFTyFun SFKind SFKind

data SFType
  = SFTyVar Lvl
  | SFTyFun SFType SFType
  | SFTyForall SFKind SFType
  | SFTyLam SFKind SFType
  | SFTyApp SFType SFType
  | SFTyUnit
  | SFTyPair SFType SFType
  | SFTyEither SFType SFType

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

class TypeInfo (a :: EType) where
  typeInfo :: Proxy a -> SFType

instance TypeInfo EUnit where
  typeInfo _ = SFTyUnit

instance (TypeInfo a, TypeInfo b) => TypeInfo (EPair a b) where
  typeInfo _ = SFTyPair (typeInfo $ Proxy @a) (typeInfo $ Proxy @b)

instance (TypeInfo a, TypeInfo b) => TypeInfo (EEither a b) where
  typeInfo _ = SFTyEither (typeInfo $ Proxy @a) (typeInfo $ Proxy @b)

instance (TypeInfo a, TypeInfo b) => TypeInfo (a #-> b) where
  typeInfo _ = SFTyFun (typeInfo $ Proxy @a) (typeInfo $ Proxy @b)

newtype Impl (a :: EType) = Impl { runImpl :: Lvl -> Impl }

instance EDSL Impl where
  type IsEType Impl = TypeInfo

instance (TypeInfo a, TypeInfo b) => EConstructable Impl (EPair a b) where
  econ (EPair x y) = Impl \lvl -> SFPair (runImpl x lvl) (runImpl y lvl)
  ematch t f = f $ EPair (Impl \lvl -> SFFst $ runImpl t lvl) (Impl \lvl -> SFSnd $ runImpl t lvl)

{-
instance (TypeInfo a, TypeInfo b) => EConstructable Impl (EEither a b) where
  econ (ELeft x) = Impl \lvl -> MkSumLeft (runImpl x lvl) (typeInfo $ Proxy @b)
  econ (ERight y) = Impl \lvl -> MkSumRight (typeInfo $ Proxy @a) (runImpl y lvl)
  ematch t f = Impl \lvl ->
    Match (runImpl t lvl)
      (runImpl ((elam \left -> f (ELeft left))) lvl)
      (runImpl (elam \right -> f (ERight right)) lvl)

instance (TypeInfo a, TypeInfo b) => EConstructable Impl (a #-> b) where
  econ (ELam f) = Impl \lvl -> Lam (typeInfo $ Proxy @a) $ runImpl (f $ Impl \_ -> Var lvl) (succLvl lvl)
  ematch f g = g $ ELam \x -> Impl \lvl -> runImpl f lvl `App` runImpl x lvl

compile :: (forall edsl. ESTLC edsl => edsl a) -> (SimpleTerm, SimpleType)
compile = undefined
-}
