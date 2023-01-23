module Plutarch.Frontends.C (
  PC (..),
  PInt, PProc, PProcVA, PPointer, PChar, PString, PCFFIProc (..), PUnsafeC (..), PMain) where

import Plutarch.Repr (PHasRepr, PReprSort)
import Plutarch.Repr.Primitive (PReprPrimitive)
import Plutarch.Prelude
import Plutarch.Core (PAll)
import Generics.SOP.Dict (Dict (Dict))
import Generics.SOP (All, NP ((:*), Nil))
import Data.Text (Text)
import GHC.TypeLits (Symbol, KnownSymbol)
import Data.Proxy (Proxy (Proxy))
import Data.String (IsString)

data PInt (ef :: PTypeF)
instance PHasRepr PInt where type PReprSort _ = PReprPrimitive

data PChar (ef :: PTypeF)
instance PHasRepr PChar where type PReprSort _ = PReprPrimitive

data PProc (as :: [PType]) (b :: PType) (effect :: [PDSLKind -> Constraint]) (ef :: PTypeF)
  deriving PHasRepr via DerivePReprPrimitive

data PProcVA (as :: [PType]) (b :: PType) (effect :: [PDSLKind -> Constraint]) (ef :: PTypeF)
  deriving PHasRepr via DerivePReprPrimitive

data PPointer (a :: PType) (ef :: PTypeF)
  deriving PHasRepr via DerivePReprPrimitive

type PString = PPointer PChar

class PCFFIProc (name :: Symbol) (as :: [PType]) (b :: PType) (effect :: [PDSLKind -> Constraint]) (e :: PDSLKind) | name -> as b effect where
  pFFIProc :: Proxy name -> Term e (PProc as b effect)

class
  ( Num (Term e PInt)
  , IsPType e PInt
  , IsString (Term e PString)
  , IsPType e PChar
  , forall a. IsPType e a => IsPTypePrim e (PPointer a)
  , forall as b effect. All (IsPType e @PPType) as => IsPTypePrim e (PProc as b effect)
  , forall as b effect. All (IsPType e @PPType) as => IsPTypePrim e (PProcVA as b effect)
  ) => PC e where
  data PCLValue e (a :: PType)
  pset :: IsPType e a => Term e a ->  PCLValue e a -> PIO e ()
  pget :: IsPType e a => PCLValue e a -> Term e a
  pderef :: IsPType e a => Term e (PPointer a) -> PIO e (PCLValue e a)
  pref :: IsPType e a => PCLValue e a -> Term e (PPointer a)
  pmkProc :: IsPType e (PProc as b effect) => (forall e'. (PDSL e', PAll e' effect) => NP (Term e') as -> TermIO e' b) -> Term e (PProc as b effect)
  pcall :: (IsPType e (PProc as b effect), PAll e effect) => Term e (PProc as b effect) -> NP (Term e) as -> TermIO e b

class
  ( PC e
  ) => PUnsafeC e where
  punsafeFFIVar :: IsPType e a => Text -> PCLValue e a
  punsafeFFIProc :: (IsPType e (PProc as b effect), KnownSymbol name) => Proxy name -> (PCFFIProc name as b effect e => PIO e c) -> PIO e c
  punsafeCallVA :: (IsPType e (PProcVA as b effect), All (IsPType e) as', PAll e effect) => Term e (PProcVA as b effect) -> NP (Term e) as -> NP (Term e) as' -> TermIO e b

type PMain = PProc '[PInt, PPointer PString] PInt '[PUnsafeC]
