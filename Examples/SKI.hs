-- This isn't necessarily Plutarch-related, but is more so a test for the SKI singletons stuff

module Examples.SKI where

import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Generic)
import Plutarch.Internal.SKI

type FlipS :: (a ~> b ~> c) ~> b ~> a ~> c
type FlipS = S :@ (S :@ (K :@ S) :@ (S :@ (K :@ K) :@ S)) :@ (K :@ K)

type ComposeS :: (b ~> c) ~> (a ~> b) ~> a ~> c
type ComposeS = S :@ (K :@ S) :@ K

type (.) a b = ComposeS :@ a :@ b
infixr 8 .

type (<*>) a b = S :@ a :@ b
infixl 4 <*>

type TwiceS :: a ~> (a ~> a ~> b) ~> b
type TwiceS = S :@ (S :@ (K :@ S) :@ (S :@ (K :@ (S :@ I)) :@ K)) :@ K

type TopairS :: a ~> (a, a)
type TopairS = FlipS :@ TwiceS :@ MkPair

newtype Id' a = Id' (a ~> a)
  deriving stock (Generic)
type instance DefineNewtypeInner (Id' a) = a ~> a
type instance DefineNewtypeConstructor (Id' _) = 'Id'

type IdS'' :: () ~> a ~> a
type IdS'' = K :@ I

type family IdS' :: forall a. () ~> Id' a

-- FIXME: GHC needs type-level big lambdas
-- type instance IdS' = S :@ (K :@ MkNewtype) :@ (K :@ I)

type IdS :: () ~> ForallS Id'
type IdS = MkForall IdS'

idS :: () ~> ForallS Id'
idS = MkForall $ S :@ (K :@ MkNewtype) :@ (K :@ I)

type RemoveConstantS :: (c ~> a ~> b) ~> (a ~> c) ~> a ~> b
type RemoveConstantS = ComposeS :@ S :@ FlipS

type RemoveUnitS :: (() ~> a ~> b) ~> a ~> b
type RemoveUnitS = FlipS :@ RemoveConstantS :@ MkUnit

type IdS_recovered :: forall a. a ~> a
type IdS_recovered = RemoveUnitS :@ (ComposeS :@ ElimNewtype :@ (S :@ (K :@ ElimForall) :@ IdS))

newtype NatF a = NatF (Either () a)
  deriving stock (Show, Generic)
type instance DefineNewtypeInner (NatF a) = Either () a
type instance DefineNewtypeConstructor (NatF _) = 'NatF

type Nat = Fix NatF

type NatZ :: a ~> Nat
type NatZ = MkFix . MkNewtype . MkLeft . MkUnit

type NatS :: Nat ~> Nat
type NatS = MkFix . MkNewtype . MkRight

type NatAdd' :: (Nat ~> Nat ~> Nat) ~> Nat ~> Nat ~> Nat
type NatAdd' =
  (K :@ ComposeS <*> (K :@ (ElimEither :@ (K :@ I)) <*> ComposeS :@ (FlipS :@ ComposeS :@ NatS)))
    <*> K
    :@ (ElimNewtype . ElimFix)

type NatAdd :: Nat ~> Nat ~> Nat
type NatAdd = FixSKI :@ NatAdd'

natAdd :: Nat -> Nat -> Nat
natAdd = interp . interp (known' (Proxy @NatAdd))

type Ex :: Nat
type Ex = Interp (NatS . NatS . NatZ) ()

{-

zero_plus_x_is_x :: Single (n :: Nat) -> Interp (K :@ NatAdd <*> NatZ <*> K :@@ n) '() :~: n
zero_plus_x_is_x _ = Refl

zero_plus_x_is_xS :: Single (n :: Nat) ~> Interp (K :@ NatAdd <*> NatZ <*> K :@@ n) '() :~: n
zero_plus_x_is_xS = MkEq
-}

{-
x_plus_zero_is_x :: Single (n :: Nat) -> Interp (K :@ (NatAdd :@@ n) <*> NatZ) '() :~: n
x_plus_zero_is_x (SFix n) = sunwrap n \Refl n' -> case n' of
  SLeft SUnit -> Refl
  SRight n'' -> _ $ x_plus_zero_is_x n''
-}
