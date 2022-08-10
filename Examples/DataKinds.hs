module Examples.DataKinds where

import Data.Kind (Type)
import Plutarch.Experimental (EEq)
import Plutarch.Prelude

data Nat = N | S Nat
data SNat :: Nat -> Type where
  SN :: SNat 'N
  SS :: SNat n -> SNat ( 'S n)

data EBool ef = EFalse | ETrue
  deriving stock (Generic)
instance EHasRepr EBool where type EReprSort _ = EReprSOP

data ESBool (b :: EHs EBool) ef
  = ESFalse (ef /$ EEq b EFalse)
  | ESTrue (ef /$ EEq b ETrue)
  deriving stock (Generic)
instance EHasRepr (ESBool b) where type EReprSort _ = EReprSOP
