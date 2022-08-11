module Pxamples.DataKinds where

import Data.Kind (Type)
import Plutarch.Pxperimental (PEq)
import Plutarch.Prelude

data Nat = N | S Nat
data SNat :: Nat -> Type where
  SN :: SNat 'N
  SS :: SNat n -> SNat ( 'S n)

data PBool ef = PFalse | PTrue
  deriving stock (Generic)
instance PHasRepr PBool where type PReprSort _ = PReprSOP

data PSBool (b :: PHs PBool) ef
  = PSFalse (ef /$ PEq b PFalse)
  | PSTrue (ef /$ PEq b PTrue)
  deriving stock (Generic)
instance PHasRepr (PSBool b) where type PReprSort _ = PReprSOP
