module Examples.DataKinds where

import Data.Kind (Type)
import GHC.Generics (Generic)
import Plutarch.Core
import Plutarch.EType
import Plutarch.Experimental

data Nat = N | S Nat
data SNat :: Nat -> Type where
  SN :: SNat 'N
  SS :: SNat n -> SNat ( 'S n)

data EBool ef = EFalse | ETrue
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

data ESBool (b :: EHs EBool) ef
  = ESFalse (ef /$ EEq b EFalse)
  | ESTrue (ef /$ EEq b ETrue)
