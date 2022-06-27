module Examples.DataKinds where

import Plutarch.Core
import Plutarch.EType
import Plutarch.Experimental
import GHC.Generics (Generic)
import Data.Kind (Type)

data Nat = N | S Nat
data SNat :: Nat -> Type where
  SN :: SNat 'N
  SS :: SNat n -> SNat ('S n)

data EBool ef = EFalse | ETrue
  deriving stock Generic
  deriving anyclass EIsNewtype

-- takes `edsl` twice..
data ESBool (b :: EHs EBool) ef
  = ESFalse (ef /$ EEq b EFalse)
  | ESTrue (ef /$ EEq b ETrue)

