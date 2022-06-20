{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Examples.Simple where
    
import Plutarch.Core
import Plutarch.EType
import GHC.Generics (Generic)
import Data.Proxy (Proxy (Proxy))

type ESystemF edsl = (ELC edsl, EPolymorphic edsl, ESOP edsl)

data EBool ef = ETrue | EFalse
  deriving stock Generic
  deriving anyclass EIsNewtype

newtype EForall1 (f :: EType -> EType) ef = EForall1 (Ef ef (EForall (IsEType (UnEf ef)) f))
  deriving stock Generic
  deriving anyclass EIsNewtype

newtype EId' a ef = EId' (Ef ef (a #-> a))
newtype EId ef = EId (Ef ef (EForall1 EId'))

type U0 = EUnit
type U1 = EEither U0 U0
type U2 = EEither U1 U1
type U3 = EEither U2 U2
type U4 = EEither U3 U3
type U5 = EEither U4 U4
type U6 = EEither U5 U5
type U7 = EEither U6 U6
type U8 = EEither U7 U7

type Word = U8

f :: ESOP edsl => Term edsl U1 -> Term edsl U0
f x = ematch x \case
  ERight EUnit -> econ EUnit
  ELeft EUnit -> econ EUnit

{-

f :: Functor f => f Bool -> f Bool
f x = not <$> x


--newtype EMap f a b ef = EMap (Ef ef (f a #-> f b))

--newtype EMap' a b ef = EMap (EForall (IsEType2 edsl) )

class EFunctor edsl f where
  --emap :: Term edsl (EMap f)

newtype A a f = A (Ef f (a EBool #-> a EBool))

--f' :: EFunctor f => Term edsl
--
-}
