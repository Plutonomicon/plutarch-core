{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Examples.Simple where
    
import Plutarch.Core
import Plutarch.EType
import GHC.Generics (Generic)
import Data.Proxy (Proxy (Proxy))

type ESystemF edsl = (ELC edsl, EPolymorphic edsl, ESOP edsl)

data F
instance ESystemF edsl => ENamedTerm F edsl (EUnit #-> EUnit) where
  enamedTermImpl _ = elam \x -> g # x

f :: ESystemF edsl => Term edsl (EUnit #-> EUnit)
f = enamedTerm (Proxy @F)

data G
instance ESystemF edsl => ENamedTerm G edsl (EUnit #-> EUnit) where
  enamedTermImpl _ = elam \x -> f # x

g :: ESystemF edsl => Term edsl (EUnit #-> EUnit)
g = enamedTerm (Proxy @G)

{-

f :: Functor f => f Bool -> f Bool
f x = not <$> x

data EBool f = ETrue | EFalse
  deriving stock Generic
  deriving anyclass EIsNewtype

newtype EId' a = EId' (Ef f (a #-> a)
newtype EId = EId (EForall something EId')

--newtype EMap f a b ef = EMap (Ef ef (f a #-> f b))

--newtype EMap' a b ef = EMap (EForall (IsEType2 edsl) )

class EFunctor edsl f where
  --emap :: Term edsl (EMap f)

newtype A a f = A (Ef f (a EBool #-> a EBool))

--f' :: EFunctor f => Term edsl
--
-}
