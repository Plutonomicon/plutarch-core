{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Examples.Simple (eid_alt, eid, efalse) where

import Plutarch.Core (ELC, EPolymorphic, ESOP)
import Plutarch.Prelude

type ESystemF edsl = (ELC edsl, EPolymorphic edsl, ESOP edsl)

data EBool ef = ETrue | EFalse
  deriving stock (Generic)
instance EHasRepr EBool where type EReprSort _ = EReprSOP

newtype EId' a ef = EId' (ef /$ (a #-> a))
  deriving stock (Generic)
instance EHasRepr (EId' a) where type EReprSort _ = EReprSOP

newtype EId ef = EId (ef /$ EForall EId')
  deriving stock (Generic)
instance EHasRepr EId where type EReprSort _ = EReprSOP

efalse :: ESystemF edsl => Term edsl EBool
efalse = econ EFalse

eid''' :: (ESystemF edsl, IsEType edsl a) => Term edsl $ a #-> a
eid''' = elam \x -> x

eid'' :: (ESystemF edsl, IsEType edsl a) => Term edsl $ EId' a
eid'' = econ $ EId' eid'''

eid' :: ESystemF edsl => Term edsl (EForall EId')
eid' = econ $ EForall eid''

eid :: ESystemF edsl => Term edsl EId
eid = econ $ EId eid'

eid_alt :: ESystemF edsl => Term edsl EId
eid_alt = econ $ EId $$ EForall $ econ $ EId' $ elam \x -> x
