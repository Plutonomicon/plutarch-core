{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Examples.Simple (eid_alt, eid, efalse) where

import Plutarch.Core (PLC, PPolymorphic, PSOP)
import Plutarch.Prelude

type PSystemF edsl = (PLC edsl, PPolymorphic edsl, PSOP edsl)

data PBool ef = PTrue | PFalse
  deriving stock (Generic)
instance PHasRepr PBool where type PReprSort _ = PReprSOP

newtype PId' a ef = PId' (ef /$ (a #-> a))
  deriving stock (Generic)
instance PHasRepr (PId' a) where type PReprSort _ = PReprSOP

newtype PId ef = PId (ef /$ PForall PId')
  deriving stock (Generic)
instance PHasRepr PId where type PReprSort _ = PReprSOP

efalse :: PSystemF edsl => Term edsl PBool
efalse = econ PFalse

eid''' :: (PSystemF edsl, IsPType edsl a) => Term edsl $ a #-> a
eid''' = elam \x -> x

eid'' :: (PSystemF edsl, IsPType edsl a) => Term edsl $ PId' a
eid'' = econ $ PId' eid'''

eid' :: PSystemF edsl => Term edsl (PForall PId')
eid' = econ $ PForall eid''

eid :: PSystemF edsl => Term edsl PId
eid = econ $ PId eid'

eid_alt :: PSystemF edsl => Term edsl PId
eid_alt = econ $ PId $$ PForall $ econ $ PId' $ elam \x -> x
