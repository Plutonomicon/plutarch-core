{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Examples.Simple (pid_alt, pid, pfalse) where

import "plutarch-core" Plutarch.Frontends.Data (PSOP)
import "plutarch-core" Plutarch.Frontends.LC (PLC, PPolymorphic)
import "plutarch-core" Plutarch.Prelude

type PSystemF edsl = (PLC edsl, PPolymorphic edsl, PSOP edsl)

data PBool ef = PTrue | PFalse
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

newtype PId' a ef = PId' (ef /$ (a #-> a))
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

newtype PId ef = PId (ef /$ PForall PId')
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pfalse :: PSystemF edsl => Term edsl PBool
pfalse = pcon PFalse

pid''' :: (PLC edsl, IsPType edsl a) => Term edsl $ a #-> a
pid''' = plam \x -> x

pid'' :: (PSOP edsl, PLC edsl, IsPType edsl a) => Term edsl $ PId' a
pid'' = pcon $ PId' pid'''

pid' :: PSystemF edsl => Term edsl (PForall PId')
pid' = pcon $ PForall pid''

pid :: PSystemF edsl => Term edsl PId
pid = pcon $ PId pid'

pid_alt :: PSystemF edsl => Term edsl (PForall PId')
pid_alt = pcon $ PForall $ pcon $ PId' $ plam \x -> x
