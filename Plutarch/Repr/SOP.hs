{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Repr.SOP (PReprSOP, PSOPed (PSOPed)) where

import Data.Coerce (coerce)
import Plutarch.Internal.CoerceTo (CoerceTo)
import Plutarch.PType (
  PGeneric,
  PHsEf,
  PType,
 )
import Plutarch.Repr (PIsRepr (PReprApplyVal0, PReprC, prfrom, prto), PIsRepr0 (PReprApply), PReprKind (PReprKind))

data PReprSOP'

-- | Representation as a SOP. Requires 'PGeneric'.
type PReprSOP = 'PReprKind PReprSOP'

newtype PSOPed (a :: PType) ef = PSOPed (a ef)

instance PIsRepr0 PReprSOP where
  type PReprApply PReprSOP a = PSOPed a

instance PIsRepr PReprSOP where
  type PReprC PReprSOP a = PGeneric a
  type PReprApplyVal0 PReprSOP a x (PSOPed a PHsEf) = 'PSOPed (CoerceTo (a PHsEf) x)
  prfrom = coerce
  prto = coerce
