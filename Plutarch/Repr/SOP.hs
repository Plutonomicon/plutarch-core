{-# LANGUAGE FlexibleInstances #-}

module Plutarch.Repr.SOP (PReprSOP, PSOPed (PSOPed)) where

import Plutarch.Repr (
  PIsRepr0 (PReprApply, PReprIsPType), PIsRepr (PReprApplyVal0, prIsPType, PReprC))
import Plutarch.Repr (PReprKind (PReprKind))
import Plutarch.Internal.Unimplemented (Unimplemented, Error)
import Plutarch.PType (
  PGeneric,
  PType,
 )

data PReprSOP'

-- | Representation as a SOP. Requires 'PGeneric'.
type PReprSOP = 'PReprKind PReprSOP'

newtype PSOPed (a :: PType) ef = PSOPed (a ef)

instance PIsRepr0 PReprSOP where
  type PReprApply PReprSOP a = PSOPed a
  -- Maybe: `Known x => IsPType' edsl x`
  type PReprIsPType _ _ _ _ = Unimplemented "PReprIsPType PReprSOP"

instance PIsRepr PReprSOP where
  type PReprC PReprSOP a = PGeneric a
  type PReprApplyVal0 _ _ _ _ = Error "PReprApplyVal0 PReprSOP"
  prIsPType _ _ _ = error "unimplemented"
