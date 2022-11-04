{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Repr.Primitive (PReprPrimitive) where

import Plutarch.Core (IsPType')
import Plutarch.Repr (
  PIsRepr0 (PReprApply, PReprIsPType), PIsRepr (PReprApplyVal0, prIsPType, PReprC, prto, prfrom))
import Plutarch.Repr (PReprKind (PReprKind))
import Plutarch.PType (PHs', PHs, PPType)
import Plutarch.Internal.CoerceTo (CoerceTo)

data PReprPrimitive'

-- | The "identity" representation.
type PReprPrimitive = 'PReprKind PReprPrimitive'

instance PIsRepr0 PReprPrimitive where
  type PReprApply PReprPrimitive a = a
  type PReprIsPType PReprPrimitive a edsl x = (PReprApplyVal0 PReprPrimitive a x (PHs a) ~ x, IsPType' edsl x)

instance PIsRepr PReprPrimitive where
  -- equivalent to:
  -- type PReprApplyVal0 PReprPrimitive a x _ = x
  type PReprApplyVal0 PReprPrimitive PPType x _ = x
  type PReprApplyVal0 PReprPrimitive a x (PHs' a) = CoerceTo (PHs' a) x
  type PReprC PReprPrimitive _ = ()
  prto = id
  prfrom = id
  prIsPType _ _ f = f
