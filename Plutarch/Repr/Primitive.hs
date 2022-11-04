{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Repr.Primitive (PReprPrimitive) where

import Plutarch.Core (IsPType')
import Plutarch.Internal.CoerceTo (CoerceTo)
import Plutarch.PType (PHs, PHs', PPType)
import Plutarch.Repr (PIsRepr (PReprApplyVal0, PReprC, prIsPType, prfrom, prto), PIsRepr0 (PReprApply, PReprIsPType), PReprKind (PReprKind))

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
