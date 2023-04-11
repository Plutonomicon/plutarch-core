{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Repr.Primitive (PReprPrimitive) where

import Plutarch.Internal.CoerceTo (CoerceTo)
import Plutarch.PType (PHs)
import Plutarch.Repr (PIsRepr (PReprApplyVal0, PReprC, prfrom, prto), PIsRepr0 (PReprApply), PReprKind (PReprKind))

data PReprPrimitive'

-- | The "identity" representation.
type PReprPrimitive = 'PReprKind PReprPrimitive'

instance PIsRepr0 PReprPrimitive where
  type PReprApply PReprPrimitive a = a

instance PIsRepr PReprPrimitive where
  type PReprApplyVal0 PReprPrimitive (x :: PHs _) a' = CoerceTo a' x
  type PReprC PReprPrimitive _ = ()
  prto = id
  prfrom = id
