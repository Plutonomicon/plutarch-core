{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Repr.Newtype (PReprNewtype) where

import Plutarch.Repr (
  PIsRepr0 (PReprApply, PReprIsPType), PIsRepr (PReprApplyVal0, prIsPType, PReprC))
import Plutarch.Repr (PReprKind (PReprKind))
import Plutarch.Internal.Unimplemented (Unimplemented, Error)
import Plutarch.PType (
  PGeneric,
  PType,
  PCode,
 )

type family GetPNewtype' (a :: [[PType]]) :: PType where
  GetPNewtype' '[ '[a]] = a

type family GetPNewtype (a :: PType) :: PType where
  GetPNewtype a = GetPNewtype' (PCode a)

data PReprNewtype'

-- | Representation as a Newtype. Requires 'PGeneric'.
type PReprNewtype = 'PReprKind PReprNewtype'

instance PIsRepr0 PReprNewtype where
  type PReprApply PReprNewtype a = GetPNewtype a
  type PReprIsPType _ _ _ _ = Unimplemented "PReprIsPType PReprNewtype"

instance PIsRepr PReprNewtype where
  type PReprC PReprNewtype a = PGeneric a
  type PReprApplyVal0 _ _ _ _ = Error "PReprApplyVal0 PReprNewtype"
  prIsPType _ _ _ = error "unimplemented"
