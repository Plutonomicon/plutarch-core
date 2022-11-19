{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Repr.Newtype (PReprNewtype) where

import Data.Coerce (Coercible, coerce)
import Plutarch.Internal.Unimplemented (Error, Unimplemented)
import Plutarch.PType (
  PCode,
  PGeneric,
  PType,
 )
import Plutarch.Repr (
  PIsRepr (PReprApplyVal0, PReprC, prfrom, prto),
  PIsRepr0 (PReprApply),
  PReprKind (PReprKind),
  PReprSort,
 )

type family GetPNewtype' (a :: [[PType]]) :: PType where
  GetPNewtype' '[ '[a]] = a

type family GetPNewtype (a :: PType) :: PType where
  GetPNewtype a = GetPNewtype' (PCode a)

data PReprNewtype'

-- | Representation as a Newtype. Requires 'PGeneric'.
type PReprNewtype = 'PReprKind PReprNewtype'

instance PIsRepr0 PReprNewtype where
  type PReprApply PReprNewtype a = PReprApply (PReprSort (GetPNewtype a)) (GetPNewtype a)

instance PIsRepr PReprNewtype where
  type
    PReprC PReprNewtype a =
      ( PGeneric a
      , Coercible a (GetPNewtype a)
      , PIsRepr (PReprSort (GetPNewtype a))
      , PReprC (PReprSort (GetPNewtype a)) (GetPNewtype a)
      )
  type PReprApplyVal0 _ _ _ _ = Error "PReprApplyVal0 PReprNewtype"
  prfrom (x :: a ef) = prfrom (coerce x :: GetPNewtype a ef)
  prto :: forall a ef. PReprC PReprNewtype a => PReprApply PReprNewtype a ef -> a ef
  prto x = coerce $ (prto x :: GetPNewtype a ef) :: a ef
