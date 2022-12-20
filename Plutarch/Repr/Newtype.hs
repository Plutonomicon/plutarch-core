{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Repr.Newtype (PReprNewtype, PNewtyped (..)) where

import Data.Coerce (Coercible, coerce)
import Data.Kind (Constraint)
import Plutarch.Internal.Unimplemented (Error)
import Plutarch.PType (
  PCode,
  PGeneric,
  PType,
  PTypeF,
  type (/$),
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

newtype PNewtyped (a :: PType) ef = PNewtyped (ef /$ a)

instance PIsRepr0 PReprNewtype where
  type PReprApply PReprNewtype a = PNewtyped (GetPNewtype a) -- PReprApply (PReprSort (GetPNewtype a)) (GetPNewtype a)

type C :: PType -> PTypeF -> Constraint
class Coercible (a ef) (ef /$ GetPNewtype a) => C a ef
instance Coercible (a ef) (ef /$ GetPNewtype a) => C a ef

type C' :: PType -> Constraint
class (forall ef. C a ef) => C' a
instance (forall ef. C a ef) => C' a

instance PIsRepr PReprNewtype where
  type
    PReprC PReprNewtype a =
      ( PGeneric a
      , C' a
      , PIsRepr (PReprSort (GetPNewtype a))
      , PReprC (PReprSort (GetPNewtype a)) (GetPNewtype a)
      )
  type PReprApplyVal0 _ _ _ _ = Error "PReprApplyVal0 PReprNewtype is unimplemented"
  prfrom (x :: a ef) = PNewtyped (coerce x)
  prto :: forall a ef. PReprC PReprNewtype a => PNewtyped (GetPNewtype a) ef -> a ef
  prto (PNewtyped (x :: ef /$ GetPNewtype a)) = f (coerce x) -- (prto x :: GetPNewtype a ef) :: a ef
    where
      -- so dumb, should report to GHC bug tracker
      f :: (Coercible (a ef) (ef /$ GetPNewtype a) => b) -> b
      f x = x
