{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Repr (PHasRepr (..), PReprKind (..), PIsRepr0 (..), PIsRepr (..), PRepr) where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import Generics.SOP.Type.Metadata (DatatypeInfo (ADT, Newtype))
import {-# SOURCE #-} Plutarch.Core (IsPTypePrim, IsPTypePrimData, PDSLKind, isPTypePrim)
import Plutarch.PType (
  PDatatypeInfoOf,
  PHs,
  PPType,
  PType,
 )
import {-# SOURCE #-} Plutarch.Repr.Newtype (PReprNewtype)
import {-# SOURCE #-} Plutarch.Repr.SOP (PReprSOP)

newtype PReprKind = PReprKind Type

type family F (a :: DatatypeInfo) :: PReprKind where
  F ( 'ADT _ _ _ _) = PReprSOP
  F ( 'Newtype _ _ _) = PReprNewtype

class PHasRepr (a :: PType) where
  type PReprSort a :: PReprKind

  -- FIXME: Use more direct check for better performance
  type PReprSort a = F (PDatatypeInfoOf a)

class PIsRepr0 (r :: PReprKind) where
  type PReprApply r (a :: PType) :: PType

{- | A "representation" of a type. This defines how a user-visible type
 is mapped onto a type in the backend.
-}
class PIsRepr0 r => PIsRepr (r :: PReprKind) where
  type PReprApplyVal0 r (a :: PType) (x :: PHs a) (out :: Type) :: out -- out ~ PHs (PReprApply r a)
  type PReprC r (a :: PType) :: Constraint
  prfrom :: forall a ef. (PReprC r a, PReprSort a ~ r) => a ef -> PReprApply r a ef
  prto :: forall a ef. (PReprC r a, PReprSort a ~ r) => PReprApply r a ef -> a ef

type PReprApplyVal :: forall (r :: PReprKind) -> forall (a :: PType) -> PHs a -> PHs (PReprApply r a)
type PReprApplyVal r a x = PReprApplyVal0 r a x (PHs (PReprApply r a))

data PReprPPType'

-- | The "identity" representation.
type PReprPPType = 'PReprKind PReprPPType'

instance PIsRepr0 PReprPPType where
  type PReprApply PReprPPType PPType = PPType

instance PIsRepr PReprPPType where
  type PReprApplyVal0 PReprPPType PPType x _ = PReprApply (PReprSort x) x
  type PReprC PReprPPType a = a ~ PPType
  prfrom = error "invalid"
  prto = error "invalid"

instance PHasRepr PPType where
  type PReprSort _ = PReprPPType

type PRepr :: forall (a :: PType). PHs a -> PHs (PReprApply (PReprSort a) a)
type PRepr (x :: PHs a) = PReprApplyVal (PReprSort a) a x
