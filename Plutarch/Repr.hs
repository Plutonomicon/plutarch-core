{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Repr (PHasRepr (..), PReprKind (..), PIsRepr0 (..), PIsRepr (..), PRepr) where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import {-# SOURCE #-} Plutarch.Core (IsPTypePrim, PDSLKind)
import Plutarch.PType (
  PHs,
  PPType,
  PType,
 )
import {-# SOURCE #-} Plutarch.Repr.SOP (PReprSOP)

newtype PReprKind = PReprKind Type

class PHasRepr (a :: PType) where
  type PReprSort a :: PReprKind
  type PReprSort _ = PReprSOP

class PIsRepr0 (r :: PReprKind) where
  type PReprApply r (a :: PType) :: PType
  type PReprIsPType r (a :: PType) (edsl :: PDSLKind) (x :: PHs a) :: Constraint

{- | A "representation" of a type. This defines how a user-visible type
 is mapped onto a type in the backend.
-}
class PIsRepr0 r => PIsRepr (r :: PReprKind) where
  type PReprApplyVal0 r (a :: PType) (x :: PHs a) (out :: Type) :: out -- out ~ PHs (PReprApply r a)
  type PReprC r (a :: PType) :: Constraint
  prfrom :: forall a ef. (PReprC r a, PReprSort a ~ r) => a ef -> PReprApply r a ef
  prto :: forall a ef. (PReprC r a, PReprSort a ~ r) => PReprApply r a ef -> a ef
  prIsPType ::
    forall edsl a (x :: PHs a) y.
    (PReprC r a, PReprSort a ~ r, PReprIsPType r a edsl x) =>
    Proxy edsl ->
    Proxy x ->
    -- (forall a' (x' :: PHs a'). IsPTypePrim edsl x' => Proxy x' -> (forall p. p x -> p x') -> y) ->
    (IsPTypePrim edsl (PReprApplyVal r a x) => y) ->
    y

type PReprApplyVal :: forall (r :: PReprKind) -> forall (a :: PType) -> PHs a -> PHs (PReprApply r a)
type PReprApplyVal r a x = PReprApplyVal0 r a x (PHs (PReprApply r a))

data PReprPPType'

-- | The "identity" representation.
type PReprPPType = 'PReprKind PReprPPType'

instance PIsRepr0 PReprPPType where
  type PReprApply PReprPPType PPType = PPType
  type PReprIsPType PReprPPType PPType edsl x = IsPTypePrim edsl (PReprApply (PReprSort x) x)

instance PIsRepr PReprPPType where
  type PReprApplyVal0 PReprPPType PPType x _ = PReprApply (PReprSort x) x
  type PReprC PReprPPType a = a ~ PPType
  prfrom = error "invalid"
  prto = error "invalid"
  prIsPType _ _ f = f

instance PHasRepr PPType where
  type PReprSort _ = PReprPPType

type PRepr :: forall (a :: PType). PHs a -> PHs (PReprApply (PReprSort a) a)
type PRepr (x :: PHs a) = PReprApplyVal (PReprSort a) a x
