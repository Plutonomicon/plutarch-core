{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Frontends.LC (PLC, PPolymorphic) where

import Data.Kind (Constraint)
import Plutarch.Core (IsPType, IsPTypePrim, PConstructablePrim, PDSLKind)
import Plutarch.Frontends.Data (PForall, type (#->) (PLam))
import Plutarch.PType (PHs, PPType, PType)

class IsPTypePrim edsl x => IsPTypePrim' edsl x
instance IsPTypePrim edsl x => IsPTypePrim' edsl x

type PLC :: PDSLKind -> Constraint
type PLC edsl = forall a b. (IsPType edsl a, IsPType edsl b) => PConstructablePrim edsl (a #-> b)

type PPolymorphic :: PDSLKind -> Constraint
class
  ( forall a (f :: PHs a -> PType).
    IsPType edsl ( 'PLam f :: PHs (a #-> PPType)) =>
    PConstructablePrim edsl (PForall f)
  , forall a b (f :: PHs a -> PHs b).
    (IsPType edsl a, IsPType edsl b, forall (x :: PHs a). IsPType edsl x => IsPType edsl (f x)) =>
    IsPTypePrim' edsl ( 'PLam f :: PHs (a #-> b))
  ) =>
  PPolymorphic edsl
