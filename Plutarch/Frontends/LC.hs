{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Frontends.LC (PLC, PPolymorphic) where

import Data.Kind (Constraint)
import Plutarch.Core (IsPType, PConstructable, PDSLKind, PHs)
import Plutarch.Frontends.Data (PForall, type (#->) (PLam))
import Plutarch.PType (PPType, PType)

type PLC :: PDSLKind -> Constraint
type PLC edsl = forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable edsl (a #-> b)

type PPolymorphic :: PDSLKind -> Constraint
type PPolymorphic edsl =
  ( forall a (f :: PHs a -> PType). IsPType edsl ( 'PLam f :: PHs (a #-> PPType)) => PConstructable edsl (PForall f)
  , forall a b (f :: PHs a -> PHs b). (forall xVd. IsPType edsl xVd => IsPType edsl (f xVd)) => IsPType edsl ( 'PLam f :: PHs (a #-> b))
  )
