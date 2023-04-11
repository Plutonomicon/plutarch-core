module Plutarch.Frontends.Untyped (PUntyped (..)) where

import Plutarch.Core (IsPType, IsPTypeData, PDSL, Term)

class PDSL e => PUntyped e where
  punsafeCoerce :: (IsPType e a, IsPType e b) => Term e a -> Term e b
  punsafeGiveType :: IsPTypeData e x
