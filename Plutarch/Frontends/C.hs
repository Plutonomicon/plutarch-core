module Plutarch.Frontends.C (PInt) where

import Plutarch.Repr (PHasRepr, PReprSort)
import Plutarch.Repr.Primitive (PReprPrimitive)

data PInt ef
instance PHasRepr PInt where type PReprSort _ = PReprPrimitive

data PProcedure (a :: PType) (b :: PType) (lang :: PDSLKind -> Constraint) (ef :: PTypeF)

class
  ( PHarvard e
  , Num (Term e PInt)
  ) => PC e
  pcffi :: IsPType e a => Text -> Term e a
