module Plutarch.PList where

import Plutarch.Core
import Plutarch.EType
import GHC.Generics

data PListF a self ef
  = PNil
  | PCons (ef /$ a) (ef /$ self)
  deriving stock Generic
  deriving anyclass EIsNewtype

newtype PList edsl a = PList (Term edsl (EFix (PListF a)))
  deriving stock Generic

mkPList :: (ESOP edsl, IsEType edsl a, _) => EConcrete edsl (PListF a (EFix (PListF a))) -> PList edsl a
mkPList = PList . econ . EFix . econ

pnil :: (ESOP edsl, IsEType edsl a, _) => PList edsl a
pnil = mkPList PNil

pcons :: (ESOP edsl, IsEType edsl a, _) => Term edsl a -> PList edsl a -> PList edsl a
pcons a (PList as) = mkPList $ PCons a as