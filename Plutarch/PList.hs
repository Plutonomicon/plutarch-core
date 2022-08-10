module Plutarch.PList where

import GHC.Generics
import Plutarch.Core
import Plutarch.EType

data PListF a self ef
  = PNil
  | PCons (ef /$ a) (ef /$ self)
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

newtype PList a ef = PList {unPList :: ef /$ EFix (PListF a)}
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

mkPList ::
  ( ESOP edsl
  , IsEType edsl a
  , IsEType edsl (EFix (PListF a))
  , EConstructable edsl (EFix (PListF a))
  ) =>
  EConcrete edsl (PListF a (EFix (PListF a))) ->
  Term edsl (PList a)
mkPList = econ . PList . econ . EFix . econ

pnil ::
  ( ESOP edsl
  , IsEType edsl a
  , IsEType edsl (EFix (PListF a))
  , EConstructable edsl (EFix (PListF a))
  ) =>
  Term edsl (PList a)
pnil = mkPList PNil

pcons ::
  ( ESOP edsl
  , IsEType edsl a
  , IsEType edsl (EFix (PListF a))
  , EConstructable edsl (EFix (PListF a))
  ) =>
  Term edsl a ->
  Term edsl (PList a) ->
  Term edsl (PList a)
pcons a las = mkPList $ PCons a (ematch las unPList)
