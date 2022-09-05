module Plutarch.PList where

import GHC.Generics
import Plutarch.Core
import Plutarch.PType

data PListF a self ef
  = PNil
  | PCons (ef /$ a) (ef /$ self)
  deriving stock (Generic)
  deriving anyclass PHasRepr

newtype PList a ef = PList {unPList :: ef /$ PFix (PListF a)}
  deriving stock (Generic)
  deriving anyclass PHasRepr

mkPList ::
  ( PSOP edsl
  , IsPType edsl a
  , IsPType edsl (PFix (PListF a))
  , PConstructable edsl (PFix (PListF a))
  ) =>
  PConcrete edsl (PListF a (PFix (PListF a))) ->
  Term edsl (PList a)
mkPList = pcon . PList . pcon . PFix . pcon

pnil ::
  ( PSOP edsl
  , IsPType edsl a
  , IsPType edsl (PFix (PListF a))
  , PConstructable edsl (PFix (PListF a))
  ) =>
  Term edsl (PList a)
pnil = mkPList PNil

pcons ::
  ( PSOP edsl
  , IsPType edsl a
  , IsPType edsl (PFix (PListF a))
  , PConstructable edsl (PFix (PListF a))
  ) =>
  Term edsl a ->
  Term edsl (PList a) ->
  Term edsl (PList a)
pcons a las = mkPList $ PCons a (pmatch las unPList)
