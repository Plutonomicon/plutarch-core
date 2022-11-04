{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Generics (PIsSOP (..)) where

import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import GHC.TypeLits (ErrorMessage (ShowType, Text, (:$$:)), TypeError)
import Generics.SOP qualified as SOP
import Generics.SOP.GGP qualified as SOPG
import Plutarch.Core (IsPType, PConcrete, PDSLKind, Term)
import Plutarch.PType (PGeneric, PType)
import Plutarch.Repr (PReprSort)
import Plutarch.Repr.SOP (PReprSOP)

data PIsProductR (edsl :: PDSLKind) (a :: [Type]) = forall inner.
  (SOP.All (IsPType edsl) inner, SOP.SListI a) =>
  PIsProductR
  { inner :: Proxy inner
  , to :: SOP.NP (Term edsl) inner -> SOP.NP SOP.I a
  , from :: SOP.NP SOP.I a -> SOP.NP (Term edsl) inner
  }

class PIsProduct (edsl :: PDSLKind) (a :: [Type]) where
  pisProduct :: Proxy edsl -> Proxy a -> PIsProductR edsl a

instance PIsProduct edsl '[] where
  pisProduct _ _ =
    PIsProductR
      { inner = Proxy @'[]
      , to = \SOP.Nil -> SOP.Nil
      , from = \SOP.Nil -> SOP.Nil
      }

-- TODO: Replace with https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0433-unsatisfiable.rst
-- TODO: Possibly show type in question?
instance
  {-# OVERLAPPABLE #-}
  ( TypeError
      ( Text "Can not embed type that contains: "
          :$$: ShowType a
      )
  , PIsProduct edsl as
  ) =>
  PIsProduct edsl (a : as)
  where
  pisProduct edsl _ = error "unreachable" $ pisProduct edsl (Proxy @as)

instance (IsPType edsl a, PIsProduct edsl as) => PIsProduct edsl (Term edsl a : as) where
  pisProduct edsl _ =
    let prev = pisProduct edsl (Proxy @as)
     in case prev of
          PIsProductR {inner = _ :: Proxy asi, to, from} ->
            PIsProductR
              { inner = Proxy @(a : asi)
              , to = \(x SOP.:* xs) -> SOP.I x SOP.:* to xs
              , from = \(SOP.I x SOP.:* xs) -> x SOP.:* from xs
              }

data PIsSumR (edsl :: PDSLKind) (a :: [[Type]]) = forall inner.
  (SOP.All2 (IsPType edsl) inner, SOP.SListI2 a) =>
  PIsSumR
  { inner :: Proxy inner
  , to :: SOP.SOP (Term edsl) inner -> SOP.SOP SOP.I a
  , from :: SOP.SOP SOP.I a -> SOP.SOP (Term edsl) inner
  }

class PIsSum (edsl :: PDSLKind) (a :: [[Type]]) where
  pisSum :: Proxy edsl -> Proxy a -> PIsSumR edsl a

instance PIsSum edsl '[] where
  pisSum _ _ =
    PIsSumR
      { inner = Proxy @'[]
      , to = \case {}
      , from = \case {}
      }

instance (PIsProduct edsl a, PIsSum edsl as) => PIsSum edsl (a : as) where
  pisSum edsl _ =
    case pisProduct edsl (Proxy @a) of
      PIsProductR {inner = _ :: Proxy innerh, to = toh, from = fromh} ->
        case pisSum edsl (Proxy @as) of
          PIsSumR {inner = _ :: Proxy innert, to = tot, from = fromt} ->
            PIsSumR
              { inner = Proxy @(innerh : innert)
              , to = \case
                  SOP.SOP (SOP.Z x) -> SOP.SOP $ SOP.Z $ toh x
                  SOP.SOP (SOP.S x) -> case tot $ SOP.SOP $ x of SOP.SOP y -> SOP.SOP (SOP.S y)
              , from = \case
                  SOP.SOP (SOP.Z x) -> SOP.SOP $ SOP.Z $ fromh x
                  SOP.SOP (SOP.S x) -> case fromt $ SOP.SOP $ x of SOP.SOP y -> SOP.SOP (SOP.S y)
              }

class
  ( PGeneric a
  , PIsSum edsl (SOPG.GCode (PConcrete edsl a))
  , PReprSort a ~ PReprSOP
  ) =>
  PIsSOP (edsl :: PDSLKind) (a :: PType)
  where
  psop :: Proxy edsl -> Proxy a -> PIsSumR edsl (SOPG.GCode (PConcrete edsl a))
instance
  ( PGeneric a
  , PIsSum edsl (SOPG.GCode (PConcrete edsl a))
  , PReprSort a ~ PReprSOP
  ) =>
  PIsSOP (edsl :: PDSLKind) (a :: PType)
  where
  psop edsl _ = pisSum edsl Proxy
