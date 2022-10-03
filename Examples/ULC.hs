{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Examples.ULC where

import Plutarch.Core
import Plutarch.Prelude
import Plutarch.ULC ( ULC, compile )
import Data.Functor.Identity ( Identity(runIdentity) )

pid :: (PConstructable edsl (PUnit #-> PUnit)) => Term edsl (PUnit #-> PUnit)
pid = pcon $ PLam \x -> x

-- | >>> runIdentity . compile $ pid
-- Lam (Var 0)

ptru ::
  ( PConstructable edsl (PUnit #-> PUnit)
  , PConstructable edsl (PUnit #-> PUnit #-> PUnit)
  ) => Term edsl (PUnit #-> PUnit #-> PUnit)
ptru = pcon $ PLam \t -> pcon $ PLam \_ -> t

-- | >>> runIdentity . compile $ ptru
-- Lam (Lam (Var 0))

pfls ::
  ( PConstructable edsl (PUnit #-> PUnit)
  , PConstructable edsl (PUnit #-> PUnit #-> PUnit)
  ) => Term edsl (PUnit #-> PUnit #-> PUnit)
pfls = pcon $ PLam \_ -> pcon $ PLam \f -> f

-- | >>> runIdentity . compile $ pfls
-- Lam (Lam (Var 1))

pif ::
  forall edsl.
  ( PLC edsl
  , PConstructable edsl (PUnit #-> PUnit)
  , PConstructable edsl (PUnit #-> PUnit #-> PUnit)
  , PConstructable edsl ((PUnit #-> PUnit #-> PUnit) #-> PUnit #-> PUnit #-> PUnit)
  , IsPType edsl PUnit
  ) => Term edsl ((PUnit #-> PUnit #-> PUnit) #-> PUnit #-> PUnit #-> PUnit)
pif = pcon $ PLam \l -> pcon $ PLam \m -> pcon $ PLam \n -> l # m # n

pnot ::
  ( PLC edsl
  , PConstructable edsl (PUnit #-> PUnit)
  , PConstructable edsl (PUnit #-> PUnit #-> PUnit)
  , PConstructable edsl ((PUnit #-> PUnit #-> PUnit) #-> PUnit #-> PUnit #-> PUnit)
  , IsPType edsl PUnit
  ) => Term edsl ((PUnit #-> PUnit #-> PUnit) #-> PUnit #-> PUnit #-> PUnit)
pnot = plam \b x y -> b # y # x

-- | >>> runIdentity . compile $ pnot # ptru
-- App (Lam (Lam (Lam (App (App (Var 0) (Var 2)) (Var 1))))) (Lam (Lam (Var 0)))
