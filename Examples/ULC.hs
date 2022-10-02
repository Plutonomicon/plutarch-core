{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Examples.ULC where

import Plutarch.Prelude
import Plutarch.ULC ( ULC, compile )
import Data.Functor.Identity ( Identity(runIdentity) )

pid :: (forall a b. PConstructable edsl (a #-> b)) => Term edsl (a #-> a)
pid = pcon $ PLam \x -> x

-- | >>> runIdentity . compile $ pid
-- Lam (Var 0)

ptru :: (forall a b. PConstructable edsl (a #-> b)) => Term edsl (a #-> a #-> a)
ptru = pcon $ PLam \t -> pcon $ PLam \_ -> t

-- | >>> runIdentity . compile $ ptru
-- Lam (Lam (Var 0))

pfls :: (forall a b. PConstructable edsl (a #-> b)) => Term edsl (a #-> a #-> a)
pfls = pcon $ PLam \_ -> pcon $ PLam \f -> f

-- | >>> runIdentity . compile $ pfls
-- Lam (Lam (Var 1))

pif ::
  ( forall a b. PConstructable edsl (a #-> b)
  , IsPType edsl a
  ) => Term edsl ((a #-> a #-> a) #-> a #-> a #-> a)
pif = pcon $ PLam \l -> pcon $ PLam \m -> pcon $ PLam \n -> l # m # n

pnot :: (forall a b. PConstructable edsl (a #-> b)) => Term edsl (((a #-> a #-> a) #-> (a #-> a #-> a) #-> (a #-> a #-> a)) #-> (a #-> a #-> a))
pnot = pcon $ PLam \x -> x # pfls # ptru

x :: ULC
x = runIdentity . compile $ pnot # ptru
