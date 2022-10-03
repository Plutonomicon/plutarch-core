{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Examples.ULC (x, pif, pfls, pid) where

import Data.Functor.Identity (Identity (runIdentity))
import Plutarch.Core
import Plutarch.Prelude
import Plutarch.ULC (PULC, ULC, compile)

pid'' :: forall (a :: PType) edsl. PConstructable edsl (a #-> a) => Term edsl (a #-> a)
pid'' = pcon $ PLam \x -> x

newtype PId' a ef = PId' (ef /$ (a #-> a))
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pid' :: forall (a :: PType) edsl. (PConstructable edsl (a #-> a), PSOP edsl) => Term edsl (PId' a)
pid' = pcon $ PId' pid''

newtype PId ef = PId (ef /$ PForall PId')
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pid :: forall edsl. (PPolymorphic edsl, (forall a. IsPType edsl a => PConstructable edsl (a #-> a)), PSOP edsl) => Term edsl PId
pid = pcon $ PId $ pcon $ PForall pid'

{- | >>> runIdentity . compile $ pid
 Lam (Var 0)
-}
ptru :: (forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable edsl (a #-> b), IsPType edsl a) => Term edsl (a #-> a #-> a)
ptru = pcon $ PLam \t -> pcon $ PLam \_ -> t

{- | >>> runIdentity . compile $ ptru
 Lam (Lam (Var 0))
-}
pfls :: (forall a b. PConstructable edsl (a #-> b)) => Term edsl (a #-> a #-> a)
pfls = pcon $ PLam \_ -> pcon $ PLam \f -> f

{- | >>> runIdentity . compile $ pfls
 Lam (Lam (Var 1))
-}
pif ::
  ( forall a b. PConstructable edsl (a #-> b)
  , IsPType edsl a
  ) =>
  Term edsl ((a #-> a #-> a) #-> a #-> a #-> a)
pif = pcon $ PLam \l -> pcon $ PLam \m -> pcon $ PLam \n -> l # m # n

pnot :: (forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable edsl (a #-> b), IsPType edsl a) => Term edsl ((a #-> a #-> a) #-> (a #-> a #-> a))
pnot = plam \b x y -> b # y # x

t :: forall edsl. PULC edsl => Term edsl (PUnit #-> PUnit #-> PUnit)
t = pnot # ptru

x :: ULC
x = runIdentity . compile @(PUnit #-> PUnit #-> PUnit) $ t

-- PPolymorphic and PSOP is missing
-- y :: ULC
-- y = runIdentity . compile $ pid
