module Examples.DataKinds2 (F' (..)) where

import Plutarch.Prelude

data EProxy (x :: EHs a) ef = EProxy
  deriving stock (Generic)
instance EHasRepr (EProxy x) where type EReprSort _ = EReprSOP

newtype EIdentity a ef = EIdentity (ef /$ a)
  deriving stock (Generic)
instance EHasRepr (EIdentity a) where type EReprSort _ = EReprSOP

newtype F' a x ef = F' (ef /$ EProxy x #-> EUnit)

{-
newtype F (a :: EType) ef = F (ef /$ EForall (F' a))

f :: EForall F
f = econ $ EForall $$ F $$ EForall $$ F' $ elam \_ -> econ EUnit

--g :: Proxy x -> ()
--g (Proxy @x) = f (Proxy @(Identity x))

g :: EForall F
g = econ $ EForall $$ F $$ EForall $$ F' $ elam \(x :: Term edsl (EProxy x)) ->
  ematch f \EForall f ->
  ematch f \F f ->
  ematch f \EForall f ->
  ematch f \F' f ->
  f # (econ EProxy :: Term edsl (EProxy ('EIdentity x)))
-}
