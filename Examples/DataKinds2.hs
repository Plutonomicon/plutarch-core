module Examples.DataKinds2 (F' (..)) where

import Plutarch.Prelude

data PProxy (x :: PHs a) ef = PProxy
  deriving stock (Generic)
instance PHasRepr (PProxy x) where type PReprSort _ = PReprSOP

newtype PIdentity a ef = PIdentity (ef /$ a)
  deriving stock (Generic)
instance PHasRepr (PIdentity a) where type PReprSort _ = PReprSOP

newtype F' a x ef = F' (ef /$ PProxy x #-> PUnit)

{-
newtype F (a :: PType) ef = F (ef /$ PForall (F' a))

f :: PForall F
f = pcon $ PForall $$ F $$ PForall $$ F' $ elam \_ -> pcon PUnit

--g :: Proxy x -> ()
--g (Proxy @x) = f (Proxy @(Identity x))

g :: PForall F
g = pcon $ PForall $$ F $$ PForall $$ F' $ elam \(x :: Term edsl (PProxy x)) ->
  pmatch f \PForall f ->
  pmatch f \F f ->
  pmatch f \PForall f ->
  pmatch f \F' f ->
  f # (pcon PProxy :: Term edsl (PProxy ('PIdentity x)))
-}
