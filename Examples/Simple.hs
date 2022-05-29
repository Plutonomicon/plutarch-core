module Examples.Simple where
  
import Plutarch.Core
--import Plutarch.STLC
import Plutarch.EType
import GHC.Generics (Generic)

type ESystemF edsl = (ELC edsl, EPolymorphic edsl, ESOP edsl)

data EId a f = EId (Ef f (a #-> a)) deriving stock Generic deriving anyclass EIsNewtype

data EBool (f :: ETypeF) = ETrue | EFalse deriving stock Generic deriving anyclass EIsNewtype

data Bad (f :: ETypeF) = Bad Integer deriving stock Generic deriving anyclass EIsNewtype

badex :: forall edsl. (ESystemF edsl) => Term edsl Bad
badex = econ $ Bad 100

f :: EGeneric (EId a) => ()
f = ()

g :: ()
g = f

ex :: forall a edsl. (IsEType edsl a, ESystemF edsl) => Term edsl (EId a)
ex = econ $ EId ex'

ex' :: forall a edsl. (IsEType edsl a, ESystemF edsl) => Term edsl (a #-> a)
ex' = elam \(x :: Term edsl a) -> x
--
--expoly :: forall edsl. ESystemF edsl => Term edsl (EForall (IsEType edsl) EId)
--expoly = econ $ EForall ex

{-
exfailwithmessage :: forall a. (EEmbeds IO edsl, IsEType edsl a, EPLC edsl, EPartial edsl) => Term edsl a
exfailwithmessage = eembed $ do
  msg <- readFile "something"
  pure $ etraceError (fromString msg)
-}
