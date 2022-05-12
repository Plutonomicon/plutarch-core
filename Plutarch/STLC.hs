module Plutarch.STLC where

import Plutarch.Core
import Plutarch.EType
import Data.Proxy (Proxy (Proxy))

newtype Lvl = Lvl Int

succLvl :: Lvl -> Lvl
succLvl (Lvl l) = Lvl (l + 1)

data SimpleType
  = UnitType
  | ProductType SimpleType SimpleType
  | SumType SimpleType SimpleType
  | FunctionType SimpleType SimpleType
  | NewType String SimpleType

data SimpleTerm
  = App SimpleTerm SimpleTerm
  | Lam SimpleType SimpleTerm
  | Var Lvl
  | MkUnit
  | MkProduct SimpleTerm SimpleTerm
  | Fst SimpleTerm
  | Snd SimpleTerm
  | MkSumLeft SimpleTerm SimpleType
  | MkSumRight SimpleType SimpleTerm
  | Match SimpleTerm SimpleTerm SimpleTerm
  | MkNewtype String SimpleTerm

type ESTLC edsl = (ELC edsl, ESOP edsl)

class TypeInfo (a :: EType) where
  typeInfo :: Proxy a -> SimpleType

instance TypeInfo EUnit where
  typeInfo _ = UnitType

instance (TypeInfo a, TypeInfo b) => TypeInfo (EPair a b) where
  typeInfo _ = ProductType (typeInfo $ Proxy @a) (typeInfo $ Proxy @b)

instance (TypeInfo a, TypeInfo b) => TypeInfo (EEither a b) where
  typeInfo _ = SumType (typeInfo $ Proxy @a) (typeInfo $ Proxy @b)

instance (TypeInfo a, TypeInfo b) => TypeInfo (a #-> b) where
  typeInfo _ = FunctionType (typeInfo $ Proxy @a) (typeInfo $ Proxy @b)

newtype STLCImpl (a :: EType) = STLCImpl { runImpl :: Lvl -> SimpleTerm }

instance EDSL STLCImpl where
  type IsEType STLCImpl = TypeInfo

instance (TypeInfo a, TypeInfo b) => EConstructable STLCImpl (EPair a b) where
  econ (EPair x y) = STLCImpl \lvl -> MkProduct (runImpl x lvl) (runImpl y lvl)
  ematch t f = f $ EPair (STLCImpl \lvl -> Fst $ runImpl t lvl) (STLCImpl \lvl -> Snd $ runImpl t lvl)

instance (TypeInfo a, TypeInfo b) => EConstructable STLCImpl (EEither a b) where
  econ (ELeft x) = STLCImpl \lvl -> MkSumLeft (runImpl x lvl) (typeInfo $ Proxy @b)
  econ (ERight y) = STLCImpl \lvl -> MkSumRight (typeInfo $ Proxy @a) (runImpl y lvl)
  ematch t f = STLCImpl \lvl ->
    Match (runImpl t lvl)
      (runImpl ((elam \left -> f (ELeft left))) lvl)
      (runImpl (elam \right -> f (ERight right)) lvl)

instance (TypeInfo a, TypeInfo b) => EConstructable STLCImpl (a #-> b) where
  econ (ELam f) = STLCImpl \lvl -> Lam (typeInfo $ Proxy @a) $ runImpl (f $ STLCImpl \_ -> Var lvl) (succLvl lvl)
  ematch f g = g $ ELam \x -> STLCImpl \lvl -> runImpl f lvl `App` runImpl x lvl

compile :: (forall edsl. ESTLC edsl => edsl a) -> (SimpleTerm, SimpleType)
compile = undefined
