module Plutarch.Helpers (IsPType1, IsPType2, IsPType3) where

import Plutarch.Core (IsPType)

type IsPType1 e f = forall a. IsPType e a => IsPType e (f a)
type IsPType2 e f = forall b. IsPType e b => IsPType1 e (f b)
type IsPType3 e f = forall c. IsPType e c => IsPType2 e (f c)

type PConstructable1 e f = forall a. IsPType e a => PConstructable e (f a)
type PConstructable2 e f = forall b. IsPType e b => PConstructable1 e (f b)
type PConstructable3 e f = forall c. IsPType e c => PConstructable2 e (f c)

plet :: forall e a b. (HasCallStack, PConstructable e (PLet a), IsPType e b) => T e a -> TC e (T e a)
plet x f = pmatch (pcon $ PLet x) \(PLet y) -> f y

pbind :: forall e a b. (HasCallStack, PConstructable e (PLet a), IsPType e b) => T e a -> ETC e (T e a)
pbind x f = pmatch (pcon $ PLet x) \(PLet y) -> f y

(#) :: (HasCallStack, PLC e, IsPType e a, IsPType e b) => T e (a #-> b) -> T e a -> T e b
(#) f x = pmatch f (\(PLam f') -> f' x)

infixl 8 #
