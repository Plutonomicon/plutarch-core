-- | Work-around for the lack of partial application of type families
module Plutarch.TyLam where

import Data.Kind (Type)

data TyLamMarker (a :: Type) (b :: Type) = TyLamMarker

type TyLam a b = TyLamMarker a b -> Type

class IsTyLam (f :: TyLam inp out) | f -> inp out where
  type TyLamApp f (x :: inp) :: out

data Composed (f :: TyLam b c) (g :: TyLam a b) (_m :: TyLamMarker a c)

instance (IsTyLam f, IsTyLam g) => IsTyLam (Composed f g) where
  type TyLamApp (Composed f g) x = TyLamApp f (TyLamApp g x)

{-

data Compose (a :: Type) (b :: Type) (c :: Type) (_m :: TyLamMarker)

instance IsTyLam (Compose a b c) (TyLam, TyLam) TyLam where
  type TyLamApp (Compose a b c) '(f, g) = Composed f g

type Map :: (a -> b) -> [a] -> [b]
type family Map f x where
  Map f '[] = '[]
  Map f (x ': xs) = f x ': Map f xs

type Map' :: TyLam -> [a] -> [b]
type family Map' f x where
  Map f '[] = '[]
  Map f (x ': xs) = TyLamApp f x ': Map' f xs

-}
