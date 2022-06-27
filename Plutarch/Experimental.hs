module Plutarch.Experimental (EEq (..), ESingle (..)) where

import Plutarch.EType (EHs, EIsNewtype (EIsNewtype'), EType, type (/$))

data EEq (x :: a) (y :: a) ef where
    ERefl :: EEq x x ef
instance EIsNewtype (EEq x y) where type EIsNewtype' _ = False

type ESingle :: forall (a :: EType). EHs a -> EType
newtype ESingle (x :: EHs a) ef = ESingle (ef /$ a)
instance EIsNewtype (ESingle x) where type EIsNewtype' _ = False
