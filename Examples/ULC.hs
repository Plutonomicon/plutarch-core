{-# LANGUAGE PartialTypeSignatures #-}
module Examples.ULC where

import Plutarch.Core
import Plutarch.ULC

import Data.Proxy
import Data.Functor.Identity
import Plutarch.PType

x :: forall (a :: PType) m. (IsPTypeBackend (ULCImpl m) a) => Proxy a -> ULC
x _ = runIdentity . compile (Proxy @(a #-> a)) $ pcon (PLam id)
