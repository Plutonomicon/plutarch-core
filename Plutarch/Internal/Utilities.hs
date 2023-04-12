module Plutarch.Internal.Utilities where

import Plutarch.Core

insertPermute :: ListEqMod1 xs xs' y -> Permute xs ys -> Permute xs' (y : ys)
insertPermute ListEqMod1N perm = PermuteS ListEqMod1N perm
insertPermute (ListEqMod1S idx) (PermuteS idx' rest) = PermuteS (ListEqMod1S idx') $ insertPermute idx rest

invPermute :: Permute xs ys -> Permute ys xs
invPermute PermuteN = PermuteN
invPermute (PermuteS idx rest) = insertPermute idx $ invPermute rest
