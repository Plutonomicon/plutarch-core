module Plutarch.Internal.Utilities (
  insertPermute,
  invPermute,
  cmpListEqMod1,
  bringPermute,
  transListEqMod1,
  idxPermute,
  transPermute,
) where

import Data.Type.Equality ((:~:) (Refl))
import Plutarch.Core

insertPermute :: ListEqMod1 xs xs' y -> Permute xs ys -> Permute xs' (y : ys)
insertPermute ListEqMod1N perm = PermuteS ListEqMod1N perm
insertPermute (ListEqMod1S idx) (PermuteS idx' rest) = PermuteS (ListEqMod1S idx') $ insertPermute idx rest

invPermute :: Permute xs ys -> Permute ys xs
invPermute PermuteN = PermuteN
invPermute (PermuteS idx rest) = insertPermute idx $ invPermute rest

cmpListEqMod1 ::
  ListEqMod1 new' new x ->
  ListEqMod1 tail new y ->
  ( forall tail'.
    Either
      (x :~: y, new' :~: tail)
      (ListEqMod1 tail' tail x, ListEqMod1 tail' new' y) ->
    b
  ) ->
  b
cmpListEqMod1 ListEqMod1N ListEqMod1N f = f (Left (Refl, Refl))
cmpListEqMod1 ListEqMod1N (ListEqMod1S idx) f = f (Right (ListEqMod1N, idx))
cmpListEqMod1 (ListEqMod1S idx) ListEqMod1N f = f (Right (idx, ListEqMod1N))
cmpListEqMod1 (ListEqMod1S idx) (ListEqMod1S idx') f = cmpListEqMod1 idx idx' \case
  Left (x, Refl) -> f (Left (x, Refl))
  Right (idx2, idx'2) -> f (Right (ListEqMod1S idx2, ListEqMod1S idx'2))

bringPermute :: ListEqMod1 new' new x -> Permute old new -> Permute old (x : new')
bringPermute ListEqMod1N x = x
bringPermute idx (PermuteS idx' tail) =
  cmpListEqMod1 idx idx' \case
    Left (Refl, Refl) -> PermuteS ListEqMod1N tail
    Right (idx2, idx'2) ->
      PermuteS (ListEqMod1S idx'2) $
        bringPermute idx2 $
          tail

transListEqMod1 ::
  ListEqMod1 xs ys x ->
  ListEqMod1 ys zs y ->
  (forall xs'. ListEqMod1 xs' zs x -> ListEqMod1 xs xs' y -> b) ->
  b
transListEqMod1 idx ListEqMod1N k = k (ListEqMod1S idx) ListEqMod1N
transListEqMod1 ListEqMod1N (ListEqMod1S idx) k = k ListEqMod1N idx
transListEqMod1 (ListEqMod1S idx) (ListEqMod1S idx') k =
  transListEqMod1 idx idx' \idx'' idx''' -> k (ListEqMod1S idx'') (ListEqMod1S idx''')

idxPermute ::
  ListEqMod1 xs' xs x ->
  Permute xs ys ->
  (forall ys'. ListEqMod1 ys' ys x -> Permute xs' ys' -> b) ->
  b
idxPermute ListEqMod1N (PermuteS idx rest) k = k idx rest
idxPermute (ListEqMod1S idx) (PermuteS idx' rest) k =
  idxPermute idx rest \idx'' rest' -> transListEqMod1 idx'' idx' \idx''' idx'''' ->
    k idx''' (PermuteS idx'''' rest')

transPermute :: Permute xs ys -> Permute ys zs -> Permute xs zs
transPermute PermuteN perm = case perm of
  PermuteN -> PermuteN
transPermute (PermuteS idx rest) perm = idxPermute idx perm \idx' perm' -> PermuteS idx' (transPermute rest perm')
