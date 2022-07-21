{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Optics.Optional where

import Plutarch.Core

import Plutarch.Optics.Iso
import Plutarch.Optics.Lens
import Plutarch.Optics.Optic
import Plutarch.Optics.Prism
import Plutarch.Optics.Profunctor

type POptional edsl s t a b = forall p. IsPOptional edsl p => POptic p s t a b

class (IsPLens edsl p, IsPPrism edsl p) => IsPOptional edsl p

newtype UnpackedPOptional edsl a b s t
  = UnpackedPOptional
  { withUnpackedPOptional ::
    forall r.
      (
        (s :--> EEither t a) edsl ->
        (Term edsl s -> Term edsl b -> Term edsl t) ->
        r
      ) -> r
  }

unpackedPOptional ::
  (s :--> EEither t a) edsl ->
  (Term edsl s -> Term edsl b -> Term edsl t) ->
  UnpackedPOptional edsl a b s t
unpackedPOptional prj set = UnpackedPOptional $ \k -> k prj set

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  PProfunctor edsl (UnpackedPOptional edsl a b) where
  pdimap f g (UnpackedPOptional r) =
    r $ \prj set ->
      unpackedPOptional
        (peither (pleft . g) pright . prj . f)
        (unTermF . prmap g . TermF . set . f)

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  PStrong edsl (UnpackedPOptional edsl a b) where
  pfirst' (UnpackedPOptional r) =
    r $ \prj set ->
      unpackedPOptional
        (\tp -> ematch tp \(EPair a c) -> ematch (prj a) \case
          ELeft b -> pleft (econ $ EPair b c)
          ERight a -> pright a)
        (\tp b -> ematch tp \(EPair a c) -> econ $ EPair (set a b) c)

  psecond' (UnpackedPOptional r) =
    r $ \prj set ->
      unpackedPOptional
        (\tp -> ematch tp \(EPair c a) -> ematch (prj a) \case
          ELeft b -> pleft (econ $ EPair c b)
          ERight a -> pright a)
        (\tp b -> ematch tp \(EPair a c) -> econ $ EPair a (set c b))

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  PChoice edsl (UnpackedPOptional edsl a b) where
    pleft' (UnpackedPOptional r) =
      r $ \prj set ->
        unpackedPOptional
          (peither
            (peither (pleft . pleft) pright . prj)
            (pleft . pright)
          )
          (\e b -> ematch e \case
            ELeft a -> pleft (set a b)
            ERight c -> pright c)
  
    pright' (UnpackedPOptional r) =
      r $ \prj set ->
        unpackedPOptional
          (peither
            (pleft . pleft)
            (peither (pleft . pright) pright . prj)
          )
          (\e b -> ematch e \case
            ELeft a -> pleft a
            ERight c -> pright (set c b))

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  IsPIso edsl (UnpackedPOptional edsl a b)

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  IsPLens edsl (UnpackedPOptional edsl a b)

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  IsPPrism edsl (UnpackedPOptional edsl a b)

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  IsPOptional edsl (UnpackedPOptional edsl a b)