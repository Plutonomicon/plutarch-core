{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Core (
  EGeneric,
  Compile,
  CompileAp,
  ERepr,
  EDSLKind,
  Term (Term),
  ClosedTerm,
  IsEType',
  EIsNewtype,
  EIsNewtype',
  EIfNewtype,
  IsEType,
  EConcrete,
  EConstructable' (econImpl, ematchImpl),
  EConstructable,
  econ,
  ematch,
  type (#->),
  pattern ELam,
  type (#=>),
  pattern EConstrained,
  EVoid,
  EDelay (EDelay),
  EPair (EPair),
  EEither (ELeft, ERight),
  peither,
  pleft,
  pright,
  EForall (EForall),
  ESome (ESome),
  EFix (EFix),
  EAny (EAny),
  EPolymorphic,
  ESOP,
  EIsSOP (..),
  EUnit (EUnit),
  punit,
  EDSL,
  ELC,
  unTerm,
  elam,
  (#),
  elet,
  eunsafeCoerce,
  EUntyped,
  EPartial,
  eerror,
  EEmbeds,
  eembed,
  EAp,
  eapr,
  eapl,
  EIsProduct (..),
  EIsProductR (..),
  EIsSum (..),
  EIsSumR (..),
) where

import Data.Coerce (coerce)
import Data.Functor.Compose (Compose)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import GHC.TypeLits (TypeError, pattern ShowType, pattern Text, pattern (:$$:))
import qualified Generics.SOP as SOP
import qualified Generics.SOP.GGP as SOPG
import Plutarch.EType (
  EDSLKind,
  EIfNewtype,
  EIsNewtype,
  EIsNewtype',
  ENewtype,
  ERepr,
  EReprAp,
  EType,
  ETypeF,
  ETypeRepr (MkETypeRepr),
  Ef,
  coerceERepr,
  pattern MkETypeF,
  type (/$),
 )
import Plutarch.Reduce (NoReduce)

class EDSL (edsl :: EDSLKind) where
  type IsEType' edsl :: ETypeRepr -> Constraint

type role Term nominal nominal
data Term (edsl :: EDSLKind) (a :: EType) where
  Term :: {unTerm :: (EDSL edsl, IsEType' edsl (ERepr a)) => edsl (ERepr a)} -> Term edsl a

type ClosedTerm (c :: EDSLKind -> Constraint) (a :: EType) = forall edsl. c edsl => Term edsl a

type family Helper (edsl :: EDSLKind) :: ETypeF where
  Helper edsl = MkETypeF (IsEType edsl) (Compose NoReduce (Term edsl))

type EConcrete (edsl :: EDSLKind) (a :: EType) = a (Helper edsl)

type EConcreteRepr (edsl :: EDSLKind) (a :: ETypeRepr) = EConcrete edsl (EReprAp a)

toERepr :: forall a edsl. EIsNewtype a => EConcrete edsl a -> EConcreteRepr edsl (ERepr a)
toERepr x = coerceERepr (Proxy @a) $ coerce x
fromERepr :: forall a edsl. EIsNewtype a => EConcreteRepr edsl (ERepr a) -> EConcrete edsl a
fromERepr x = coerceERepr (Proxy @a) $ coerce x

class (IsEType' edsl (ERepr a)) => IsEType (edsl :: EDSLKind) (a :: EType)
instance (IsEType' edsl (ERepr a)) => IsEType edsl a

class (forall a. IsEType edsl a => IsEType edsl (f a)) => IsEType2 (edsl :: EDSLKind) (f :: EType -> EType)
instance (forall a. IsEType edsl a => IsEType edsl (f a)) => IsEType2 (edsl :: EDSLKind) (f :: EType -> EType)

class (EDSL edsl, IsEType' edsl a) => EConstructable' edsl (a :: ETypeRepr) where
  econImpl :: HasCallStack => EConcreteRepr edsl a -> edsl a

  -- If this didn't return `Term`, implementing it would be a lot harder.
  ematchImpl :: forall b. (HasCallStack, IsEType edsl b) => edsl a -> (EConcreteRepr edsl a -> Term edsl b) -> Term edsl b

-- | The crux of what an eDSL is.
class (EConstructable' edsl (ERepr a)) => EConstructable edsl a

instance (EConstructable' edsl (ERepr a)) => EConstructable edsl a

-- | The handling of effects depends on the type.
econ :: forall edsl a. (HasCallStack, EIsNewtype a, EConstructable edsl a) => EConcrete edsl a -> Term edsl a
econ x = Term $ econImpl (toERepr x)

{- | For `ematch x \y -> z`, all effects in `x` and `z` must happen in the result.
 The effects in `x` must happen before the effects in `z`.
 `y` must be effectless.
-}
ematch :: forall edsl a b. (HasCallStack, EIsNewtype a, EConstructable edsl a, IsEType edsl b) => Term edsl a -> (EConcrete edsl a -> Term edsl b) -> Term edsl b
ematch (Term t) f = ematchImpl t \x -> f (fromERepr x)

data EVoid ef
instance EIsNewtype EVoid where type EIsNewtype' _ = False

-- | Effects of `econ` are effects of the argument.
data ELet a ef = ELet (Ef ef a)

instance EIsNewtype (ELet a) where type EIsNewtype' _ = False

-- | `econ` has no effects.
data EDelay a ef = EDelay (Ef ef a)

instance EIsNewtype (EDelay a) where type EIsNewtype' _ = False

-- | '=>' embedded into an eDSL.
data (#=>) (a :: Constraint) (b :: EType) ef = EConstrained (a => Ef ef b)

instance EIsNewtype (a #=> b) where type EIsNewtype' _ = False

infixr 0 #=>

-- | '->' embedded into an eDSL.
data (#->) a b ef = ELam ((ef /$ a) -> (ef /$ b)) deriving stock (Generic)

instance EIsNewtype (a #-> b) where type EIsNewtype' _ = False

infixr 0 #->

data EAny ef = forall a. EAny (Proxy a) (Ef ef a)
instance EIsNewtype EAny where type EIsNewtype' _ = False

newtype EForall (constraint :: a -> Constraint) (b :: a -> EType) ef = EForall (forall (x :: a). constraint x => ef /$ b x)
instance EIsNewtype (EForall c ef) where type EIsNewtype' _ = False

data ESome (constraint :: a -> Constraint) (b :: a -> EType) ef = forall (x :: a). ESome (constraint x => ef /$ b x)
instance EIsNewtype (ESome c ef) where type EIsNewtype' _ = False

newtype EFix f ef = EFix (ef /$ f (EFix f))
instance EIsNewtype (EFix f) where type EIsNewtype' _ = False

data EUnit (f :: ETypeF) = EUnit deriving stock (Generic)
instance EIsNewtype EUnit where type EIsNewtype' _ = False

punit :: (EConstructable edsl EUnit) => Term edsl EUnit
punit = econ EUnit

data EPair a b ef = EPair (ef /$ a) (ef /$ b) deriving stock (Generic)
instance EIsNewtype (EPair a b) where type EIsNewtype' _ = False

data EEither a b f = ELeft (Ef f a) | ERight (Ef f b) deriving stock (Generic)
instance EIsNewtype (EEither a b) where type EIsNewtype' _ = False


pleft :: (ESOP edsl, IsEType edsl a, IsEType edsl b) => Term edsl a -> Term edsl (EEither a b)
pleft = econ . ELeft

pright :: (ESOP edsl, IsEType edsl a, IsEType edsl b) => Term edsl b -> Term edsl (EEither a b)
pright = econ . ERight

peither :: (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl c) =>
  (Term edsl a -> Term edsl c) ->
  (Term edsl b -> Term edsl c) ->
  Term edsl (EEither a b) ->
  Term edsl c
peither f g te = ematch te \case
  ELeft x -> f x
  ERight x -> g x

type ELC :: EDSLKind -> Constraint
type ELC edsl = forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable edsl (a #-> b)

elam :: forall edsl a b. (HasCallStack, EConstructable edsl (a #-> b)) => (Term edsl a -> Term edsl b) -> Term edsl (a #-> b)
elam f = econ $ (ELam f :: EConcrete edsl (a #-> b))

(#) :: (HasCallStack, ELC edsl, IsEType edsl a, IsEType edsl b) => Term edsl (a #-> b) -> Term edsl a -> Term edsl b
(#) f x = ematch f (\(ELam f') -> f' x)

infixl 8 #

elet :: forall edsl a b. (HasCallStack, EConstructable edsl (ELet a), IsEType edsl b) => Term edsl a -> (Term edsl a -> Term edsl b) -> Term edsl b
elet x f = ematch (econ $ ELet x) \(ELet y) -> f y

class EDSL edsl => EUntyped edsl where
  eunsafeCoerce :: (HasCallStack, IsEType edsl a, IsEType edsl b) => Term edsl a -> Term edsl b

type EPolymorphic :: EDSLKind -> Constraint
type EPolymorphic edsl = forall a. (forall x. IsEType edsl (a x)) => EConstructable edsl (EForall (IsEType edsl) a)

class EDSL edsl => EPartial edsl where
  eerror :: IsEType edsl a => Term edsl a

class EDSL edsl => EAp (f :: Type -> Type) edsl where
  eapr :: HasCallStack => f a -> Term edsl b -> Term edsl b
  eapl :: HasCallStack => Term edsl a -> f b -> Term edsl a

class EAp m edsl => EEmbeds (m :: Type -> Type) edsl where
  eembed :: HasCallStack => m (Term edsl a) -> Term edsl a

type EGeneric a = forall f. Generic (a f)

class SOPG.GFrom a => EGFrom' a
instance SOPG.GFrom a => EGFrom' a
type EGFrom a = forall f. EGFrom' (a f)

class SOPG.GTo a => EGTo' a
instance SOPG.GTo a => EGTo' a
type EGTo a = forall f. EGTo' (a f)

data EIsProductR (edsl :: EDSLKind) (a :: [Type]) = forall inner.
  SOP.All (IsEType edsl) inner =>
  EIsProductR
  { inner :: Proxy inner
  , to :: SOP.NP (Term edsl) inner -> SOP.NP SOP.I a
  , from :: SOP.NP SOP.I a -> SOP.NP (Term edsl) inner
  }

class EIsProduct (edsl :: EDSLKind) (a :: [Type]) where
  eisProduct :: Proxy edsl -> Proxy a -> EIsProductR edsl a

instance EIsProduct edsl '[] where
  eisProduct _ _ =
    EIsProductR
      { inner = Proxy @'[]
      , to = \SOP.Nil -> SOP.Nil
      , from = \SOP.Nil -> SOP.Nil
      }

-- TODO: Replace with https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0433-unsatisfiable.rst
-- TODO: Possibly show type in question?
instance
  {-# OVERLAPPABLE #-}
  ( TypeError
      ( Text "Can not embed type that contains: "
          :$$: ShowType a
      )
  , EIsProduct edsl as
  ) =>
  EIsProduct edsl (a : as)
  where
  eisProduct edsl _ = error "unreachable" $ eisProduct edsl (Proxy @as)

instance (IsEType edsl a, EIsProduct edsl as) => EIsProduct edsl (Term edsl a : as) where
  eisProduct edsl _ =
    let prev = eisProduct edsl (Proxy @as)
     in case prev of
          EIsProductR {inner = _ :: Proxy asi, to, from} ->
            EIsProductR
              { inner = Proxy @(a : asi)
              , to = \(x SOP.:* xs) -> SOP.I x SOP.:* to xs
              , from = \(SOP.I x SOP.:* xs) -> x SOP.:* from xs
              }

data EIsSumR (edsl :: EDSLKind) (a :: [[Type]]) = forall inner.
  SOP.All2 (IsEType edsl) inner =>
  EIsSumR
  { inner :: Proxy inner
  , to :: SOP.SOP (Term edsl) inner -> SOP.SOP SOP.I a
  , from :: SOP.SOP SOP.I a -> SOP.SOP (Term edsl) inner
  }

class EIsSum (edsl :: EDSLKind) (a :: [[Type]]) where
  eisSum :: Proxy edsl -> Proxy a -> EIsSumR edsl a

instance EIsSum edsl '[] where
  eisSum _ _ =
    EIsSumR
      { inner = Proxy @'[]
      , to = \case {}
      , from = \case {}
      }

instance (EIsProduct edsl a, EIsSum edsl as) => EIsSum edsl (a : as) where
  eisSum edsl _ =
    case eisProduct edsl (Proxy @a) of
      EIsProductR {inner = _ :: Proxy innerh, to = toh, from = fromh} ->
        case eisSum edsl (Proxy @as) of
          EIsSumR {inner = _ :: Proxy innert, to = tot, from = fromt} ->
            EIsSumR
              { inner = Proxy @(innerh : innert)
              , to = \case
                  SOP.SOP (SOP.Z x) -> SOP.SOP $ SOP.Z $ toh x
                  SOP.SOP (SOP.S x) -> case tot $ SOP.SOP $ x of SOP.SOP y -> SOP.SOP (SOP.S y)
              , from = \case
                  SOP.SOP (SOP.Z x) -> SOP.SOP $ SOP.Z $ fromh x
                  SOP.SOP (SOP.S x) -> case fromt $ SOP.SOP $ x of SOP.SOP y -> SOP.SOP (SOP.S y)
              }

class
  ( EGFrom a
  , EGTo a
  , EGeneric a
  , EIsSum edsl (SOPG.GCode (EConcrete edsl a))
  , EIfNewtype a
  ) =>
  EIsSOP (edsl :: EDSLKind) (a :: EType)
  where
  esop :: Proxy edsl -> Proxy a -> EIsSumR edsl (SOPG.GCode (EConcrete edsl a))
instance
  ( EGFrom a
  , EGTo a
  , EGeneric a
  , EIsSum edsl (SOPG.GCode (EConcrete edsl a))
  , EIfNewtype a
  ) =>
  EIsSOP (edsl :: EDSLKind) (a :: EType)
  where
  esop edsl _ = eisSum edsl Proxy

class IsEType' edsl a => IsETypeHelper edsl a
instance IsEType' edsl a => IsETypeHelper edsl a

type ESOP :: EDSLKind -> Constraint
type ESOP edsl =
  ( EConstructable edsl EUnit
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable' edsl (MkETypeRepr (EPair a b))
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable' edsl (MkETypeRepr (EEither a b))
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable' edsl (MkETypeRepr (a #-> b))
  , forall a. EIsSOP edsl a => EConstructable' edsl (MkETypeRepr (ENewtype a))
  )

type CompileAp variant output =
  forall a m.
  (HasCallStack, Applicative m, forall edsl. variant edsl => IsEType edsl a) =>
  (forall edsl. (variant edsl, EAp m edsl) => Term edsl a) ->
  m output

type Compile variant output =
  forall a m.
  (HasCallStack, Monad m, forall edsl. variant edsl => IsEType edsl a) =>
  (forall edsl. (variant edsl, EEmbeds m edsl) => Term edsl a) ->
  m output
