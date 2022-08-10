{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Core (
  EGeneric,
  Compile,
  CompileAp,
  ERepr,
  EDSLKind,
  UnEDSLKind,
  Term (Term),
  ClosedTerm,
  IsETypeBackend,
  EHasRepr (..),
  EIsRepr (..),
  IsEType,
  isEType,
  EReprPrimitive,
  EReprSOP,
  EHs,
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
  (:-->),
) where

import Data.Functor.Compose (Compose)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import GHC.TypeLits (Symbol, TypeError, pattern ShowType, pattern Text, pattern (:$$:))
import qualified Generics.SOP as SOP
import qualified Generics.SOP.GGP as SOPG
import Plutarch.EType (
  EEType,
  EGeneric,
  EHs,
  EType,
  ETypeF,
  EfC,
  pattern MkETypeF,
  type (/$),
 )
import Plutarch.Reduce (NoReduce)

newtype EDSLKind = EDSLKind (EType -> Type)

type family UnEDSLKind (edsl :: EDSLKind) :: EType -> Type where
  UnEDSLKind ( 'EDSLKind edsl) = edsl

newtype EReprKind = EReprKind Type

{- | A "representation" of a type. This defines how a user-visible type
 is mapped onto a type in the backend.
-}
class EIsRepr (r :: EReprKind) where
  type EReprApply r (a :: EType) :: EType
  type EReprC r (a :: EType) :: Constraint
  type EReprIsEType r (a :: EType) (edsl :: EDSLKind) (x :: EHs a) :: Constraint
  erfrom :: (EHasRepr a, EReprSort a ~ r) => a ef -> EReprApply r a ef
  erto :: (EHasRepr a, EReprSort a ~ r) => EReprApply r a ef -> a ef
  erIsEType ::
    forall edsl a (x :: EHs a) y.
    (EHasRepr a, EReprSort a ~ r, EReprIsEType r a edsl x) =>
    Proxy r ->
    Proxy edsl ->
    Proxy x ->
    (forall a' (x' :: EHs a'). IsETypeBackend edsl x' => Proxy x' -> y) ->
    y

data EReprPrimitive'

-- | The "identity" representation.
type EReprPrimitive = 'EReprKind EReprPrimitive'

instance EIsRepr EReprPrimitive where
  type EReprApply EReprPrimitive a = a
  type EReprC EReprPrimitive _ = ()
  type EReprIsEType EReprPrimitive _ edsl x = IsETypeBackend edsl x
  erfrom = id
  erto = id
  erIsEType _ _ x f = f x

data EReprSOP'

-- | Representation as a SOP. Requires 'EGeneric'.
type EReprSOP = 'EReprKind EReprSOP'

newtype ESOPed (a :: EType) ef = ESOPed (a ef)

type family Unimplemented (t :: Symbol) :: Constraint where

instance EIsRepr EReprSOP where
  type EReprApply EReprSOP a = ESOPed a
  type EReprC EReprSOP a = EGeneric a
  type EReprIsEType _ _ _ _ = Unimplemented "It is not yet clear how to handle this" -- Known x => IsETypeBackend edsl x
  erfrom = ESOPed
  erto (ESOPed x) = x
  erIsEType _ _ _ _ = error "unimplemented"

class (EIsRepr (EReprSort a), EReprC (EReprSort a) a) => EHasRepr (a :: EType) where
  type EReprSort a :: EReprKind
  type EReprSort _ = EReprSOP

instance EHasRepr EEType where
  type EReprSort _ = EReprPrimitive

type ERepr :: EType -> EType
type ERepr a = EReprApply (EReprSort a) a

class EDSL (edsl :: EDSLKind) where
  type IsETypeBackend edsl :: forall (a :: EType). EHs a -> Constraint

type role Term nominal nominal
data Term (edsl :: EDSLKind) (a :: EType) where
  Term :: {unTerm :: (EDSL edsl, IsETypeBackend edsl (ERepr a)) => UnEDSLKind edsl (ERepr a)} -> Term edsl a

type ClosedTerm (c :: EDSLKind -> Constraint) (a :: EType) = forall edsl. c edsl => Term edsl a

type IsETypeWrapper :: Bool -> EDSLKind -> forall (a :: EType). EHs a -> Constraint
class IsETypeWrapper typeorval edsl x where
  isETypeWrapper :: Proxy typeorval -> Proxy edsl -> Proxy x -> (forall a' (x' :: EHs a'). IsETypeBackend edsl x' => Proxy x' -> y) -> y

instance (EHasRepr a, IsETypeBackend edsl @EEType (ERepr a)) => IsETypeWrapper 'True edsl (a :: EType) where
  isETypeWrapper _ _ _ f = f (Proxy @(ERepr a))

instance (EHasRepr a, EReprIsEType (EReprSort a) a edsl x) => IsETypeWrapper 'False edsl (x :: EHs a) where
  isETypeWrapper _ edsl x f = erIsEType (Proxy @(EReprSort a)) edsl x f

type family TypeOrVal (a :: EType) :: Bool where
  TypeOrVal EEType = 'True
  TypeOrVal _ = 'False

type IsEType :: EDSLKind -> forall (a :: EType). EHs a -> Constraint
class (IsETypeWrapper (TypeOrVal a) edsl x) => IsEType edsl (x :: EHs a)
instance (IsETypeWrapper (TypeOrVal a) edsl x) => IsEType edsl (x :: EHs a)

isEType :: forall edsl a (x :: EHs a) y. IsEType edsl x => Proxy edsl -> Proxy x -> (forall a' (x' :: EHs a'). IsETypeBackend edsl x' => Proxy x' -> y) -> y
isEType = isETypeWrapper (Proxy @(TypeOrVal a))

type CoerceTo :: forall a. forall (b :: Type) -> a -> b
type family CoerceTo (b :: Type) (x :: a) :: b where
  CoerceTo _ x = x

type H1 :: EDSLKind -> forall (a :: Type) -> a -> Constraint
type family H1 (edsl :: EDSLKind) (a :: Type) (x :: a) :: Constraint where
  H1 edsl EType x = IsEType edsl x
  forall (edsl :: EDSLKind) (a :: EType) (_ef :: ETypeF) (x :: a _ef).
    H1 edsl (a _ef) x =
      IsEType edsl (CoerceTo (EHs a) x)

type H2 :: EDSLKind -> forall (a :: Type). a -> Constraint
class H1 edsl a x => H2 edsl (x :: a)
instance H1 edsl a x => H2 edsl (x :: a)

type family Helper (edsl :: EDSLKind) :: ETypeF where
  Helper edsl = MkETypeF (H2 edsl) (Compose NoReduce (Term edsl))

type EConcrete (edsl :: EDSLKind) (a :: EType) = a (Helper edsl)

class (EDSL edsl, IsETypeBackend edsl a) => EConstructable' edsl (a :: EType) where
  econImpl :: HasCallStack => EConcrete edsl a -> UnEDSLKind edsl a

  -- If this didn't return `Term`, implementing it would be a lot harder.
  ematchImpl :: forall b. (HasCallStack, IsEType edsl b) => UnEDSLKind edsl a -> (EConcrete edsl a -> Term edsl b) -> Term edsl b

-- | The crux of what an eDSL is.
class (EConstructable' edsl (ERepr a), EHasRepr a) => EConstructable edsl (a :: EType)

instance (EConstructable' edsl (ERepr a), EHasRepr a) => EConstructable edsl a

-- | The handling of effects depends on the type.
econ :: forall edsl a. (HasCallStack, EConstructable edsl a) => EConcrete edsl a -> Term edsl a
econ x = Term $ econImpl (erfrom x)

{- | For `ematch x \y -> z`, all effects in `x` and `z` must happen in the result.
 The effects in `x` must happen before the effects in `z`.
 `y` must be effectless.
-}
ematch ::
  forall edsl a b.
  (HasCallStack, EConstructable edsl a, IsEType edsl b) =>
  Term edsl a ->
  (EConcrete edsl a -> Term edsl b) ->
  Term edsl b
ematch (Term t) f = ematchImpl t \x -> f (erto x)

data EVoid ef
instance EHasRepr EVoid where type EReprSort _ = EReprPrimitive

-- | Effects of `econ` are effects of the argument.
data ELet a ef = ELet (ef /$ a)

instance EHasRepr (ELet a) where type EReprSort _ = EReprPrimitive

-- | `econ` has no effects.
data EDelay a ef = EDelay (ef /$ a)

instance EHasRepr (EDelay a) where type EReprSort _ = EReprPrimitive

-- | '=>' embedded into an eDSL.
data (#=>) (a :: Constraint) (b :: EType) ef = EConstrained (a => ef /$ b)

instance EHasRepr (a #=> b) where type EReprSort _ = EReprPrimitive

infixr 0 #=>

-- | '->' embedded into an eDSL.
data (#->) a b ef = ELam ((ef /$ a) -> (ef /$ b)) deriving stock (Generic)

instance EHasRepr (a #-> b) where type EReprSort _ = EReprPrimitive

infixr 0 #->

data EAny ef = forall a. EAny (Proxy a) (ef /$ a)
instance EHasRepr EAny where type EReprSort _ = EReprPrimitive

newtype EForall (f :: EHs a -> EType) ef = EForall (forall (forallvar :: EHs a). EfC ef forallvar => ef /$ f forallvar)
instance EHasRepr (EForall ef) where type EReprSort _ = EReprPrimitive

data ESome (f :: EHs a -> EType) ef = forall (x :: EHs a). ESome (EfC ef x => ef /$ f x)
instance EHasRepr (ESome ef) where type EReprSort _ = EReprPrimitive

newtype EFix f ef = EFix (ef /$ f (EFix f))
instance EHasRepr (EFix f) where type EReprSort _ = EReprPrimitive

data EUnit (ef :: ETypeF) = EUnit deriving stock (Generic)
instance EHasRepr EUnit where type EReprSort _ = EReprPrimitive

punit :: (EConstructable edsl EUnit) => Term edsl EUnit
punit = econ EUnit

data EPair a b ef = EPair (ef /$ a) (ef /$ b) deriving stock (Generic)
instance EHasRepr (EPair a b) where type EReprSort _ = EReprPrimitive

data EEither a b ef = ELeft (ef /$ a) | ERight (ef /$ b) deriving stock (Generic)
instance EHasRepr (EEither a b) where type EReprSort _ = EReprPrimitive

pleft :: (ESOP edsl, IsEType edsl a, IsEType edsl b) => Term edsl a -> Term edsl (EEither a b)
pleft = econ . ELeft

pright :: (ESOP edsl, IsEType edsl a, IsEType edsl b) => Term edsl b -> Term edsl (EEither a b)
pright = econ . ERight

peither ::
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl c) =>
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
type EPolymorphic edsl =
  ( forall a (f :: EHs a -> EType). IsEType edsl ( 'ELam f :: EHs (a #-> EEType)) => EConstructable edsl (EForall f)
  , forall a b (f :: EHs a -> EHs b). (forall xVd. IsEType edsl xVd => IsEType edsl (f xVd)) => IsEType edsl ( 'ELam f :: EHs (a #-> b))
  )

class EDSL edsl => EPartial edsl where
  eerror :: IsEType edsl a => Term edsl a

class EDSL edsl => EAp (f :: Type -> Type) edsl where
  eapr :: HasCallStack => f a -> Term edsl b -> Term edsl b
  eapl :: HasCallStack => Term edsl a -> f b -> Term edsl a

class EAp m edsl => EEmbeds (m :: Type -> Type) edsl where
  eembed :: HasCallStack => m (Term edsl a) -> Term edsl a

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
  ( EGeneric a
  , EIsSum edsl (SOPG.GCode (EConcrete edsl a))
  , EReprSort a ~ EReprSOP
  ) =>
  EIsSOP (edsl :: EDSLKind) (a :: EType)
  where
  esop :: Proxy edsl -> Proxy a -> EIsSumR edsl (SOPG.GCode (EConcrete edsl a))
instance
  ( EGeneric a
  , EIsSum edsl (SOPG.GCode (EConcrete edsl a))
  , EReprSort a ~ EReprSOP
  ) =>
  EIsSOP (edsl :: EDSLKind) (a :: EType)
  where
  esop edsl _ = eisSum edsl Proxy

type ESOP :: EDSLKind -> Constraint
type ESOP edsl =
  ( EConstructable edsl EUnit
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable' edsl (EPair a b)
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable' edsl (EEither a b)
  , forall a. EIsSOP edsl a => EConstructable' edsl (ESOPed a)
  , IsEType edsl EEType
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

-- | Useful combinator for unembedded functions.
type (:-->) a b edsl = Term edsl a -> Term edsl b
