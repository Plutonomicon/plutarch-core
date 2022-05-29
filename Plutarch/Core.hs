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
  ENamedTerm,
  enamedTermImpl,
  enamedTerm,
  IsEType',
  ENewtype (ENewtype),
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
  EVoid,
  EDelay (EDelay),
  EPair(EPair),
  EEither(ELeft, ERight),
  EForall (EForall),
  EAny (EAny),
  EPolymorphic,
  ESOP,
  EIsSOP (..),
  EUnit (EUnit),
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
    
import Data.Kind (Constraint, Type)
import GHC.Generics (Generic)
import Data.Functor.Compose (Compose)
import Data.Proxy (Proxy (Proxy))
import Data.Typeable (Typeable)
import qualified Generics.SOP as SOP
import qualified Generics.SOP.GGP as SOPG
import GHC.TypeLits (TypeError, pattern Text, pattern (:$$:), pattern ShowType)
import Unsafe.Coerce (unsafeCoerce) -- oh no
import Plutarch.EType (EType, ETypeF, ToETypeF, Ef)
import Plutarch.Reduce (NoReduce)
import GHC.Stack (HasCallStack)

type EDSLKind = EType -> Type

type role Term nominal nominal
data Term (edsl :: EDSLKind) (a :: EType) where
  Term :: { unTerm :: (EDSL edsl, IsEType' edsl (ERepr a)) => edsl (ERepr a) } -> Term edsl a

type EConcrete (edsl :: EDSLKind) (a :: EType) = a (ToETypeF (Compose NoReduce (Term edsl)))

class EDSL (edsl :: EDSLKind) where
  type IsEType' edsl :: EType -> Constraint
  enamedTerm :: (HasCallStack, ENamedTerm name edsl a) => Proxy name -> Term edsl a

class Typeable name => ENamedTerm (name :: Type) (edsl :: EDSLKind) (a :: EType) | name -> a where
  enamedTermImpl :: Proxy name -> Term edsl a

newtype ENewtype (a :: EType) f = ENewtype (a f)

class EIsNewtype (a :: EType) where
  type EIsNewtype' a :: Bool
  type EIsNewtype' a = True

type EIfNewtype a = (EIsNewtype a, EIsNewtype' a ~ True)

type family EReprHelper (b :: Bool) (a :: EType) where
  EReprHelper True a = ENewtype a
  EReprHelper False a = a

type ERepr a = EReprHelper (EIsNewtype' a) a

-- Implementing these type safely is almost impossible without full dependent types,
-- as we need to prove that `forall a b. Coercible (EReprHelper b a) a` from the fact
-- that `forall a. Coercible (EReprHelper 'True a) a` and `forall a. Coercible (EReprHelper 'False a) a`.
toERepr :: EConcrete edsl a -> EConcrete edsl (ERepr a)
toERepr = unsafeCoerce
fromERepr :: EConcrete edsl (ERepr a) -> EConcrete edsl a
fromERepr = unsafeCoerce

class (IsEType' edsl (ERepr a)) => IsEType (edsl :: EDSLKind) (a :: EType)
instance (IsEType' edsl (ERepr a)) => IsEType edsl a

class (EDSL edsl, IsEType' edsl a) => EConstructable' edsl (a :: EType) where
  econImpl :: HasCallStack => EConcrete edsl a -> edsl a
  -- If this didn't return `Term`, implementing it would be a lot harder.
  ematchImpl :: forall b. (HasCallStack, IsEType edsl b) => edsl a -> (EConcrete edsl a -> Term edsl b) -> Term edsl b

-- | The crux of what an eDSL is.
class (EConstructable' edsl (ERepr a)) => EConstructable edsl a where
instance (EConstructable' edsl (ERepr a)) => EConstructable edsl a where

-- | The handling of effects depends on the type.
econ :: forall edsl a. (HasCallStack, EConstructable edsl a) => EConcrete edsl a -> Term edsl a
econ x = Term $ econImpl (toERepr x)

-- | For `ematch x \y -> z`, all effects in `x` and `z` must happen in the result.
-- The effects in `x` must happen before the effects in `z`.
-- `y` must be effectless.
ematch :: forall edsl a b. (HasCallStack, EConstructable edsl a, IsEType edsl b) => Term edsl a -> (EConcrete edsl a -> Term edsl b) -> Term edsl b
ematch (Term t) f = ematchImpl t \x -> f (fromERepr x)

data EVoid f

-- | Effects of `econ` are effects of the argument.
data ELet a f = ELet (Ef f a)
instance EIsNewtype (ELet a) where type EIsNewtype' _ = False

-- | `econ` has no effects.
data EDelay a f = EDelay (Ef f a)
instance EIsNewtype (EDelay a) where type EIsNewtype' _ = False

-- | '->' embedded into an eDSL.
data (#->) a b f = ELam ((Ef f a) -> (Ef f b)) deriving stock Generic
instance EIsNewtype (a #-> b) where type EIsNewtype' _ = False

data EAny f = forall a. EAny (Proxy a) (Ef f a)
instance EIsNewtype EAny where type EIsNewtype' _ = False

data EForall (constraint :: a -> Constraint) (b :: a -> EType) f = EForall (forall (x :: a). constraint x => Ef f (b x))
instance EIsNewtype (EForall c f) where type EIsNewtype' _ = False

data EUnit (f :: ETypeF) = EUnit deriving stock Generic
instance EIsNewtype EUnit where type EIsNewtype' _ = False

data EPair a b f = EPair (Ef f a) (Ef f b) deriving stock Generic
instance EIsNewtype (EPair a b) where type EIsNewtype' _ = False

data EEither a b f = ELeft (Ef f a) | ERight (Ef f b) deriving stock Generic
instance EIsNewtype (EEither a b) where type EIsNewtype' _ = False

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

data EIsProductR (edsl :: EDSLKind) (a :: [Type]) =
  forall inner. SOP.All (IsEType edsl) inner => EIsProductR
  { inner :: Proxy inner
  , to :: SOP.NP (Term edsl) inner -> SOP.NP SOP.I a
  , from :: SOP.NP SOP.I a -> SOP.NP (Term edsl) inner
  }

class EIsProduct (edsl :: EDSLKind) (a :: [Type]) where
  eisProduct :: Proxy edsl -> Proxy a -> EIsProductR edsl a

instance EIsProduct edsl '[] where
  eisProduct _ _ = EIsProductR
    { inner = Proxy @'[]
    , to = \SOP.Nil -> SOP.Nil
    , from = \SOP.Nil -> SOP.Nil
    }

-- TODO: Replace with https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0433-unsatisfiable.rst
-- TODO: Possibly show type in question?
instance {-# OVERLAPPABLE #-}
  ( TypeError (
    Text "Can not embed type that contains: "
    :$$: ShowType a
    )
  , EIsProduct edsl as
  ) => EIsProduct edsl (a : as) where
    eisProduct edsl _ = error "unreachable" $ eisProduct edsl (Proxy @as)

instance (IsEType edsl a, EIsProduct edsl as) => EIsProduct edsl (Term edsl a : as) where
  eisProduct edsl _ =
    let prev = eisProduct edsl (Proxy @as) in
    case prev of
      EIsProductR { inner = _ :: Proxy asi, to, from } -> EIsProductR
          { inner = Proxy @(a : asi)
          , to = \(x SOP.:* xs) -> SOP.I x SOP.:* to xs
          , from = \(SOP.I x SOP.:* xs) -> x SOP.:* from xs
          }

data EIsSumR (edsl :: EDSLKind) (a :: [[Type]]) =
  forall inner. SOP.All2 (IsEType edsl) inner => EIsSumR
  { inner :: Proxy inner
  , to :: SOP.SOP (Term edsl) inner -> SOP.SOP SOP.I a
  , from :: SOP.SOP SOP.I a -> SOP.SOP (Term edsl) inner
  }

class EIsSum (edsl :: EDSLKind) (a :: [[Type]]) where
  eisSum :: Proxy edsl -> Proxy a -> EIsSumR edsl a

instance EIsSum edsl '[] where
  eisSum _ _ = EIsSumR
   { inner = Proxy @'[]
   , to = \case {}
   , from = \case {}
   }

instance (EIsProduct edsl a, EIsSum edsl as) => EIsSum edsl (a : as) where
  eisSum edsl _ =
    case eisProduct edsl (Proxy @a) of
      EIsProductR { inner = _ :: Proxy innerh, to = toh, from = fromh } ->
        case eisSum edsl (Proxy @as) of
          EIsSumR { inner = _ :: Proxy innert, to = tot, from = fromt } ->
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
  ) => EIsSOP (edsl :: EDSLKind) (a :: EType) where
    esop :: Proxy edsl -> Proxy a -> EIsSumR edsl (SOPG.GCode (EConcrete edsl a))
instance
  ( EGFrom a
  , EGTo a
  , EGeneric a
  , EIsSum edsl (SOPG.GCode (EConcrete edsl a))
  , EIfNewtype a
  ) => EIsSOP (edsl :: EDSLKind) (a :: EType) where
    esop edsl _ = eisSum edsl Proxy

class IsEType' edsl a => IsETypeHelper edsl a
instance IsEType' edsl a => IsETypeHelper edsl a

type ESOP :: EDSLKind -> Constraint
type ESOP edsl =
  ( EConstructable edsl EUnit
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable' edsl (EPair a b)
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable' edsl (EEither a b)
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable' edsl (a #-> b)
  , forall a. EIsSOP edsl a => EConstructable' edsl (ENewtype a)
  )

type CompileAp variant output = forall a m. (HasCallStack, Applicative m, forall edsl. variant edsl => IsEType edsl a) => (forall edsl. (variant edsl, EAp m edsl) => Term edsl a) -> m (m output)

type Compile variant output = forall a m. (HasCallStack, Monad m, forall edsl. variant edsl => IsEType edsl a) => (forall edsl. (variant edsl, EEmbeds m edsl) => Term edsl a) -> m (m output)
