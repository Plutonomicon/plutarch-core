module Plutarch.Core where
  
import Data.Kind (Constraint, Type)
import GHC.Generics (Generic)
import Data.Functor.Compose (Compose)

import Plutarch.EType (EType, ToETypeF, Ef)
import Plutarch.Reduce (NoReduce)

class EDSL (edsl :: EType -> Type) where
  type IsEType edsl :: EType -> Constraint

type EConcrete edsl a = (a (ToETypeF (Compose NoReduce edsl)))

-- | The crux of what an eDSL is.
class (EDSL edsl, IsEType edsl a) => EConstructable edsl (a :: EType) where
  econ :: EConcrete edsl a -> edsl a
  ematch :: forall b. IsEType edsl b => edsl a -> (EConcrete edsl a -> edsl b) -> edsl b

type Embed2 a b c f = a (Ef f b) (Ef f c)

-- | '->' embedded into an eDSL.
data (#->) a b f = ELam (Embed2 (->) a b f) deriving stock Generic

type ELC :: (EType -> Type) -> Constraint
type ELC edsl = forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable edsl (a #-> b)

elam :: (ELC edsl, IsEType edsl a, IsEType edsl b) => (edsl a -> edsl b) -> edsl (a #-> b)
elam f = econ $ ELam f

(#) :: (ELC edsl, IsEType edsl a, IsEType edsl b) => edsl (a #-> b) -> edsl a -> edsl b
(#) f x = ematch f $ \(ELam f') -> f' x

infixl 8 #

{-
class EDSL edsl => EConstructable edsl (a :: EType) where
  type ERepr edsl a :: EType
  econImpl :: forall a. a (ToETypeF edsl) -> edsl (ERepr edsl a)
  ematchImpl :: forall a b. edsl (ERepr edsl a) -> (a (ToETypeF edsl) -> edsl b) -> edsl b
-}

--data EAny f = forall a. EAny (Ef f a)

class EDSL edsl => EUntyped edsl where
  eunsafeCoerce :: (IsEType edsl a, IsEType edsl b) => edsl a -> edsl b

-- FIXME: add Generic instance
data EPoly (a :: EType -> EType) f = EPoly (forall b. Ef f (a b))

type EPolymorphic edsl = forall a. IsEType edsl a => EConstructable edsl (EPoly a)

class EDSL edsl => EPartial edsl where
  eerror :: IsEType edsl a => edsl a

class EDSL edsl => EEmbeds (m :: Type -> Type) edsl where
  eembed :: m (edsl a) -> edsl a

data EUnit f = EUnit deriving stock Generic

data EPair a b f = EPair (Ef f a) (Ef f b) deriving stock Generic

data EEither a b f = ELeft (Ef f a) | ERight (Ef f b) deriving stock Generic

type ESOP :: (EType -> Type) -> Constraint
type ESOP edsl =
  ( EConstructable edsl EUnit
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable edsl (EPair a b)
  , forall a b. (IsEType edsl a, IsEType edsl b) => EConstructable edsl (EEither a b)
  )


--type EClosed constr a =

{-
-- Hoisting

data Dig = Dig

class GoodHashable a where
  goodHash :: a -> Dig

class Typeable name => NamedTerm (name :: Type) (m :: Type -> Type) (t :: TermLeaf) (a :: HType) | a -> m t a where
  namedTerm :: Proxy name -> Term m t s a

data HoistedTerm
  = HashedHoistedTerm Dig RawTerm
  | forall name m t a. NamedTerm name m t a => NamedHoistedTerm (Proxy name)
  deriving stock (Show)

-- EType

class IsEType (a :: HType) where
  type EAssoc a :: Type
  type EInner a :: HType
  etype :: Proxy a -> EType
  econImpl :: forall s b. a (ToETypeF (Term s)) -> (Term s (PInner a b), PAssociated a)
  ematchImpl :: forall s b. (Term s (PInner a b), PAssociated a) -> (a (ToETypeF (Term s)) -> Term s b) -> Term s b

-- Term

type TermLeaf :: (Type -> Type) -> Type

data Core :: TermLeaf where
  App :: Core (,)
  Lam :: Core Identity
  Var :: Int -> Core (Const ())
  -- | forall a. Typeable a => Extended a

data CombineLeafs :: TermLeaf -> TermLeaf -> TermLeaf where
  CombineLeft :: tl f -> CombineLeafs tl tr f
  CombineRight :: tr f -> CombineLeafs tl tr f

data RawTerm :: TermLeaf -> Type where
  RawTerm :: t f -> f (RawTerm t) -> RawTerm f

-- S constructor is hidden, you're not meant to construct this ever
data S = S

newtype Lvl = Lvl {unLvl :: Int}

data TermResult t (a :: HType) = TermResult
  { rawTerm :: RawTerm t
  , deps :: [HoistedTerm]
  , usedLevels :: S.Set
  , assoc :: PAssociated a
  }

newtype Term :: (Type -> Type) -> S -> HType -> Type where
  Term :: {asRawTerm :: Lvl -> TermResult}

-}

