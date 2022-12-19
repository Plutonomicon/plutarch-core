-- TODO: Taken from github.com/L-as/ski-singletons, will be ported back eventually.

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Plutarch.Internal.SKI (
  Known(..),
  CheckCorrect,
  sinterp,
  Interp,
  DefineNewtypeInner,
  DefineNewtypeConstructor,
  GetNewtypeInner,
  GetNewtypeConstructor,
  ForallS (..),
  Fix (..),
  interp,
  mkNewtype,
  elimNewtype,
  smkNewtype,
  selimNewtype,
  know,
  sinst,
  UnSingle,
  MkSingle,
  unsafeUnSingleConstraint,
  unsafeSingleConstraint,
  sunwrap',
  single,
  single',
  known,
  known', Single, UnsafeSingle(..), type (~>)(..), pattern ElimNewtype, type ElimNewtype, type MkNewtype, pattern MkNewtype) where
  
import Data.Kind (Type, Constraint)
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy (Proxy (Proxy))
import Data.Coerce (Coercible)
import Data.Type.Equality ((:~:)(Refl))
import GHC.Generics (Rep, M1, K1, pattern MetaData)
import GHC.TypeLits (TypeError, ErrorMessage (ShowType, (:<>:), (:$$:), Text))
import Plutarch.Internal.Witness (witness)

-- Helpers

type CoerceTo' :: forall a b. a :~: b -> a -> b
type family CoerceTo' (eq :: a :~: b) (x :: a) :: b where
  CoerceTo' 'Refl x = x

type Representational :: (a -> b) -> Constraint
type Representational f = (forall x y. Coercible x y => Coercible (f x) (f y))

type family Skolem :: a where

-- Singleton classes

-- LAW: Coercible (UnsafeSingle @a) a
type UnsafeSingle :: forall (a :: Type). a -> Type
data family UnsafeSingle :: a -> Type

type Single = UnsafeSingle

unSingle :: UnsafeSingle (x :: a) -> a
unSingle = unsafeCoerce

unSingle' :: forall f a x. Representational f => f (UnsafeSingle (x :: a)) -> f a
unSingle' = let _ = witness (Proxy @(Representational f)) in unsafeCoerce

single :: a -> (forall (x :: a). Single x -> b) -> b
single x f = f (unsafeCoerce x)

single' :: forall f a b. Representational f => f a -> (forall (x :: a). f (Single x) -> b) -> b
single' x f = let _ = witness (Proxy @(Representational f)) in f (unsafeCoerce x)

newtype H1 a c b = H1 (c a => b)

unsafeSingleConstraint ::
  forall (a :: Type) (c :: Type -> Constraint) (b :: Type) (x :: a).
  Proxy c -> (c (UnsafeSingle (x :: a)) => b) -> c a => b
unsafeSingleConstraint _ f = unsafeCoerce (H1 f :: H1 (UnsafeSingle x) c b)

unsafeUnSingleConstraint ::
  forall (a :: Type) (c :: Type -> Constraint) (b :: Type) (x :: a).
  Proxy c -> (c a => b) -> c (UnsafeSingle x) => b
unsafeUnSingleConstraint _ f = unsafeCoerce (H1 f :: H1 a c b)

type family MkSingle :: forall (x :: a) -> UnsafeSingle x where

type UnSingle :: forall (a :: Type) (x :: a). UnsafeSingle x -> a
type family UnSingle (sx :: UnsafeSingle (x :: a)) :: a where
  UnSingle @_ @x _ = x

sinst :: forall (a :: Type) (f :: a -> Type) (y :: forall z. f z) (x :: a). UnsafeSingle @(forall z. f z) y -> UnsafeSingle @(f x) y
sinst x = unsafeCoerce x

class Known (x :: a) where
  knownImpl :: UnsafeSingle x

known :: Known x => UnsafeSingle x
known = knownImpl

known' :: forall {a} (x :: a). Known x => Proxy x -> a
known' _ = unSingle $ known @x

newtype H2 (x :: a) b = H2 (Known x => b)

know :: forall (a :: Type) (b :: Type) (x :: a). Single x -> (Known x => b) -> b
know x f = unsafeCoerce (H2 f :: H2 x b) x

instance Show a => Show (UnsafeSingle (x :: a)) where
  showList = showList . unSingle'
  show = show . unSingle
  showsPrec n = showsPrec n . unSingle

-- Data types

data instance UnsafeSingle @Bool _ where
  SFalse :: UnsafeSingle 'False
  STrue :: UnsafeSingle 'True
instance Known False where
  knownImpl = SFalse
instance Known True where
  knownImpl = STrue

data instance UnsafeSingle @() _ where
  SUnit :: UnsafeSingle '()
instance Known '() where
  knownImpl = SUnit

data instance UnsafeSingle @(_, _) _ where
  SPair :: UnsafeSingle x -> UnsafeSingle y -> UnsafeSingle '(x, y)
instance (Known x, Known y) => Known '(x, y) where
  knownImpl = SPair known known

data instance UnsafeSingle @(Either _ _) _ where
  SLeft :: UnsafeSingle x -> UnsafeSingle (Left x)
  SRight :: UnsafeSingle y -> UnsafeSingle (Right y)
instance Known x => Known (Left x) where
  knownImpl = SLeft known
instance Known y => Known (Right y) where
  knownImpl = SRight known

data Some (f :: a -> Type) = forall (x :: a). Some (f x)
data instance UnsafeSingle @(Some _) _ where
  SSome :: forall f x (y :: f x). UnsafeSingle @(f x) y -> UnsafeSingle ('Some y)
instance forall a (f :: a -> Type) (x :: a) (y :: f x). Known y => Known ('Some y) where
  knownImpl = SSome known

data Forall (f :: a -> Type) = Forall (forall (x :: a). f x)
data instance UnsafeSingle @(Forall (_f :: _a -> Type)) _ where
  SForall ::
    forall (a :: Type) (f :: a -> Type) (y :: forall (x :: a). f x).
    UnsafeSingle @(forall (x :: a). f x) y -> UnsafeSingle ('Forall y)
instance forall a (f :: a -> Type) (y :: forall x. f x). (forall x. Known (y @x)) => Known ('Forall y) where
  knownImpl = SForall $ unsafeCoerce (known :: UnsafeSingle (y @Skolem))

-- Isomorphic to 'Forall' on the term-level.
-- Not isomorphic on the type-level, but viewed externally is equivalent.
-- ((forall x. f x) -> ForallS f, forall x. ForallS f -> f x)
data ForallS (f :: a -> Type) = forall b. ForallS (forall (x :: a). b ~> f x) b
data instance UnsafeSingle @(ForallS (_f :: _a -> Type)) _ where
  SForallS ::
    forall a b (f :: a -> Type) (y :: forall (x :: a). b ~> f x) (z :: b).
    UnsafeSingle @(forall (x :: a). b ~> f x) y -> UnsafeSingle z -> UnsafeSingle ('ForallS y z)
instance
  forall a b (f :: a -> Type) (y :: forall x. b ~> f x) (z :: b).
  (Known z, forall x. Known (y @x)) => Known ('ForallS y z) where
    knownImpl = SForallS (unsafeCoerce (known :: UnsafeSingle (y @Skolem))) known

newtype Fix (f :: Type -> Type) = Fix (f (Fix f))
deriving stock instance Show (f (Fix f)) => Show (Fix f)
data instance UnsafeSingle @(Fix _f) _ where
  SFix :: UnsafeSingle @(f (Fix f)) x -> UnsafeSingle ('Fix x)
instance Known x => Known ('Fix x) where
  knownImpl = SFix known

data instance UnsafeSingle @(_a :~: _b) _ where
  SRefl :: UnsafeSingle @(a :~: a) 'Refl
instance Known 'Refl where
  knownImpl = SRefl

-- Type-level Newtype-specialised generics

type family DefineNewtypeInner (a :: Type) :: Type
type family GetNewtypeInner (a :: Type) :: Type where
  -- FIXME: should use UnwrapNewtype, but GHC bugs prevent it from working
  GetNewtypeInner a = DefineNewtypeInner a

type family DefineNewtypeConstructor (a :: Type) :: inner -> a

type family GetNewtypeConstructor (a :: Type) :: GetNewtypeInner a -> a where
  GetNewtypeConstructor a = DefineNewtypeConstructor a

type family UnwrapNewtype' (a :: Type) (rep :: Type -> Type) :: Type where
  UnwrapNewtype' _ (M1 _ ('MetaData _ _ _ 'True) (M1 _ _ (M1 _ _ (K1 _ i)))) = i
  UnwrapNewtype' a (M1 _ ('MetaData _ _ _ 'False) _) = TypeError (Text "[SKI.UnwrapNewtype] " :<>: ShowType a :<>: Text " is not a newtype!")

type family UnwrapNewtype (a :: Type) :: Type where
  UnwrapNewtype a = UnwrapNewtype' a (Rep a)

type family CheckCorrect' (a :: Type) (i :: Type) (b :: Type) :: () where
  CheckCorrect' _ i i = '()
  CheckCorrect' a i b = TypeError (Text "[SKI.CheckCorrect] malformed DefineNewtypeInner for " :$$: ShowType a :<>: Text " : " :$$: ShowType i :<>: Text " != " :<>: ShowType b)

type family CheckCorrect (a :: Type) :: Constraint where
  CheckCorrect a = CheckCorrect' a (UnwrapNewtype a) (GetNewtypeInner a) ~ '()

elimNewtype :: forall a. CheckCorrect a => a -> GetNewtypeInner a
elimNewtype = let _ = witness (Proxy @(CheckCorrect a)) in unsafeCoerce

mkNewtype :: forall a. CheckCorrect a => GetNewtypeInner a -> a
mkNewtype = let _ = witness (Proxy @(CheckCorrect a)) in unsafeCoerce

selimNewtype ::
  forall (a :: Type) (i :: Type) (c :: i -> a) (x :: i).
  Coercible a i =>
  UnsafeSingle (c x) -> UnsafeSingle x
selimNewtype x = let _ = witness (Proxy @(Coercible a i)) in unsafeCoerce (x :: UnsafeSingle (c x))

smkNewtype ::
  forall (a :: Type) (i :: Type) (c :: i -> a) (x :: i).
  Coercible a i =>
  UnsafeSingle x -> UnsafeSingle (c x)
smkNewtype x = let _ = witness (Proxy @(Coercible a i)) in unsafeCoerce (x :: UnsafeSingle x)

sunwrap' :: forall a x b. CheckCorrect a => UnsafeSingle @a x -> (forall (y :: GetNewtypeInner a). x :~: GetNewtypeConstructor a y -> UnsafeSingle y -> b) -> b
sunwrap' x f = let _ = witness (Proxy @(CheckCorrect a)) in f (error "proof is not real") (unsafeCoerce x)

instance {-# OVERLAPPABLE #-} forall (a :: Type) (i :: Type) (c :: i -> a) (x :: i).
  (Coercible a i, Known @i x) =>
  Known @a (c x) where
  knownImpl = let _ = witness (Proxy @(Coercible a i)) in unsafeCoerce $ known @x

-- SKI

infixr 0 ~>
data (~>) (a :: Type) (b :: Type) where
  S :: (a ~> b ~> c) ~> (a ~> b) ~> a ~> c
  K :: a ~> b ~> a
  I :: a ~> a
  (:@) :: ((a ~> b) ~> c ~> d) -> (a ~> b) -> c ~> d
  (:@@) :: (a ~> b ~> c) -> a -> b ~> c
  MkUnit :: a ~> ()
  MkPair :: a ~> b ~> (a, b)
  ElimPair :: (a ~> b ~> c) ~> (a, b) ~> c
  MkLeft :: a ~> Either a b
  MkRight :: b ~> Either a b
  ElimEither :: (a ~> c) ~> (b ~> c) ~> Either a b ~> c
  MkForall :: forall a f. (forall x. a ~> f x) -> a ~> ForallS f
  ElimForall :: ForallS f ~> f x
  MkSome :: forall f x. f x ~> Some f
  ElimSome :: forall a b c (f :: c -> Type). (a ~> Some f) -> (forall x. f x ~> b) -> a ~> b
  -- FIXME: Add inductive types too and have separate type for fixpoint using
  -- and non-fixpoint using SKI terms, i.e. type (~>) @(r :: Bool) a b = SKI r a b
  MkFix :: f (Fix f) ~> Fix f
  ElimFix :: Fix f ~> f (Fix f)
  FixSKI :: ((a ~> b) ~> a ~> b) ~> a ~> b
  UnsafeMkNewtype :: a :~: GetNewtypeInner b -> a ~> b
  UnsafeElimNewtype :: GetNewtypeInner a :~: b -> a ~> b
  MkEq :: a ~> b :~: b
  ElimEq :: a :~: b ~> p a ~> p b
data instance UnsafeSingle @(_a ~> _b) _ski where
  SS :: UnsafeSingle 'S
  SK :: UnsafeSingle 'K
  SI :: UnsafeSingle 'I
  (:%@) :: UnsafeSingle x -> UnsafeSingle y -> UnsafeSingle (x ':@ y)
  (:%@@) :: UnsafeSingle x -> UnsafeSingle y -> UnsafeSingle (x ':@@ y)
  SMkUnit :: UnsafeSingle 'MkUnit
  SMkPair :: UnsafeSingle 'MkPair
  SElimPair :: UnsafeSingle 'ElimPair
  SMkLeft :: UnsafeSingle 'MkLeft
  SMkRight :: UnsafeSingle 'MkRight
  SElimEither :: UnsafeSingle 'ElimEither
  SMkForall ::
    forall a b f (y :: forall (x :: a). b ~> f x).
    UnsafeSingle @(forall (x :: a). b ~> f x) y -> UnsafeSingle ('MkForall y)
  SElimForall :: UnsafeSingle 'ElimForall
  SMkSome :: UnsafeSingle 'MkSome
  SElimSome ::
    forall a b c (f :: c -> Type) (x :: a ~> Some f) (y :: forall z. f z ~> b).
    UnsafeSingle x -> UnsafeSingle @(forall z. f z ~> b) y -> UnsafeSingle ('ElimSome x y)
  SMkFix :: UnsafeSingle 'MkFix
  SElimFix :: UnsafeSingle 'ElimFix
  SFixSKI :: UnsafeSingle 'FixSKI
  SUnsafeMkNewtype :: UnsafeSingle eq -> UnsafeSingle ('UnsafeMkNewtype eq)
  SUnsafeElimNewtype :: UnsafeSingle eq -> UnsafeSingle ('UnsafeElimNewtype eq)
  SMkEq :: UnsafeSingle 'MkEq
  SElimEq :: UnsafeSingle 'ElimEq
instance Known K where knownImpl = SK
instance Known S where knownImpl = SS
instance Known I where knownImpl = SI
instance (Known x, Known y) => Known (x :@@ y) where knownImpl = known :%@@ known
instance (Known x, Known y) => Known (x :@ y) where knownImpl = known :%@ known
instance Known MkUnit where knownImpl = SMkUnit
instance Known MkPair where knownImpl = SMkPair
instance Known ElimPair where knownImpl = SElimPair
instance Known MkLeft where knownImpl = SMkLeft
instance Known MkRight where knownImpl = SMkRight
instance Known ElimEither where knownImpl = SElimEither
instance
  forall a b (f :: a -> Type) (t :: forall x. b ~> f x).
  (forall x. Known @(b ~> f x) t) => Known (MkForall t) where
    knownImpl = SMkForall (unsafeCoerce (known :: UnsafeSingle (t @Skolem)) :: UnsafeSingle @(forall x. b ~> f x) t)
instance Known ElimForall where knownImpl = SElimForall
instance Known MkSome where knownImpl = SMkSome
instance
  forall a b c (f :: c -> Type) (x :: a ~> Some f) (y :: forall z. f z ~> b).
  (Known x, (forall skolem. Known @(f skolem ~> b) (y @skolem))) => Known (ElimSome x y)
  where knownImpl = SElimSome known (unsafeCoerce (known :: UnsafeSingle (y @Skolem)))
instance Known MkFix where knownImpl = SMkFix
instance Known ElimFix where knownImpl = SElimFix
instance Known FixSKI where knownImpl = SFixSKI
instance forall a b eq.
  (Known eq, CheckCorrect b) => Known @(a ~> b) (UnsafeMkNewtype eq) where knownImpl = SUnsafeMkNewtype known
instance Known eq => Known (UnsafeElimNewtype eq) where knownImpl = SUnsafeElimNewtype known
instance Show (a ~> b) where
  showsPrec _ K = ('K' :)
  showsPrec _ S = ('S' :)
  showsPrec _ I = ('I' :)
  showsPrec prec (x :@@ _) | prec >= 10 =
    ('(' :) . showsPrec 10 x . (" <data>)" <>)
  showsPrec _ (x :@@ _) =
    showsPrec 10 x . (" <data>" <>)
  showsPrec prec (x :@ y) | prec >= 10 =
    ('(' :) . showsPrec 10 x . (' ' :) . showsPrec 10 y . (')' :)
  showsPrec _ (x :@ y) =
    showsPrec 10 x . (' ' :) . showsPrec 10 y
  showsPrec _ MkUnit = ("MkUnit" <>)
  showsPrec _ MkPair = ("MkPair" <>)
  showsPrec _ ElimPair = ("ElimPair" <>)
  showsPrec _ MkLeft = ("MkLeft" <>)
  showsPrec _ MkRight = ("MkRight" <>)
  showsPrec _ ElimEither = ("ElimEither" <>)
  showsPrec prec (MkForall t) | prec >= 10 = ("(MkForall " <>) . showsPrec 10 t . (')' :)
  showsPrec _ (MkForall t) = ("MkForall " <>) . showsPrec 10 t
  showsPrec _ ElimForall = ("ElimForall " <>)
  showsPrec _ MkSome = ("MkSome " <>)
  showsPrec prec (ElimSome x y) | prec >= 10 = ("(ElimSome " <>) . showsPrec 10 x . (' ' :) . showsPrec 10 y . (')' :)
  showsPrec _ (ElimSome x y) = ("ElimSome " <>) . showsPrec 10 x . (' ' :) . showsPrec 10 y
  showsPrec _ MkFix = ("MkFix" <>)
  showsPrec _ ElimFix = ("ElimFix" <>)
  showsPrec _ FixSKI = ("FixSKI" <>)
  showsPrec _ (UnsafeMkNewtype _) = ("MkNewtype" <>)
  showsPrec _ (UnsafeElimNewtype _) = ("ElimNewtype" <>)
  showsPrec _ MkEq = ("MkEq" <>)
  showsPrec _ ElimEq = ("ElimEq" <>)

type family MkNewtype :: GetNewtypeInner b ~> b
type instance MkNewtype = 'UnsafeMkNewtype 'Refl

pattern MkNewtype :: (GetNewtypeInner a ~ UnwrapNewtype a) => GetNewtypeInner a ~> a
pattern MkNewtype = UnsafeMkNewtype Refl

type family ElimNewtype :: a ~> GetNewtypeInner a
type instance ElimNewtype = 'UnsafeElimNewtype 'Refl

pattern ElimNewtype :: CheckCorrect a => a ~> GetNewtypeInner a
pattern ElimNewtype = UnsafeElimNewtype Refl

infixl 9 :@
infixl 9 :%@
infixl 9 :@@
infixl 9 :%@@

type family H3 (c :: a -> b) (x :: b) :: a where
  H3 c (c y) = y

type H4 :: forall a b (f :: a -> Type). Some f -> (forall x. f x ~> b) -> b
type family H4 (w :: Some f) (y :: forall x. f x ~> b) :: b where
  forall _a _b _f (_x :: _a) (w :: _f _x) (y :: forall z. _f z ~> _b).
    H4 ('Some w) y = Interp y w

type Interp :: forall (a :: Type) (b :: Type). (a ~> b) -> a -> b
type family Interp (f :: a ~> b) (x :: a) :: b where
  Interp I x = x
  forall (a :: Type) (b :: Type) (x :: a).
    Interp @a @(b ~> a) ('K @a @b) x = 'K ':@@ x
  Interp (K :@@ x) _ = x
  Interp S x = S :@@ x
  Interp (S :@@ x) y = S :@@ x :@@ y
  Interp (S :@@ x :@@ y) z = Interp (Interp x z) (Interp y z)
  Interp MkUnit _ = '()
  Interp MkPair x = MkPair :@@ x
  Interp (MkPair :@@ x) y = '(x, y)
  Interp ElimPair f = ElimPair :@@ f
  Interp (ElimPair :@@ f) '(x, y) = f `Interp` x `Interp` y
  Interp MkLeft x = Left x
  Interp MkRight x = Right x
  Interp ElimEither f = ElimEither :@@ f
  Interp (ElimEither :@@ f) g = ElimEither :@@ f :@@ g
  Interp (ElimEither :@@ f :@@ _) (Left x) = Interp f x
  Interp (ElimEither :@@ _ :@@ g) (Right x) = Interp g x
  forall _a _b (_f :: _a -> Type) (t :: forall x. _b ~> _f x) (y :: _b).
    Interp (MkForall t) y = 'ForallS t y
  forall _a _b (_f :: _a -> Type) (x :: forall z. _b ~> _f z) (y :: _b).
    Interp ElimForall ('ForallS x y) = Interp x y
  Interp MkSome x = 'Some x
  forall _a _b _c (_f :: _c -> Type) (x :: _a ~> Some _f) (y :: forall w. _f w ~> _b) (z :: _a).
    Interp (ElimSome x y) z = H4 (Interp x z) y
  Interp MkFix x = 'Fix x
  Interp ElimFix ('Fix x) = x
  Interp FixSKI f = FixSKI :@@ f
  Interp (FixSKI :@@ f) x = Interp (Interp f (FixSKI :@@ f)) x
  Interp @_ @b (UnsafeMkNewtype eq) x = GetNewtypeConstructor b (CoerceTo' eq x)
  Interp @a (UnsafeElimNewtype eq) x = CoerceTo' eq (H3 (GetNewtypeConstructor a) x)
  Interp MkEq _ = 'Refl
  Interp ElimEq eq = ElimEq :@@ eq
  Interp (ElimEq :@@ 'Refl) x = x
  Interp (x :@@ y) z = Interp (Interp x y) z
  Interp (x :@ y) z = Interp (Interp x y) z

interp :: (a ~> b) -> a -> b
interp I x = x
interp K x = K :@@ x
interp (K :@@ x) _ = x
interp S x = S :@@ x
interp (S :@@ x) y = S :@@ x :@@ y
interp (S :@@ x :@@ y) z = (interp x z) `interp` (interp y z)
interp MkUnit _ = ()
interp MkPair x = MkPair :@@ x
interp (MkPair :@@ x) y = (x, y)
interp ElimPair f = ElimPair :@@ f
interp (ElimPair :@@ f) (x, y) = f `interp` x `interp` y
interp MkLeft x = Left x
interp MkRight x = Right x
interp ElimEither f = ElimEither :@@ f
interp (ElimEither :@@ f) g = ElimEither :@@ f :@@ g
interp (ElimEither :@@ f :@@ _) (Left x) = interp f x
interp (ElimEither :@@ _ :@@ g) (Right x) = interp g x
interp (MkForall x) y = ForallS x y
interp ElimForall (ForallS x y) = interp x y
interp MkSome x = Some x
interp (ElimSome x y) z = case interp x z of Some w -> interp y w
interp MkFix x = Fix x
interp ElimFix (Fix x) = x
interp FixSKI f = FixSKI :@@ f
interp (FixSKI :@@ f) x = interp (interp f (FixSKI :@@ f)) x
interp (UnsafeMkNewtype Refl) x = unsafeCoerce x
interp (UnsafeElimNewtype Refl) x = unsafeCoerce x
interp MkEq _ = Refl
interp ElimEq eq = ElimEq :@@ eq
interp (ElimEq :@@ Refl) x = x
interp (x :@@ y) z = interp (interp x y) z
interp (x :@ y) z = interp (interp x y) z

-- Implementing this directly is *possible*, but you need some `unsafeCoerce` internally
-- on the `MkForall` and `ElimSome` cases, so it doesn't make much sense to do so.
sinterp :: UnsafeSingle (ski :: a ~> b) -> UnsafeSingle (x :: a) -> UnsafeSingle (Interp ski x :: b)
sinterp = unsafeCoerce interp
