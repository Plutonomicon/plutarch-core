-- | Untyped Plutus Core.

{-# Options_GHC -w #-}

{-# Language StandaloneKindSignatures #-}
{-# Language ImportQualifiedPost #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}

module Plutarch.UPLC where -- Term(..), ValueOf(..)) where

import Plutarch.Core hiding (Term)
import Plutarch.Core qualified as Core
import Plutarch.EType (EDSLKind)
import Plutarch.EType
import Data.Kind (Type, Constraint)
import qualified Generics.SOP as SOP
import GHC.Stack (HasCallStack, callStack)
import Data.Coerce
import Type.Reflection
import Data.Proxy
import Control.Applicative (liftA2, liftA3)
import Data.Some.Newtype
import Data.ByteString qualified as BS
import Data.Text qualified as Text
import Data.Word
-- import PlutusCore.Data (Data (..))
import Data.GADT.Show
-- Backend for Term

-- 1) make a Compile EUPLC Term
-- 2) define EUPLC
-- you can look at the STLC backend for inspiration
-- Implementing EForall is a bit hard, I'm still working on that
-- it's related to the DataKinds work

compile' :: forall a m. Applicative m => IsEType (UPLCImpl m) a => Core.Term (UPLCImpl m) a -> m Term
compile' (TheImpl term) = term deBruijnInitIndex

compile :: Compile EUPLC Term
compile t = let _unused = callStack in compile' t

newtype Index = Index { dbnIndex :: Word64 }
  deriving stock Show
  deriving newtype (Eq, Num)

deBruijnInitIndex :: Index
deBruijnInitIndex = Index 0

succIndex :: Index -> Index
succIndex (Index l) = Index (l + 1)

type EUPLC :: EDSLKind -> Constraint
type EUPLC edsl = (ELC edsl, EPolymorphic edsl, ESOP edsl)

type    UPLCImpl :: (Type -> Type) -> EDSLKind
newtype UPLCImpl m a = UPLCImpl { runUPLCImpl :: Index -> m Term }

pattern TheImpl :: (Index -> m Term) -> Core.Term (UPLCImpl m) a
pattern TheImpl { runTheImpl } = Core.Term (UPLCImpl runTheImpl)

instance Applicative f => EConstructable' (UPLCImpl f) (MkETypeRepr (EPair a b)) where
  econImpl :: HasCallStack
           => EConcreteRepr (UPLCImpl f) (MkETypeRepr (EPair a b))
           -> UPLCImpl f (MkETypeRepr (EPair a b))
  econImpl (EPair (TheImpl x) (TheImpl y)) = coerce do
    elam \pair -> pair # TheImpl x # TheImpl y

  ematchImpl
    :: forall x. ()
    => HasCallStack
    => IsEType (UPLCImpl f) x
    => UPLCImpl f (MkETypeRepr (EPair a b))
    -> (EConcreteRepr (UPLCImpl f) (MkETypeRepr (EPair a b))
    -> Core.Term (UPLCImpl f) x)
    -> Core.Term (UPLCImpl f) x
  ematchImpl (UPLCImpl term) next = body where

    body :: Core.Term (UPLCImpl f) x
    body = elet (TheImpl term) \(TheImpl thePair) -> let

      one :: Core.Term (UPLCImpl f) a
      two :: Core.Term (UPLCImpl f) b
      one = TheImpl thePair # elam2 \a b -> a
      two = TheImpl thePair # elam2 \a b -> b

      in next (EPair one two)

instance Applicative f => EConstructable' (UPLCImpl f) (MkETypeRepr (EEither a b)) where
  econImpl :: HasCallStack
           => EConcreteRepr (UPLCImpl f) (MkETypeRepr (EEither a b))
           -> UPLCImpl f (MkETypeRepr (EEither a b))
  econImpl (ELeft (TheImpl left)) = coerce do
    elam2 \inl _ -> inl # TheImpl left
  econImpl (ERight (TheImpl right)) = coerce do
    elam2 \_ inr -> inr # TheImpl right

  ematchImpl
    :: forall x. ()
    => HasCallStack
    => IsEType (UPLCImpl f) x
    => UPLCImpl f (MkETypeRepr (EEither a b))
    -> (EConcreteRepr (UPLCImpl f) (MkETypeRepr (EEither a b)) -> Core.Term (UPLCImpl f) x)
    -> Core.Term (UPLCImpl f) x
  ematchImpl sum next = coerce sum
    # elam do \left  -> next (ELeft  left)
    # elam do \right -> next (ERight right)

instance
  ( EIsSOP (UPLCImpl f) a
  , IsEType (UPLCImpl f) a
  , Applicative f
  ) =>
  EConstructable' (UPLCImpl f) (MkENewtype a)
  where
  econImpl :: HasCallStack => EConcreteRepr (UPLCImpl f) (MkENewtype a) -> UPLCImpl f (MkENewtype a)
  econImpl (ENewtype x) =
    case esop (Proxy @(UPLCImpl f)) (Proxy @a) of
      EIsSumR {inner, from} -> undefined
-- helper @(Proxy @f) inner do
--         UPLCImpl mapAll2 inner
--         (Proxy @(IsEType (UPLCImpl f)))
--         (Proxy @NoTypeInfo)
--         undefined

instance Applicative f => EConstructable' (UPLCImpl f) (MkETypeRepr (a #-> b)) where
  econImpl :: HasCallStack
           => EConcreteRepr (UPLCImpl f) (MkETypeRepr (a #-> b))
           -> UPLCImpl f (MkETypeRepr (a #-> b))
  econImpl (ELam body) = UPLCImpl funImpl where

    funImpl :: Index -> f Term
    funImpl lvl = LamAbs <$> x (succIndex lvl) where

      x :: Index -> f Term
      TheImpl x = body do
        TheImpl \_ -> pure (Var lvl)

  ematchImpl
    :: HasCallStack
    => IsEType (UPLCImpl f) x
    => UPLCImpl f (MkETypeRepr (a #-> b))
    -> (EConcreteRepr (UPLCImpl f) (MkETypeRepr (a #-> b)) -> Core.Term (UPLCImpl f) x)
    -> Core.Term (UPLCImpl f) x
  ematchImpl (UPLCImpl fun) next = next $ ELam \(TheImpl term) -> TheImpl \lvl ->
    Apply <$> fun lvl <*> term lvl

instance Applicative m => EAp m (UPLCImpl m) where
  eapr :: HasCallStack => m a -> Core.Term (UPLCImpl m) b -> Core.Term (UPLCImpl m) b
  eapr as (TheImpl term) = TheImpl \lvl -> as *> term lvl

  eapl :: HasCallStack => Core.Term (UPLCImpl m) a -> m b -> Core.Term (UPLCImpl m) a
  eapl (TheImpl term) bs = TheImpl \lvl -> term lvl <* bs

instance Monad m => EEmbeds m (UPLCImpl m) where
  eembed :: HasCallStack => m (Core.Term (UPLCImpl m) a) -> Core.Term (UPLCImpl m) a
  eembed terms = TheImpl \lvl -> do
    impl <- terms
    runTheImpl impl lvl

type NoTypeInfo :: ETypeRepr -> Constraint
class    NoTypeInfo a
instance NoTypeInfo a

instance EDSL (UPLCImpl m) where
  type IsEType' (UPLCImpl m) = NoTypeInfo

instance Applicative f => EConstructable' (UPLCImpl f) (MkETypeRepr EUnit) where
  econImpl :: HasCallStack => EConcreteRepr (UPLCImpl f) (MkETypeRepr EUnit) -> (UPLCImpl f) (MkETypeRepr EUnit)
  econImpl EUnit = UPLCImpl \_ -> pure MkUnit

  ematchImpl :: (HasCallStack, IsEType (UPLCImpl f) b) => UPLCImpl f (MkETypeRepr EUnit) -> (EConcreteRepr (UPLCImpl f) (MkETypeRepr EUnit) -> Core.Term (UPLCImpl f) b) -> Core.Term (UPLCImpl f) b
  ematchImpl _ next = next EUnit

instance EConstructable' (UPLCImpl f) (MkETypeRepr (EForall (IsEType (UPLCImpl f)) a)) where
  econImpl
    :: HasCallStack
    => EConcreteRepr (UPLCImpl f) (MkETypeRepr (EForall (IsEType (UPLCImpl f)) a))
    -> UPLCImpl f (MkETypeRepr (EForall (IsEType (UPLCImpl f)) a))
  econImpl (EForall f) = coerce f

  ematchImpl
    :: HasCallStack
    => IsEType (UPLCImpl f) b
    => UPLCImpl f (MkETypeRepr (EForall (IsEType (UPLCImpl f)) a))
    -> (EConcreteRepr (UPLCImpl f) (MkETypeRepr (EForall (IsEType (UPLCImpl f)) a)) -> Core.Term (UPLCImpl f) b)
    -> Core.Term (UPLCImpl f) b
  ematchImpl term next = next do
    EForall (coerce term)


instance Functor f => EConstructable' (UPLCImpl f) (MkETypeRepr (ELet a)) where
  econImpl
    :: HasCallStack
    => EConcreteRepr (UPLCImpl f) (MkETypeRepr (ELet a))
    -> UPLCImpl f (MkETypeRepr (ELet a))
  econImpl (ELet term) = coerce term

  ematchImpl :: HasCallStack => IsEType (UPLCImpl f) b => UPLCImpl f (MkETypeRepr (ELet a)) -> (EConcreteRepr (UPLCImpl f) (MkETypeRepr (ELet a)) -> Core.Term (UPLCImpl f) b) -> Core.Term (UPLCImpl f) b
  ematchImpl term next = next do
    ELet (coerce term)

-- | A value of a particular type from a universe.
type ValueOf :: Type -> Type
data ValueOf a = ValueOf !(DefaultUni a) !a
  deriving stock Show

infixr 0 `Apply`

type Term :: Type
data Term
  = Var Index
  | LamAbs !Term
  | Apply !Term !Term
  | Force !Term
  | Delay !Term
  | Constant !(Some ValueOf)
  | Builtin
  | Error
  deriving stock Show

type DefaultUni :: forall k. k -> Type
data DefaultUni a where
  DefaultUniInteger    :: DefaultUni Integer
  DefaultUniByteString :: DefaultUni BS.ByteString
  DefaultUniString     :: DefaultUni Text.Text
  DefaultUniUnit       :: DefaultUni ()
  DefaultUniBool       :: DefaultUni Bool
  DefaultUniProtoList  :: DefaultUni []
  DefaultUniProtoPair  :: DefaultUni (,)
  DefaultUniApply      :: !(DefaultUni f) -> !(DefaultUni a) -> DefaultUni (f a)
  DefaultUniData       :: DefaultUni Data

instance GShow ValueOf
instance Show (DefaultUni a)

data Data
  = Constr Integer [Data]
  | Map [(Data, Data)]
  | List [Data]
  | I Integer
  | B BS.ByteString
  deriving stock (Show, Eq, Ord)

pattern MkUnit :: Term
pattern MkUnit = Constant (Some (ValueOf DefaultUniUnit ()))

--

-- gpInfo :: forall (a :: [EType]) m. SOP.All (TypeInfo m) a => Proxy m -> Proxy a -> SimpleType
-- gpInfo _ _ = getConst $ (SOP.cpara_SList (Proxy @(TypeInfo m)) (Const UnitType) go :: Const SimpleType a)
--   where
--     go :: forall y ys. TypeInfo m y => Const SimpleType ys -> Const SimpleType (y : ys)
--     go (Const UnitType) = Const $ typeInfo (Proxy @m) (Proxy @y)
--     go (Const x) = Const $ ProductType (typeInfo (Proxy @m) (Proxy @y)) x

-- gsInfo :: forall (a :: [[EType]]) m. SOP.All2 (TypeInfo m) a => Proxy m -> Proxy a -> SimpleType
-- gsInfo _ _ = getConst $ (SOP.cpara_SList (Proxy @(SOP.All (TypeInfo m))) (Const VoidType) go :: Const SimpleType a)
--   where
--     go :: forall y ys. (SOP.All (TypeInfo m) y) => Const SimpleType ys -> Const SimpleType (y : ys)
--     go (Const VoidType) = Const $ gpInfo (Proxy @m) (Proxy @y)
--     go (Const x) = Const $ SumType (gpInfo (Proxy @m) (Proxy @y)) x

-- gpCon :: forall (a :: [EType]) m. (Applicative m, SOP.All (TypeInfo m) a) => SOP.NP (Term (Impl m)) a -> Lvl -> m (SimpleTerm)
-- gpCon SOP.Nil _ = pure MkUnit
-- gpCon (x SOP.:* SOP.Nil) lvl = runImpl (unTerm x) lvl
-- gpCon (x SOP.:* xs) lvl = MkProduct <$> runImpl (unTerm x) lvl <*> gpCon xs lvl

-- -- FIXME: Ormolu doesn't support `@` in patterns
-- {- ORMOLU_DISABLE -}
-- gsCon :: forall (a :: [[EType]]) m. (Applicative m, SOP.All2 (TypeInfo m) a) => SOP.SOP (Term (Impl m)) a -> Lvl -> m (SimpleTerm)
-- gsCon (SOP.SOP (SOP.Z @_ @_ @_ @(at :: [[EType]]) t)) = case SOP.sList :: SOP.SList at of
--   SOP.SNil -> gpCon t
--   SOP.SCons -> \lvl -> MkSumLeft <$> (gpCon t lvl) <*> (pure $ gsInfo (Proxy @m) (Proxy @at))
-- gsCon (SOP.SOP (SOP.S @_ @_ @_ @(ah :: [EType]) sum)) = \lvl -> MkSumRight (gpInfo (Proxy @m) (Proxy @ah)) <$> (gsCon (SOP.SOP sum) lvl)

-- gpMatch :: forall (a :: [EType]) m a' b. (Applicative m, SOP.All (TypeInfo m) a) => Impl m a' -> (SOP.NP (Term (Impl m)) a -> Term (Impl m) b) -> Term (Impl m) b
-- gpMatch = case SOP.sList :: SOP.SList a of
--   SOP.SNil -> \_ f -> f SOP.Nil
--   SOP.SCons @_ @at -> case SOP.sList :: SOP.SList at of
--     SOP.SNil -> \(Impl t) f -> f $ (Term (Impl t) SOP.:* SOP.Nil)
--     SOP.SCons -> \t f -> Term $ Impl \lvl ->
--       Let <$> runImpl t lvl <*> (
--         flip runImpl (succLvl lvl) $ unTerm $ gpMatch (Impl \_ -> pure $ Snd (Var lvl)) \sop ->
--           (f $ (Term $ Impl \_ -> pure $ Fst (Var lvl)) SOP.:* sop)
--       )

-- gsMatch :: forall (a :: [[EType]]) m a' b. (Applicative m, SOP.All2 (TypeInfo m) a) => Impl m a' -> (SOP.SOP (Term (Impl m)) a -> Term (Impl m) b) -> Term (Impl m) b
-- gsMatch = case SOP.sList :: SOP.SList a of
--   SOP.SNil -> \(Impl t) _ -> Term $ Impl t
--   SOP.SCons @_ @at @ah -> case SOP.sList :: SOP.SList at of
--     SOP.SNil -> \t f -> gpMatch t \sop -> f (SOP.SOP $ SOP.Z $ sop)
--     SOP.SCons -> \t f -> Term $ Impl \lvl ->
--       Match <$> (runImpl t lvl)
--         <*> (Lam (gpInfo (Proxy @m) (Proxy @ah)) <$> (flip runImpl (succLvl lvl) $ unTerm $ gpMatch (Impl \_ -> pure $ Var lvl) \p -> f (SOP.SOP $ SOP.Z p)))
--         <*> (Lam (gsInfo (Proxy @m) (Proxy @at)) <$> (flip runImpl (succLvl lvl) $ unTerm $ gsMatch (Impl \_ -> pure $ Var lvl) \(SOP.SOP sop) -> f (SOP.SOP $ SOP.S sop)))

mapAll :: forall a b c d. (SOP.All c a, forall a'. c a' => d a') => Proxy a -> Proxy c -> Proxy d -> (SOP.All d a => b) -> b
mapAll _ c d f = case (SOP.sList :: SOP.SList a) of
  SOP.SNil -> f
  SOP.SCons @_ @at -> mapAll (Proxy @at) c d f

-- mapAll2 :: forall a b c d. (SOP.All2 c a, forall a'. c a' => d a') => Proxy a -> Proxy c -> Proxy d -> (SOP.All2 d a => b) -> b
-- mapAll2 _ c d f = case (SOP.sList :: SOP.SList a) of
--   SOP.SNil -> f
--   SOP.SCons @_ @at @ah -> mapAll2 (Proxy @at) c d $ mapAll (Proxy @ah) c d f
-- {- ORMOLU_ENABLE -}

-- helper2 :: forall a b m. SOP.All2 (IsEType (Impl m)) a => Proxy m -> Proxy a -> (SOP.All2 (TypeInfo m) a => b) -> b
-- helper2 _ _ = mapAll2 (Proxy @a) (Proxy @(IsEType (Impl m))) (Proxy @(TypeInfo m))

-- TypeInfo' :: (Type -> Type) -> (ETypeRepr -> Constraint)
-- TypeInfo  :: (Type -> Type) -> (EType     -> Constraint)
