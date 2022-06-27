{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Plutarch.STLC (ESTLC, compile, compileAp, SimpleType (..), SimpleTerm (..)) where

import Data.Kind (Type)
import Plutarch.Core
import Plutarch.EType
import Data.Proxy (Proxy (Proxy))
import qualified Generics.SOP as SOP
import qualified Generics.SOP.GGP as SOPG
import Data.Functor.Const (Const (Const), getConst)
import GHC.Stack (callStack)

newtype Lvl = Lvl Int

succLvl :: Lvl -> Lvl
succLvl (Lvl l) = Lvl (l + 1)

data SimpleType
  = VoidType
  | UnitType
  | ProductType SimpleType SimpleType
  | SumType SimpleType SimpleType
  | FunctionType SimpleType SimpleType

data SimpleTerm
  = App SimpleTerm SimpleTerm
  | Let SimpleTerm SimpleTerm
  | Lam SimpleType SimpleTerm
  | Var Lvl
  | MkUnit
  | MkProduct SimpleTerm SimpleTerm
  | Fst SimpleTerm
  | Snd SimpleTerm
  | MkSumLeft SimpleTerm SimpleType
  | MkSumRight SimpleType SimpleTerm
  | Match SimpleTerm SimpleTerm SimpleTerm

type ESTLC edsl = (ELC edsl, ESOP edsl)

newtype Impl (m :: Type -> Type) (a :: ETypeRepr) = Impl { runImpl :: Lvl -> m SimpleTerm }

instance EDSL (Impl m) where
  type IsEType' (Impl m) = TypeInfo' m

class TypeInfo' (m :: Type -> Type) (a :: ETypeRepr) where
  typeInfo' :: Proxy m -> Proxy a -> SimpleType

class TypeInfo' m (ERepr a) => TypeInfo m a
instance TypeInfo' m (ERepr a) => TypeInfo m a

typeInfo :: forall a m. TypeInfo m a => Proxy m -> Proxy a -> SimpleType
typeInfo p _ = typeInfo' p (Proxy @(ERepr a))

instance TypeInfo' m (MkETypeRepr EUnit) where
  typeInfo' _ _ = UnitType

instance (TypeInfo m a, TypeInfo m b) => TypeInfo' m (MkETypeRepr (EPair a b)) where
  typeInfo' m _ = ProductType (typeInfo m $ Proxy @a) (typeInfo m $ Proxy @b)

instance (TypeInfo m a, TypeInfo m b) => TypeInfo' m (MkETypeRepr (EEither a b)) where
  typeInfo' m _ = SumType (typeInfo m $ Proxy @a) (typeInfo m $ Proxy @b)

instance (TypeInfo m a, TypeInfo m b) => TypeInfo' m (MkETypeRepr (a #-> b)) where
  typeInfo' m _ = FunctionType (typeInfo m $ Proxy @a) (typeInfo m $ Proxy @b)

instance Applicative m => EConstructable' (Impl m) (MkETypeRepr EUnit) where
  econImpl EUnit = Impl $ \_ -> pure MkUnit
  ematchImpl _ f = f EUnit

instance (Applicative m, TypeInfo m a, TypeInfo m b) => EConstructable' (Impl m) (MkETypeRepr (EPair a b)) where
  econImpl (EPair (Term x) (Term y)) = Impl \lvl -> MkProduct <$> (runImpl x lvl) <*> (runImpl y lvl)
  ematchImpl t f = Term $ Impl \lvl ->
    Let <$> runImpl t lvl <*> (flip runImpl (succLvl lvl) $ unTerm $ f $ EPair (Term $ Impl \_ -> pure $ Fst (Var lvl)) (Term $ Impl \_ -> pure $ Snd (Var lvl)))

instance (Applicative m, TypeInfo m a, TypeInfo m b) => EConstructable' (Impl m) (MkETypeRepr (EEither a b)) where
  econImpl (ELeft (Term x)) = Impl \lvl -> MkSumLeft <$> runImpl x lvl <*> pure (typeInfo (Proxy @m) $ Proxy @b)
  econImpl (ERight (Term y)) = Impl \lvl -> MkSumRight (typeInfo (Proxy @m) $ Proxy @a) <$> (runImpl y lvl)
  ematchImpl t f = Term $ Impl \lvl ->
    Match <$> (runImpl t lvl)
      <*> (runImpl ((unTerm $ elam \left -> f (ELeft left))) lvl)
      <*> (runImpl ((unTerm $ elam \right -> f (ERight right))) lvl)

instance (Applicative m, TypeInfo m a, TypeInfo m b) => EConstructable' (Impl m) (MkETypeRepr (a #-> b)) where
  econImpl (ELam f) = Impl \lvl -> Lam (typeInfo (Proxy @m) $ Proxy @a) <$> runImpl (unTerm . f . Term $ Impl \_ -> pure $ Var lvl) (succLvl lvl)
  ematchImpl f g = g $ ELam \(Term x) -> Term $ Impl \lvl -> App <$> runImpl f lvl <*> runImpl x lvl

instance Applicative m => EAp m (Impl m) where
  eapr x y = Term $ Impl \lvl -> x *> runImpl (unTerm $ y) lvl
  eapl x y = Term $ Impl \lvl -> runImpl (unTerm $ x) lvl <* y

instance Monad m => EEmbeds m (Impl m) where
  eembed t = Term $ Impl \lvl -> do
    t' <- t
    runImpl (unTerm $ t') lvl

gpInfo :: forall (a :: [EType]) m. SOP.All (TypeInfo m) a => Proxy m -> Proxy a -> SimpleType
gpInfo _ _ = getConst $ (SOP.cpara_SList (Proxy @(TypeInfo m)) (Const UnitType) go :: Const SimpleType a)
  where
    go :: forall y ys. TypeInfo m y => Const SimpleType ys -> Const SimpleType (y : ys)
    go (Const UnitType) = Const $ typeInfo (Proxy @m) (Proxy @y)
    go (Const x) = Const $ ProductType (typeInfo (Proxy @m) (Proxy @y)) x

gsInfo :: forall (a :: [[EType]]) m. SOP.All2 (TypeInfo m) a => Proxy m -> Proxy a -> SimpleType
gsInfo _ _ = getConst $ (SOP.cpara_SList (Proxy @(SOP.All (TypeInfo m))) (Const VoidType) go :: Const SimpleType a)
  where
    go :: forall y ys. (SOP.All (TypeInfo m) y) => Const SimpleType ys -> Const SimpleType (y : ys)
    go (Const VoidType) = Const $ gpInfo (Proxy @m) (Proxy @y)
    go (Const x) = Const $ SumType (gpInfo (Proxy @m) (Proxy @y)) x

gpCon :: forall (a :: [EType]) m. (Applicative m, SOP.All (TypeInfo m) a) => SOP.NP (Term (Impl m)) a -> Lvl -> m (SimpleTerm)
gpCon SOP.Nil _ = pure MkUnit
gpCon (x SOP.:* SOP.Nil) lvl = runImpl (unTerm x) lvl
gpCon (x SOP.:* xs) lvl = MkProduct <$> runImpl (unTerm x) lvl <*> gpCon xs lvl

-- FIXME: Ormolu doesn't support `@` in patterns
{- ORMOLU_DISABLE -}
gsCon :: forall (a :: [[EType]]) m. (Applicative m, SOP.All2 (TypeInfo m) a) => SOP.SOP (Term (Impl m)) a -> Lvl -> m (SimpleTerm)
gsCon (SOP.SOP (SOP.Z @_ @_ @_ @(at :: [[EType]]) t)) = case SOP.sList :: SOP.SList at of
  SOP.SNil -> gpCon t
  SOP.SCons -> \lvl -> MkSumLeft <$> (gpCon t lvl) <*> (pure $ gsInfo (Proxy @m) (Proxy @at))
gsCon (SOP.SOP (SOP.S @_ @_ @_ @(ah :: [EType]) sum)) = \lvl -> MkSumRight (gpInfo (Proxy @m) (Proxy @ah)) <$> (gsCon (SOP.SOP sum) lvl)

gpMatch :: forall (a :: [EType]) m a' b. (Applicative m, SOP.All (TypeInfo m) a) => Impl m a' -> (SOP.NP (Term (Impl m)) a -> Term (Impl m) b) -> Term (Impl m) b
gpMatch = case SOP.sList :: SOP.SList a of
  SOP.SNil -> \_ f -> f SOP.Nil
  SOP.SCons @_ @at -> case SOP.sList :: SOP.SList at of
    SOP.SNil -> \(Impl t) f -> f $ (Term (Impl t) SOP.:* SOP.Nil)
    SOP.SCons -> \t f -> Term $ Impl \lvl ->
      Let <$> runImpl t lvl <*> (
        flip runImpl (succLvl lvl) $ unTerm $ gpMatch (Impl \_ -> pure $ Snd (Var lvl)) \sop ->
          (f $ (Term $ Impl \_ -> pure $ Fst (Var lvl)) SOP.:* sop)
      )

gsMatch :: forall (a :: [[EType]]) m a' b. (Applicative m, SOP.All2 (TypeInfo m) a) => Impl m a' -> (SOP.SOP (Term (Impl m)) a -> Term (Impl m) b) -> Term (Impl m) b
gsMatch = case SOP.sList :: SOP.SList a of
  SOP.SNil -> \(Impl t) _ -> Term $ Impl t
  SOP.SCons @_ @at @ah -> case SOP.sList :: SOP.SList at of
    SOP.SNil -> \t f -> gpMatch t \sop -> f (SOP.SOP $ SOP.Z $ sop)
    SOP.SCons -> \t f -> Term $ Impl \lvl ->
      Match <$> (runImpl t lvl)
        <*> (Lam (gpInfo (Proxy @m) (Proxy @ah)) <$> (flip runImpl (succLvl lvl) $ unTerm $ gpMatch (Impl \_ -> pure $ Var lvl) \p -> f (SOP.SOP $ SOP.Z p)))
        <*> (Lam (gsInfo (Proxy @m) (Proxy @at)) <$> (flip runImpl (succLvl lvl) $ unTerm $ gsMatch (Impl \_ -> pure $ Var lvl) \(SOP.SOP sop) -> f (SOP.SOP $ SOP.S sop)))

mapAll :: forall a b c d. (SOP.All c a, forall a'. c a' => d a') => Proxy a -> Proxy c -> Proxy d -> (SOP.All d a => b) -> b
mapAll _ c d f = case (SOP.sList :: SOP.SList a) of
  SOP.SNil -> f
  SOP.SCons @_ @at -> mapAll (Proxy @at) c d f

mapAll2 :: forall a b c d. (SOP.All2 c a, forall a'. c a' => d a') => Proxy a -> Proxy c -> Proxy d -> (SOP.All2 d a => b) -> b
mapAll2 _ c d f = case (SOP.sList :: SOP.SList a) of
  SOP.SNil -> f
  SOP.SCons @_ @at @ah -> mapAll2 (Proxy @at) c d $ mapAll (Proxy @ah) c d f
{- ORMOLU_ENABLE -}

helper2 :: forall a b m. SOP.All2 (IsEType (Impl m)) a => Proxy m -> Proxy a -> (SOP.All2 (TypeInfo m) a => b) -> b
helper2 _ _ = mapAll2 (Proxy @a) (Proxy @(IsEType (Impl m))) (Proxy @(TypeInfo m))

instance (EIsSOP (Impl m) a) => TypeInfo' m (MkENewtype a) where
  typeInfo' m _ =
    case esop (Proxy @(Impl m)) (Proxy @a) of
      EIsSumR { inner } -> helper2 m inner $ gsInfo m inner

instance
  ( EIsSOP (Impl m) a
  , IsEType (Impl m) a
  , Applicative m
  ) => EConstructable' (Impl m) (MkENewtype a) where
  econImpl (ENewtype x) =
    case esop (Proxy @(Impl m)) (Proxy @a) of
      EIsSumR { inner, from } -> helper2 (Proxy @m) inner $ Impl $ gsCon $ (from (SOPG.gfrom x))
  ematchImpl x f =
    case esop (Proxy @(Impl m)) (Proxy @a) of
      EIsSumR { inner, to } -> helper2 (Proxy @m) inner $ gsMatch x \sop -> f $ ENewtype $ SOPG.gto (to sop)

compile' :: forall a m. (Applicative m, IsEType (Impl m) a) => Term (Impl m) a -> m (SimpleTerm, SimpleType)
compile' (Term t) = (,) <$> runImpl t (Lvl 0) <*> pure (typeInfo (Proxy @m) $ Proxy @a)

compile :: Compile ESTLC (SimpleTerm, SimpleType)
compile t = let _unused = callStack in compile' t

compileAp :: CompileAp ESTLC (SimpleTerm, SimpleType)
compileAp t = let _unused = callStack in compile' t
