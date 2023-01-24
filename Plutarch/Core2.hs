{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Core2 where

import Data.Kind (Type)
import Control.Monad.Trans.Reader (Reader)
import Data.Functor.Identity (Identity)

type Union :: [(Type -> Type)] -> Type -> Type
data family Union fs a
data instance Union '[] _
data instance Union (f ': fs) a = Here (f a) | There (Union fs a)

instance Functor (Union '[]) where
  fmap _ = \case {}

instance (Functor f, Functor (Union fs)) => Functor (Union (f ': fs)) where
  fmap f (Here x) = Here $ fmap f x
  fmap f (There x) = There $ f <$> x

data Free fs a = Pure a | Join (Union fs (Free fs a))

instance Functor (Union fs) => Functor (Free fs) where
  fmap f (Pure x) = Pure $ f x
  fmap f (Join x) = Join $ fmap f <$> x

instance Functor (Union fs) => Applicative (Free fs) where
  pure = Pure
  x' <*> y' = do
    x <- x'
    y <- y'
    pure (x y)

instance Functor (Union fs) => Monad (Free fs) where
  Pure x >>= f = f x
  Join x >>= f = Join $ (>>= f) <$> x

class Inject f fs where
  inject :: f a -> Union fs a

instance Inject f (f ': fs) where
  inject = Here

instance {-# OVERLAPPABLE #-} Inject f fs => Inject f (g ': fs) where
  inject = There . inject

-- Warning! This is O(n*m) unfortunately since we can't sort
-- then compare fs and gs (I think?).
class InjectMany fs gs where
  injectMany :: Union fs a -> Union gs a

instance InjectMany '[] gs where
  injectMany = \case

instance InjectMany fs gs => InjectMany (f ': fs) (f ': gs) where
  injectMany (Here x) = (Here x)
  injectMany (There x) = There (injectMany x)

instance {-# OVERLAPPABLE #-} (Inject f gs, InjectMany fs gs) => InjectMany (f ': fs) gs where
  injectMany (Here x) = inject x
  injectMany (There x) = injectMany x

send :: Inject f fs => f (Free fs a) -> Free fs a
send = Join . inject

reorder :: (Functor (Union gs), InjectMany fs gs) => Free fs a -> Free gs a
reorder (Pure x) = Pure x
reorder (Join x) = Join $ reorder <$> injectMany x

data QueryInput self = QueryInput ((Int, Int) -> self)
  deriving stock (Functor)

data PermuteInt self = PermuteInt Int (Int -> self)
  deriving stock (Functor)

data CombineInt self = CombineInt Int Int (Int -> self)
  deriving stock (Functor)

data Error e self = Throw e | Catch self (e -> self)
  deriving stock (Functor)

data LC term self = Apply term term (term -> self) | Lam (term -> term) (term -> self)
  deriving stock (Functor)

data LCDB = Lvl Int | ApplyDB LCDB LCDB | LamDB LCDB
  deriving stock (Show)

example :: Free '[PermuteInt, CombineInt, Error Int, QueryInput, LC term] Int
example =
  send $ flip Catch pure $ (+ 100) <$> do
    (x, y) <- send $ QueryInput pure
    x' <- send $ PermuteInt x pure
    z <- send $ CombineInt x' y pure
    myflip <- send $ flip Lam pure \a -> flip Lam pure \b -> _
    if z == 0
      then send $ Throw (10 :: Int)
      else pure z

interpretQuery :: Functor (Union fs) => Free (QueryInput ': fs) a -> Free fs a
interpretQuery (Pure x) = Pure x
interpretQuery (Join (Here (QueryInput k))) = interpretQuery $ k (2, 2)
interpretQuery (Join (There x)) = Join $ interpretQuery <$> x

interpretPermute :: Functor (Union fs) => Free (PermuteInt ': fs) a -> Free fs a
interpretPermute (Pure x) = Pure x
interpretPermute (Join (Here (PermuteInt x k))) = interpretPermute $ k (negate x)
interpretPermute (Join (There x)) = Join $ interpretPermute <$> x

interpretCombine :: Functor (Union fs) => Free (CombineInt ': fs) a -> Free fs a
interpretCombine (Pure x) = Pure x
interpretCombine (Join (Here (CombineInt x y k))) = interpretCombine $ k (x + y)
interpretCombine (Join (There x)) = Join $ interpretCombine <$> x

interpretError :: Functor (Union fs) => Free (Error e ': fs) a -> Free fs (Either e a)
interpretError (Pure x) = Pure (Right x)
interpretError (Join (Here (Throw e))) = pure (Left e)
interpretError (Join (Here (Catch k i))) = interpretError k >>= \case
  Right x -> Pure (Right x)
  Left e -> interpretError $ i e
--interpretError (Join (There x)) = Join $ interpretError <$> x

--newtype Impl = Impl { runImpl :: Reader Int LCDB }
--  deriving newtype (Functor, Applicative, Monad)

interpretLC :: Functor (Union fs) => Free (LC (Reader Int LCDB) ': fs) a -> Free fs a
interpretLC (Pure x) = Pure x
interpretLC (Join (Here (Apply x y k))) = interpretLC $ k (ApplyDB <$> x <*> y)
--interpretLC (Join (Here (Lam f k))) = interpretLC $ k (ApplyDB <$> x <*> y)
interpretLC (Join (There x)) = Join $ interpretLC <$> x

unFree :: Free '[] a -> a
unFree (Pure x) = x
unFree (Join x) = case x of

out :: Either Int Int
out = unFree $ interpretError $ interpretCombine $ interpretPermute $ interpretQuery $ reorder example
