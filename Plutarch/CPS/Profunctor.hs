{-# LANGUAGE FlexibleInstances #-}

module Plutarch.CPS.Profunctor where

import Control.Monad.Cont
import Data.Tuple
import Control.Applicative

newtype CStar r f a b = CStar { runCStar :: a -> Cont r (f b) }
  
class CProfunctor r p where
  cdimap :: (a -> Cont r b) -> (c -> Cont r d) -> p b (Cont r c) -> p a (Cont r d)

clmap :: (CProfunctor r p) => (a -> Cont r b) -> p b (Cont r c) -> p a (Cont r c)
clmap f = cdimap f return

crmap :: (CProfunctor r p) => (b -> Cont r c) -> p a (Cont r b) -> p a (Cont r c)
crmap = cdimap return

instance CProfunctor r (->) where
  cdimap ab cd bc = ab >=> bc >=> cd

instance (Functor f) => CProfunctor r (CStar r f) where
  cdimap ab cd (CStar bc) = CStar $ ab >=> bc >=> return . fmap (>>= cd)

class (CProfunctor r p) => CStrong r p where
  cfirst' :: p a (Cont r b) -> p (a, c) (Cont r (b, c))
  cfirst' = cdimap (return . swap) (return . swap) . csecond'

  csecond' :: p a (Cont r b) -> p (c, a) (Cont r (c, b))
  csecond' = cdimap (return . swap) (return . swap) . cfirst'

instance CStrong r (->) where
  cfirst' ab (a, c) = (,c) <$> ab a
  csecond' ab (c, a) = (c,) <$> ab a

instance (Functor f) => CStrong r (CStar r f) where
  cfirst' (CStar afb) = CStar \(a, c) -> (fmap . fmap . fmap) (, c) (afb a)
  csecond' (CStar afb) = CStar \(c, a) -> (fmap . fmap . fmap) (c,) (afb a)

class (CProfunctor r p) => CChoice r p where
  cleft' :: p a (Cont r b) -> p (Either a c) (Cont r (Either b c))
  cleft' = cdimap (return . either Right Left) (return . either Right Left) . cright'

  cright' :: p a (Cont r b) -> p (Either c a) (Cont r (Either c b))
  cright' = cdimap (return . either Right Left) (return . either Right Left) . cleft'

instance CChoice r (->) where
  cleft' ab = either (fmap Left . ab) (return . Right)
  cright' ab = either (return . Left) (fmap Right . ab)

instance (Applicative f) => CChoice r (CStar r f) where
  cleft' (CStar afb) = CStar $
    either
      ((fmap . fmap . fmap) Left . afb)
      (return . pure . return . Right)

  cright' (CStar afb) = CStar $
    either
      (return . pure . return . Left)
      ((fmap . fmap . fmap) Right . afb)

class (CProfunctor r p) => CMonoidal r p where
  cunit :: p () (Cont r ())
  cpar :: p a (Cont r b) -> p c (Cont r d) -> p (a, c) (Cont r (b, d))

instance CMonoidal r (->) where
  cunit () = return ()
  cpar ab cd (a, c) = (,) <$> ab a <*> cd c

instance (Applicative f) => CMonoidal r (CStar r f) where
  cunit = CStar $ \() -> return . pure . return $ ()
  cpar (CStar afb) (CStar cfd) =
    CStar (\(a, c) -> (liftA2 . liftA2) (,) <$> afb a <*> cfd c)