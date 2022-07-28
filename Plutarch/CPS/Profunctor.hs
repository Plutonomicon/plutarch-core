module Plutarch.CPS.Profunctor where

import Data.Profunctor

type CPSPair r a b = (a -> b -> r) -> r

class Profunctor p => CPSStrong p where
  cpsFirst' :: p a b -> p (CPSPair r a c) (CPSPair r b c)
  cpsFirst' = dimap cpsSwap cpsSwap . cpsSecond'

  cpsSecond' :: p a b -> p (CPSPair r c a) (CPSPair r c b)
  cpsSecond' = dimap cpsSwap cpsSwap . cpsFirst'
  {-# MINIMAL cpsFirst' | cpsSecond' #-}

pair :: a -> b -> CPSPair r a b
pair a b f = f a b

pairMap :: (b -> c) -> CPSPair (CPSPair r a c) a b -> CPSPair r a c
pairMap f ab = ab \a b p -> p a (f b)

cpsFst :: CPSPair a a b -> a
cpsFst p = p const

cpsSnd :: CPSPair b a b -> b
cpsSnd p = p \_ b -> b

cpsSwap :: CPSPair r a b -> CPSPair r b a
cpsSwap ab p = ab \a b -> p b a

instance CPSStrong (->) where
  cpsFirst' f ac p = ac \a c -> p (f a) c

  cpsSecond' f ca p = ca \c a -> p c (f a)

instance (Functor f) => CPSStrong (Star f) where
  cpsFirst' (Star f) = Star (rstrength . \ac p -> ac \a c -> p (f a) c)
  cpsSecond' (Star f) = Star (lstrength . \ca p -> ca \c a -> p c (f a))

rstrength :: (Functor f) => (CPSPair (f (CPSPair r a b)) (f a) b) -> f (CPSPair r a b)
rstrength fab = fab \fa b -> fmap (\a p -> p a b) fa

lstrength :: (Functor f) => (CPSPair (f (CPSPair r a b)) a (f b)) -> f (CPSPair r a b)
lstrength afb = afb \a fb -> fmap (\b p -> p a b) fb

type CPSEither r a b = (a -> r) -> (b -> r) -> r

cpsLeft :: a -> CPSEither r a b
cpsLeft a l _ = l a

cpsRight :: b -> CPSEither r a b
cpsRight b _ r = r b

class Profunctor p => CPSChoice p where
  cpsLeft' :: p a b -> p (CPSEither r a c) (CPSEither r b c)
  cpsLeft' =
    dimap (\e -> e cpsRight cpsLeft) (\e -> e cpsRight cpsLeft)
      . cpsRight'

  cpsRight' :: p a b -> p (CPSEither r c a) (CPSEither r c b)
  cpsRight' =
    dimap (\e -> e cpsRight cpsLeft) (\e -> e cpsRight cpsLeft)
      . cpsLeft'
  {-# MINIMAL cpsLeft' | cpsRight' #-}

instance CPSChoice (->) where
  cpsLeft' f e l r = e (l . f) r
  cpsRight' f e l r = e l (r . f)

instance (Applicative f) => CPSChoice (Star f) where
  cpsLeft' (Star f) = Star (\e -> e (fmap cpsLeft . f) (pure . cpsRight))
  cpsRight' (Star f) = Star (\e -> e (pure . cpsLeft) (fmap cpsRight . f))

class Profunctor p => CPSMonoidal p where
  cpsUnit :: p () ()
  cpsPar :: p a b -> p c d -> p (CPSPair r a c) (CPSPair r b d)

instance CPSMonoidal (->) where
  cpsUnit () = ()
  cpsPar f g ac p = ac \a c -> p (f a) (g c)

instance (Applicative f) => CPSMonoidal (Star f) where
  cpsUnit = Star \() -> pure ()
  cpsPar (Star f) (Star g) = Star (starPar f g)

starPar :: (Applicative f) => (a -> f b) -> (c -> f d) -> CPSPair (f (CPSPair r b d)) a c -> f (CPSPair r b d)
starPar afb cfd ac = ac \a c -> pair <$> afb a <*> cfd c