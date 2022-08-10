module Plutarch.Optics.PList where

import Plutarch.CPS.Optics.Traversal
import Control.Monad.Cont
import Control.Applicative
import Plutarch.Core
import Plutarch.PList

list' :: [a] -> Cont r (FunList a b [b])
list' [] = cont \f -> f (pure [])
list' (x:xs) = cont $ \c -> runCont (list' xs) (c . liftA2 (:) (single x))

 
single :: a -> FunList a b b
single a = FunList $ Right (a, FunList $ Left id)

list :: CTraversal r [a] [b] a b
list = traversal list'

plist'' :: (ESOP edsl, IsEType edsl a, IsEType edsl r) => Term edsl (EFix (PListF a)) -> Cont (Term edsl r) (FunList (Term edsl a) (Term edsl b) (Term edsl (EFix (PListF b))))
plist'' fl = cont \f ->
  ematch fl \(EFix l) -> ematch l \case
    PNil -> f . pure . econ . EFix . econ $ PNil
    PCons x xs ->
      runCont
        (plist'' xs)
        (f . liftA2 (\x' -> econ . EFix . econ . PCons x') (single x))