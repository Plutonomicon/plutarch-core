module Plutarch.CPS.Optics.Optic where

import Control.Monad.Cont

type COptic r p s t a b = p a (Cont r b) -> p s (Cont r t)

type COptic' r p s a = COptic r p s s a a