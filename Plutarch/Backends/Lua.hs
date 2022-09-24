-- | Compile into Lua
module Plutarch.Backends.Lua () where

data PTable ef

class (PLC edsl, PSOP edsl, IsPType edsl PAny) => PLuaTerm edsl where
  pmkTable :: [(Term edsl a, Term edsl b)] -> Term edsl PTable
  paccess :: Term edsl a -> Term edsl b -> Term edsl PAny
