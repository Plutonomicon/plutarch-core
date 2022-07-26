module Plutarch.PList where

import Plutarch.Core
import Plutarch.EType

data PListF a self ef
  = PNil
  | PCons (ef /$ a) (ef /$ self)

newtype PList a ef = PList (EFix (PListF a) ef)
