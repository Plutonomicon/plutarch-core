module Plutarch.Repr.Newtype (PReprNewtype) where

import {-# SOURCE #-} Plutarch.Repr (PReprKind (PReprKind))

data PReprNewtype'

type PReprNewtype = 'PReprKind PReprNewtype'
