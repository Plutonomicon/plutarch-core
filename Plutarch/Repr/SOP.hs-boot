module Plutarch.Repr.SOP (PReprSOP) where

import {-# SOURCE #-} Plutarch.Repr (PReprKind (PReprKind))

data PReprSOP'

type PReprSOP = 'PReprKind PReprSOP'
