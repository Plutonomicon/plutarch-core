module Plutarch.Frontends.IO where

data PByteString (ef :: PTypeF)

data PFD (ef :: PTypeF)

class (IsPType PByteString, PDSL edsl, IsString (Term edsl PByteString)) => PByteStringOps edsl

class (PDSL edsl, IsPType PFD) => PFileSystem edsl where
  pwriteFd :: Term edsl PByteString -> Term edsl PFD -> ETermC edsl ()

class PDSL edsl => PStdout edsl where
  pstdout :: Term edsl PFD

class (PConstructableE1 e PVar, PDSL e) => PMutable e where
  type PVar e :: PType -> Type
  pmkVar :: T e a -> ETC e (PVar e a)
  psetVar :: PVar e a -> T e a -> ETC e ()
  pgetVar :: PVar e a -> ETC e (T e a)
