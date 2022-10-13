type PSOP :: PDSLKind -> Constraint
type PSOP edsl =
  ( PConstructable edsl PUnit
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable' edsl (PPair a b)
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable' edsl (PEither a b)
  , forall a. PIsSOP edsl a => PConstructable' edsl (PSOPed a)
  , IsPType edsl PPType
  )
