module Plutarch.Frontends.LC

type PLC :: PDSLKind -> Constraint
type PLC edsl = forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable edsl (a #-> b)
