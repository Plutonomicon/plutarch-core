class PDSL edsl => PUntyped edsl where
  punsafeCoerce :: (HasCallStack, IsPType edsl a, IsPType edsl b) => Term edsl a -> Term edsl b
