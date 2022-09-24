class PDSL edsl => PPartial edsl where
  -- | In a strict backend, this will cause the computation to fail early,
  -- in a lazy backend, it might fail later or never.
  perror :: IsPType edsl a => ETC e (T e a)
  -- Guaranteed fail.
  pguaranteedError ::
