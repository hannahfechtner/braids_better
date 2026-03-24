class IsCommonLeftMultipleMul (M : Type u) [Mul M] where
  common_left_multiple : ∀ a b : M, ∃ c d : M, c * a = d * b
