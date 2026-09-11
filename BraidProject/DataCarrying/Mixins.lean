import Mathlib.Tactic

class HasCommonLeftMultipleData (M : Type*) [Mul M] where
  cl₁ : M → M → M
  cl₂ : M → M → M
  cl_spec : ∀ a b : M, cl₂ a b * a = cl₁ a b * b


class HasCommonRightMultipleData (M : Type*) [Mul M] where
  cr₁ : M → M → M
  cr₂ : M → M → M
  cr_spec : ∀ a b : M, a * cr₂ a b = b * cr₁ a b
