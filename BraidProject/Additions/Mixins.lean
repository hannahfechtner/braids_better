import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Tactic

class IsCommonLeftMultipleMul (M : Type u) [Mul M] where
  common_left_multiple : ∀ a b : M, ∃ c d : M, c * a = d * b

class IsCommonRightMultipleMul (M : Type u) [Mul M] where
  common_right_multiple : ∀ a b : M, ∃ c d : M, a * c = b * d


def left_multiple_iso [Mul A] [Mul B] [h2 : IsCommonLeftMultipleMul A] (e : A ≃* B) :
  IsCommonLeftMultipleMul B where
  common_left_multiple := by
    intro a b
    have := (h2.common_left_multiple (e.symm a) (e.symm b))
    rcases this with ⟨c, d, hcd⟩
    apply congr_arg e at hcd
    simp at hcd
    use e c, e d


def cancel_mul_iso [Mul A] [Mul B] [h2 : IsCancelMul A] (e : A ≃* B) :
  IsCancelMul B where
  mul_left_cancel := by
    intro a b c h
    apply congr_arg e.symm at h
    rw [map_mul, map_mul] at h
    apply (h2.mul_left_cancel (e.symm a)) at h
    rw [EmbeddingLike.apply_eq_iff_eq] at h
    exact h
  mul_right_cancel := by
    intro a b c h
    apply congr_arg e.symm at h
    rw [map_mul, map_mul] at h
    apply (h2.mul_right_cancel (e.symm a)) at h
    rw [EmbeddingLike.apply_eq_iff_eq] at h
    exact h
