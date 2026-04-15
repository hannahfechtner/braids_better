import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.NeZero

namespace Nat

theorem zero_or_one_of_pred_eq_zero (n : ℕ) (hn : n.pred = 0): n = 0 ∨ n = 1 := by
  rcases n
  · exact Or.inl (Eq.refl zero)
  rename_i m
  rcases m
  · exact Or.inr (Eq.refl (succ zero))
  simp only [Nat.pred_succ, add_eq_zero, one_ne_zero, and_false] at hn

end Nat
