import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.NeZero

namespace Nat

theorem pred_eq_zero_iff (n : ℕ) : n.pred = 0  ↔ (n = 0 ∨ n = 1) := by
  constructor
  · intro hn
    match n with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr rfl
    | Nat.succ (Nat.succ m) => simp only [Nat.pred_succ, add_eq_zero, one_ne_zero, and_false] at hn
  aesop

end Nat
