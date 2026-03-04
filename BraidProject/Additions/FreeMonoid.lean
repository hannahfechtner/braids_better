import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Tactic.Linarith

namespace FreeMonoid

theorem prod_eq_one {a b : FreeMonoid α} (h : a * b = 1) : a = 1 ∧ b = 1 := by
  have H : FreeMonoid.length (a * b) = 0 := by
    rw [h, length_one]
  rw [FreeMonoid.length_mul] at H
  constructor
  · have H : length a = 0 := by linarith [h]
    exact length_eq_zero.mp H
  have H : length b = 0 := by linarith [h]
  exact length_eq_zero.mp H

theorem prod_eq_of {a b : FreeMonoid α} {i : α} (h : a * b = FreeMonoid.of i) :
    (a = 1 ∧ b = of i) ∨ (a = of i ∧ b = 1) := by
  have H : FreeMonoid.length (a * b) = 1 := by
    rw [h]
    exact FreeMonoid.length_of _
  rw [FreeMonoid.length_mul] at H
  have H2 : length a = 0 ∨ length b = 0 := by
    revert H
    rcases (length a)
    · exact fun _ => Or.inl rfl
    intro H
    right
    linarith [H]
  rcases H2 with a_one | b_one
  · left
    constructor
    · exact length_eq_zero.mp a_one
    rw [length_eq_zero.mp a_one] at h
    exact h
  right
  constructor
  · rw [length_eq_zero.mp b_one, mul_one] at h
    exact h
  exact length_eq_zero.mp b_one

theorem prod_eq_prod {a b c d : FreeMonoid α} (h : a * b = c * d) :
    (∃ m, c = a * m ∧ b = m * d) ∨ (∃ m, a = c * m ∧ d = m * b) :=
  List.append_eq_append_iff.mp h

@[to_additive (attr := simp)]
theorem reverse_one : reverse (1 : FreeMonoid α) = 1 := by
  apply List.reverse_nil

theorem reverse_eq_one : reverse a = 1 ↔ a = 1 := by
  constructor
  · intro h
    rw [← reverse_one, ← h]
    exact reverse_reverse.symm
  intro h
  rw [h, reverse_one]

theorem mem_reverse : a ∈ reverse b ↔ a ∈ b := List.mem_reverse

-- though this one is quickly done!
theorem bounded (u : FreeMonoid ℕ) : ∃ k, ∀ x ∈ u, x < k := by
  induction u using FreeMonoid.inductionOn'
  · use 1
    exact fun _ h => (not_mem_one h).elim
  rename_i head tail tail_ih
  rcases tail_ih with ⟨old_k, kh⟩
  use Nat.max old_k (head+1)
  intro x x_in
  rcases x_in
  · exact lt_max_of_lt_right Nat.le.refl
  next x_in_tail =>
  exact lt_max_iff.mpr (Or.inl (kh x x_in_tail))

end FreeMonoid
