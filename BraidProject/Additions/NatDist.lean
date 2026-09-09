import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.Linarith

namespace Nat
theorem le_dist_iff {i k d : ℕ} : d ≤ i.dist k ↔ i + d ≤ k ∨ k + d ≤ i := by
  unfold Nat.dist; omega

theorem eq_dist_iff {i k d : ℕ} : i.dist k = d ↔ i + d = k ∨ k + d = i := by
  unfold Nat.dist; omega

theorem dist_self_add_one {i : ℕ} : i.dist (i + 1) = 1 := by unfold Nat.dist; omega

theorem add_one_dist_self {i : ℕ} : (i + 1).dist i = 1 := by
  rw [Nat.dist_comm, dist_self_add_one]

theorem dist_trichotomy (i j : ℕ) : Nat.dist i j ≥ 2 ∨ Nat.dist i j = 1 ∨ i = j := by
  unfold Nat.dist
  omega

theorem dist_self_add_two (i : ℕ) : i.dist (i + 2) = 2 := by unfold dist; omega

theorem dist_eq_one (h : Nat.dist j k = 1) : j = k + 1 ∨ k = j + 1 := by
  unfold Nat.dist at h
  omega

theorem dist_add_one_left_lt {i j: ℕ} (h : i + 1 < j) :
    Nat.dist (i + 1) (j) < Nat.dist i j := by unfold dist ; omega

theorem dist_sub_one_right_lt {i j: ℕ} (h : i + 1 < j) :
    Nat.dist i (j-1) < Nat.dist i j := by
  unfold dist
  omega

theorem dist_no_triangle {a b c n : Nat} (hn : n > 0) : ¬ (a.dist b = n ∧  a.dist c = n ∧ b.dist c = n) := by
  unfold dist
  omega
