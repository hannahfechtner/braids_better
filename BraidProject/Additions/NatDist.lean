import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.Linarith

namespace Nat
theorem or_dist_iff {i k d : ℕ} : i.dist k ≥ d ↔ i + d ≤ k ∨ k + d ≤ i := by
  unfold Nat.dist; omega

theorem or_dist_iff_eq {i k d : ℕ} : i.dist k = d ↔ i + d = k ∨ k + d = i := by
  unfold Nat.dist; omega

theorem dist_succ {i : ℕ} : i.dist (i + 1) = 1 := by unfold Nat.dist; omega

theorem succ_dist {i : ℕ} : (i + 1).dist i = 1 := by
  rw [Nat.dist_comm, dist_succ]

theorem trichotomous_dist (i j : ℕ) : Nat.dist i j ≥ 2 ∨ Nat.dist i j = 1 ∨ i = j := by
  unfold Nat.dist
  omega

theorem dist_two (i : ℕ) : i.dist (i + 2) = 2 := by unfold dist; omega

theorem dist_eq_one (h : Nat.dist j k = 1) : j = k + 1 ∨ k = j + 1 := by
  unfold Nat.dist at h
  omega

theorem dist_lt_of_increase_smaller {i j: ℕ} (h : i+1<j) :
    Nat.dist (i + 1) (j) < Nat.dist i j := by unfold dist ; omega

theorem dist_lt_of_decrease_greater {i j: ℕ} (h : i+1<j) :
    Nat.dist i (j-1) < Nat.dist i j := by
  unfold dist
  omega

theorem dist_no_triangle {a b c n : Nat} (hn : n > 0) : ¬ (a.dist b = n ∧  a.dist c = n ∧ b.dist c = n) := by
  unfold dist
  omega

theorem dist_step {k : ℕ} (h : i ≤ j) : k + 1 ≤ Nat.dist i j → k ≤ Nat.dist (i + 1) j := by
  unfold Nat.dist
  omega

theorem dist_to_eq_le {k i j} (h : i ≤ j) : Nat.dist i j = k → j = i + k := by
  unfold Nat.dist
  omega

theorem dist_to_eq_ge {k i j} (h : i ≥ j) : Nat.dist i j = k → i = j + k := by
  unfold Nat.dist
  omega
