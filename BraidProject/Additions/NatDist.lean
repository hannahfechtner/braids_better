import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.Linarith

theorem or_dist_iff {i k d : ℕ} : i.dist k ≥ d ↔ i + d ≤ k ∨ k + d ≤ i := by
  unfold Nat.dist; omega

theorem or_dist_iff_eq {i k d : ℕ} : i.dist k = d ↔ i + d = k ∨ k + d = i := by
  unfold Nat.dist; omega

def or_dist_iff_eq_C {i k d : ℕ} : i.dist k = d → PLift (i + d = k) ⊕ PLift (k + d = i) := by
  intro h
  by_cases hik : i ≤ k
  · left
    rw [Nat.dist_eq_sub_of_le hik] at h
    exact ⟨(((Nat.sub_eq_iff_eq_add' hik).mp) h).symm⟩
  right
  constructor
  unfold Nat.dist at h
  omega

theorem dist_succ {i : ℕ} : i.dist (i + 1) = 1 := by unfold Nat.dist; omega

theorem succ_dist {i : ℕ} : (i + 1).dist i = 1 := by
  rw [Nat.dist_comm, dist_succ]

def trichotomous_dist_C (i j : ℕ) : PLift (Nat.dist i j ≥ 2) ⊕ PLift (Nat.dist i j = 1) ⊕ PLift (i = j) := by
  have H : ∀ t, t = Nat.dist i j → PLift (Nat.dist i j ≥ 2) ⊕ PLift (Nat.dist i j = 1) ⊕ PLift (i = j) := by
    intro t
    rcases t
    · exact fun h => Sum.inr (Sum.inr (⟨Nat.eq_of_dist_eq_zero h.symm⟩))
    rename_i s
    rcases s
    · exact fun h => Sum.inr (Sum.inl ⟨h.symm⟩)
    exact fun h => Sum.inl (⟨by linarith [h]⟩)
  exact H (i.dist j) rfl

theorem trichotomous_dist (i j : ℕ) : Nat.dist i j ≥ 2 ∨ Nat.dist i j = 1 ∨ i = j := by
  unfold Nat.dist
  omega

theorem Nat.dist_two (i : ℕ) : i.dist (i + 2) = 2 := by unfold dist; omega

theorem Nat.dist_eq_one (h : Nat.dist j k = 1) : j = k + 1 ∨ k = j + 1 := by
  unfold Nat.dist at h
  omega

theorem Nat.dist_lt_of_increase_smaller {i j: ℕ} (h : i+1<j) :
    Nat.dist (i + 1) (j) < Nat.dist i j := by unfold dist ; omega

theorem Nat.dist_lt_of_decrease_greater {i j: ℕ} (h : i+1<j) :
    Nat.dist i (j-1) < Nat.dist i j := by
  unfold dist
  omega

theorem Nat.dist_no_triangle {a b c n : Nat} (hn : n > 0) : ¬ (a.dist b = n ∧  a.dist c = n ∧ b.dist c = n) := by
  unfold dist
  omega

theorem Nat.dist_step {k : ℕ} (h : i ≤ j) : k + 1 ≤ Nat.dist i j → k ≤ Nat.dist (i + 1) j := by
  unfold Nat.dist
  omega

theorem Nat.dist_to_eq_le {k i j} (h : i ≤ j) : Nat.dist i j = k → j = i + k := by
    unfold Nat.dist
    omega

theorem Nat.dist_to_eq_ge {k i j} (h : i ≥ j) : Nat.dist i j = k → i = j + k := by
    unfold Nat.dist
    omega
