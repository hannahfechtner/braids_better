import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.Linarith

theorem or_dist_iff {i k d : ℕ} : i.dist k ≥ d ↔ i + d ≤ k ∨ k + d ≤ i := by
  constructor
  · intro h
    by_cases hik : i ≤ k
    · left
      rw [Nat.dist_eq_sub_of_le hik] at h
      exact (Nat.le_sub_iff_add_le' hik).mp h
    · right
      apply le_of_not_le at hik
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hik] at h
      exact (Nat.le_sub_iff_add_le' hik).mp h
  intro h1
  rcases h1 with ha | hb
  · rw [Nat.dist_eq_sub_of_le (le_of_add_le_left ha)]
    exact Nat.le_sub_of_add_le' ha
  rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (le_of_add_le_left hb)]
  exact Nat.le_sub_of_add_le' hb

theorem or_dist_iff_eq {i k d : ℕ} : i.dist k = d ↔ i + d = k ∨ k + d = i := by
  constructor
  · intro h
    by_cases hik : i ≤ k
    · left
      rw [Nat.dist_eq_sub_of_le hik] at h
      exact (((Nat.sub_eq_iff_eq_add' hik).mp) h).symm
    · right
      apply le_of_not_le at hik
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hik] at h
      exact (((Nat.sub_eq_iff_eq_add' hik).mp) h).symm
  intro h1
  rcases h1 with ha | hb
  · rw [Nat.dist_eq_sub_of_le (le_of_add_le_left (Nat.le_of_eq ha))]
    exact (Nat.eq_sub_of_add_eq' ha).symm
  rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (le_of_add_le_left (Nat.le_of_eq hb))]
  exact (Nat.eq_sub_of_add_eq' hb).symm

theorem dist_succ {i : ℕ} : i.dist (i + 1) = 1 := by
  rw [Nat.dist_eq_sub_of_le (Nat.le_succ i)]
  /- why can't I use the .symm notation? -/
  exact Eq.symm (Nat.eq_sub_of_add_eq' rfl)

theorem trichotomous_dist (i j : ℕ) : Nat.dist i j >= 2 ∨ Nat.dist i j = 1 ∨ i = j := by
  have H : ∀ t, t = Nat.dist i j → Nat.dist i j >= 2 ∨ Nat.dist i j = 1 ∨ i = j := by
    intro t
    rcases t
    · exact fun h => Or.inr (Or.inr (Nat.eq_of_dist_eq_zero h.symm))
    rename_i s
    rcases s
    · exact fun h => Or.inr (Or.inl h.symm)
    exact fun h => Or.inl (by linarith [h])
  exact H (i.dist j) rfl

theorem Nat.dist_two (i : ℕ) : i.dist (i + 2) = 2 := by
  have H := (Nat.dist_add_add_left i 0 2).trans (Nat.dist_zero_left 2)
  rw [add_zero] at H
  exact H

theorem Nat.dist_eq_one (h : Nat.dist j k = 1) : j = k + 1 ∨ k = j + 1 := by
  unfold Nat.dist at h
  rcases lt_or_ge j k with hjk | hkj
  · rw [Nat.sub_eq_zero_of_le (le_of_succ_le hjk), zero_add] at h
    exact Or.inr ((Nat.sub_eq_iff_eq_add' (le_of_succ_le hjk)).mp h)
  rw [Nat.sub_eq_zero_of_le hkj, add_zero] at h
  exact Or.inl ((Nat.sub_eq_iff_eq_add' hkj).mp h)

theorem Nat.dist_lt_of_increase_smaller {i j: ℕ} (h : i+1<j) :
    Nat.dist (i + 1) (j) < Nat.dist i j := by
  rw [Nat.dist_eq_sub_of_le (le_of_succ_le h), Nat.dist_eq_sub_of_le (by linarith [h])]
  exact sub_succ_lt_self (j - i) 0 (zero_lt_of_lt (Nat.lt_sub_iff_add_lt'.mpr h))

theorem Nat.dist_lt_of_decrease_greater {i j: ℕ} (h : i+1<j) :
    Nat.dist i (j-1) < Nat.dist i j := by
  have i_lt_j_minus_1 := Nat.le_of_succ_le (Nat.lt_sub_of_add_lt h)
  rw [Nat.dist_eq_sub_of_le i_lt_j_minus_1, Nat.dist_eq_sub_of_le (by linarith [h])]
  apply (Nat.sub_lt_sub_iff_right i_lt_j_minus_1).mpr
  exact Nat.sub_lt (Nat.one_le_of_lt h) Nat.one_pos
