import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.Linarith
import BraidProject.Additions.Finset
import BraidProject.Additions.NatDist
import BraidProject.Additions.FreeMonoid

open FreeMonoid

local instance : Coe ℕ (FreeMonoid ℕ) :=
  ⟨of⟩

/- gives a list of natural numbers from i (inclusive) up to j (exclusive) -/
def count_up (i j : ℕ) : FreeMonoid ℕ := if i < j then i * count_up (i+1) j else 1

/- gives a list of natural numbers from i (exclusive) down to j (inclusive) -/
def count_down (i j : ℕ) : FreeMonoid ℕ := (count_up j i).reverse

set_option profiler true

@[simp]
theorem count_up_self : count_up i i = 1 := by
  unfold count_up
  simp

@[simp]
theorem count_down_self : count_down i i = 1 := by
  unfold count_down
  simp

@[simp]
theorem count_up_succ : count_up i (i+1) = of i := by
  unfold count_up
  simp [count_up_self]

@[simp]
theorem count_down_succ : count_down (i+1) i = of i := by
  unfold count_down
  simp [count_up_self]

theorem count_up_pop {b n : ℕ} {h : b < n} : count_up b n =
                  (count_up b (n-1)) * (of (n-1)) := by
  have H : ∀ t, ∀ i j, j-i = t → i < j → count_up i j = (count_up i (j-1)) * ↑(j-1) := by
    intro t
    induction t with
    | zero =>
      omega
    | succ n ih =>
      intro i j eq_n lt
      conv => lhs; unfold count_up
      simp only [lt, ↓reduceIte]
      specialize ih (i+1) j (by omega)
      rcases Nat.lt_trichotomy (i + 1) j with lt' | eq' | gt
      · rw [ih lt']
        conv => rhs; unfold count_up
        have : i < j - 1 := by omega
        simp only [this, ↓reduceIte, mul_assoc]
      · have : i = j-1 := by omega
        rw [eq', this, count_up_self, count_up_self, mul_one, one_mul]
      linarith
  exact H (n-b) _ _ rfl h

theorem count_down_pop {i j : ℕ} {h : i < j} : count_down j i =
                  ↑(j-1) * (count_down (j-1) i) := by
    unfold count_down
    rw [count_up_pop]
    · simp [FreeMonoid.reverse_mul]
    exact h

-- FreeMonoid word counting between two numbers, including the little and excluding the highest
def sigma_bar (i j : ℕ) : FreeMonoid (ℕ) :=
  if i = j then 1 else if i < j then count_up i j else count_down i j

theorem sigma_bar_last {i j : ℕ} (h: i<j) : sigma_bar i j = sigma_bar i (j - 1) * (of (j-1)) := by
  induction j, h using Nat.le_induction
  · induction i
    · unfold sigma_bar
      simp only [Nat.zero_eq, Nat.reduceSucc, zero_ne_one, ↓reduceIte, zero_lt_one, tsub_zero,
        ge_iff_le, le_refl, tsub_eq_zero_of_le, one_mul, count_up_succ]
    rename_i n _
    simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero, add_eq_zero, and_false, tsub_zero]
    unfold sigma_bar
    simp only [Nat.succ_eq_add_one, Nat.add_left_inj, left_eq_add, one_ne_zero, ↓reduceIte,
      lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, count_up_succ, one_mul]
  rename_i n n_is _
  simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
  conv => lhs; unfold sigma_bar
  have h1 : ¬ i = n + 1 := by
    intro i_is
    rw [i_is] at n_is
    exact Nat.not_lt.mpr n_is <| Nat.le.step Nat.le.refl
  have h2 : i<n+1 := Nat.le.step n_is
  simp only [h1, h2]
  rw [count_up_pop]
  simp only [↓reduceIte, add_tsub_cancel_right, mul_left_inj]
  have h' : ¬i=n := by
    intro i_is
    rw [i_is] at n_is
    exact Nat.not_lt.mpr n_is Nat.le.refl
  have h'' : i<n := n_is
  unfold sigma_bar
  simp only [ge_iff_le, h', h'', ite_true, ite_false]
  exact h2

theorem sigma_bar_big_first {i j : ℕ} (h: i<=j) : sigma_bar (j+1) i = (of j) * sigma_bar j i := by
  induction j, h using Nat.le_induction
  · -- kind of j=0; in this case, we know j>=i, so we can just start at j=i
    induction i
    · --i=0
      unfold sigma_bar
      simp
    -- i = n+1
    rename_i n _
    unfold sigma_bar
    simp
  --j = k+1
  rename_i n n_is _
  have h1 : ¬ n + 1 + 1 = i := by omega
  have h2 : ¬ n + 1 + 1 < i := by omega
  simp only [sigma_bar, h1, h2, ge_iff_le, ite_false]
  rw [count_down_pop]
  have h' : ¬ n + 1 = i := by linarith [n_is]
  have h'' : ¬ n + 1 < i := by linarith [n_is]
  simp [ge_iff_le, h', h'', ite_false]
  linarith

theorem sigma_bar_first {i j : ℕ} (h: i<j) : sigma_bar i j = of i * (sigma_bar (i+1) j) := by
  induction j, h using Nat.le_induction
  · induction i
    · unfold sigma_bar
      simp
    rename_i n _
    unfold sigma_bar
    simp
  rename_i n n_is ih
  have h : i<n+1 := by
    have H1 : i < i.succ := by exact Nat.le.refl
    exact H1.trans (Nat.lt_succ.mpr n_is)
  rw [sigma_bar_last h, sigma_bar_last (Nat.add_lt_add_right n_is 1)]
  simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
  rw [ih, mul_assoc]

theorem sigma_bar_big_last {i j : ℕ} (h: i<j) : sigma_bar j i = sigma_bar j (i + 1) * (of i : FreeMonoid ℕ) := by
  induction j, h using Nat.le_induction
  · induction i
    · unfold sigma_bar
      simp
    rename_i k _
    unfold sigma_bar
    have : ¬ Nat.succ (Nat.succ k) < Nat.succ k := by
      intro h
      apply Nat.not_lt.mpr (Nat.le.step Nat.le.refl)
      exact Nat.succ_lt_succ_iff.mp h
    simp
  rename_i k lt_k ih
  rw [sigma_bar_big_first lt_k, sigma_bar_big_first, mul_assoc, mul_right_inj]
  · exact ih
  exact Nat.lt_succ.mp (Nat.le.step lt_k)

--no induction principle needed
theorem sigma_length {i j : ℕ} (h : i<j) : length (sigma_bar i j) = j-i := by
  induction j, h using Nat.le_induction
  · unfold sigma_bar
    simp only [(Nat.ne_of_lt Nat.le.refl), Nat.lt_succ_self, ge_iff_le, ite_true, ite_false]
    have : Nat.succ i - i = 1 := tsub_eq_of_eq_add_rev rfl
    rw [this]
    simp
  rename_i h lt_k ih
  rw [sigma_bar_last]
  · rw [add_tsub_cancel_right, length_mul, ih, FreeMonoid.length_of]
    exact (Nat.sub_add_comm (Nat.lt_succ.mp (Nat.le.step lt_k))).symm
  exact Nat.le.step lt_k

theorem count_up_bounded (k : ℕ) {j : ℕ} : j ∈ (count_up 1 k.succ) → j < Nat.succ k := by
    intro h
    induction k
    · simp only [Nat.succ_eq_add_one, zero_add, count_up_self] at h
      exact (not_mem_one h).elim
    rename_i n hn
    have h1 : j ∈ (count_up 1 (Nat.succ (Nat.succ n))) := by
      simp only [Nat.succ_eq_add_one]
      exact h
    rw [@count_up_pop 1 (Nat.succ (Nat.succ n)) _] at h1
    rw [mem_mul] at h1
    simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, add_tsub_cancel_right, Finset.mem_union] at h1
    cases h1
    · next left_case =>
      exact (hn left_case).trans Nat.le.refl
    next right_case =>
      rw [mem_of.mp right_case]
      exact Nat.le.refl
    linarith

theorem count_down_bounded (k : ℕ) {j : ℕ} : j ∈ (count_down (Nat.succ k) 1) → j < Nat.succ k := by
  intro h
  induction k
  · exfalso
    rw [count_down_self] at h
    exact not_mem_one h
  rename_i n hn
  have h1 : j ∈ (count_down (Nat.succ (Nat.succ n)) 1) := by
    simp only [count_down, Nat.succ_sub_succ_eq_sub, tsub_zero]
    exact h
  rw [count_down_pop] at h1
  · rw [mem_mul] at h1
    cases h1
    · next eq_n_plus_one =>
      rw [mem_of.mp eq_n_plus_one]
      exact Nat.le.refl
    next use_ih =>
    exact Nat.le.step (hn use_ih)
  linarith

theorem map_count_up_bounded (n k : ℕ): ∀ x, x ∈ (FreeMonoid.map (fun x => x +k)) (count_up 0 n) →
    x < (n + k) := by
  intro x x_in
  induction n
  · simp only [count_up_self, map_one] at x_in
    exact (not_mem_one x_in).elim
  rename_i n ih
  rcases n
  · simp only [zero_add, count_up_succ, map_of, mem_of] at x_in
    rw [x_in]
    exact Nat.lt_one_add_iff.mpr Nat.le.refl
  rename_i m
  rw [count_up_pop] at x_in
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, _root_.map_mul, map_of, mem_mul, mem_map,
    mem_of] at x_in
  rcases x_in
  · rename_i ih2
    rcases ih2 with ⟨w, hw⟩
    rw [← hw.2]
    have H : w < m.succ.succ := by
      unfold count_up at hw
      simp at hw
      rcases hw.1 with ⟨h1 | h2⟩
      · linarith
      have H := (@count_up_bounded m w) (by assumption)
      linarith
    exact Nat.add_lt_add_right H k
  rename_i x_is
  rw [x_is]
  exact Nat.add_lt_add_right Nat.le.refl k
  linarith

theorem sigma_bar_bounded (n : ℕ) {k : ℕ}: k ∈ (sigma_bar n 0) → k < n := by
  intro k_in
  induction n
  · exfalso
    exact not_mem_one k_in
  rename_i n _
  unfold sigma_bar at k_in
  rw [count_down, count_up] at k_in
  simp at k_in
  have : k ∈ count_up 0 (n + 1) := by sorry -- mem_reverse
  exact count_up_bounded _ this -- generalize count_up_bounded for any lower bound

theorem sigma_bar_bounded' (n : ℕ) {k : ℕ}: k ∈ sigma_bar 0 n → k < n := by
  intro k_in
  induction n
  · exfalso
    exact not_mem_one k_in
  rename_i n n_ih
  rw [sigma_bar_last <| Nat.lt_of_le_of_lt (Nat.zero_le n) (Nat.le.refl)] at k_in
  cases (mem_mul.mp k_in)
  · next left =>
    exact Nat.le.step (n_ih left)
  next right =>
  rw [mem_of.mp right]
  exact Nat.le.refl

theorem map_sigma_bar_bounded (n k : ℕ): ∀ x, x ∈ (FreeMonoid.map (fun x => x + k)) (sigma_bar 0 n) →
    x < (n + k) := by
  intro x h
  rcases n
  · unfold sigma_bar at h
    simp only [Nat.zero_eq, ↓reduceIte, _root_.map_one] at h
    exact (mem_nil.mp h).elim
  rename_i n
  induction n
  · simp only [sigma_bar, zero_add, zero_ne_one, ↓reduceIte, Nat.lt_one_iff, pos_of_gt,
    count_up_succ, map_of, mem_of] at h
    linarith
  simp only [right_eq_add, add_eq_zero, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
    lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, tsub_zero, mem_map] at h
  rcases h with ⟨m, hm, hm2⟩
  apply map_count_up_bounded _ _ _
  rw [← hm2]
  apply mem_map.mpr
  use m
  exact ⟨hm, rfl⟩
