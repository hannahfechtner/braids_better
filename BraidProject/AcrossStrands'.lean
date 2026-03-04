import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.Linarith
import BraidProject.Additions.Finset
import BraidProject.Additions.NatDist
import BraidProject.Additions.FreeMonoid

open FreeMonoid

local instance : Coe ℕ (FreeMonoid ℕ) := ⟨of⟩

/- gives a list of natural numbers from i (inclusive) up to j (exclusive) -/
def count_up (i j : ℕ) : FreeMonoid ℕ := if i < j then i * count_up (i+1) j else 1

/- gives a list of natural numbers from i (exclusive) down to j (inclusive) -/
def count_down (i j : ℕ) : FreeMonoid ℕ := (count_up j i).reverse

set_option profiler true

@[simp]
theorem count_up_self : count_up i i = 1 := by
  unfold count_up; simp

@[simp]
theorem count_down_self : count_down i i = 1 := by
  unfold count_down; simp

@[simp]
theorem count_up_succ : count_up i (i+1) = of i := by
  unfold count_up; simp [count_up_self]

@[simp]
theorem count_down_succ : count_down (i+1) i = of i := by
  unfold count_down; simp [count_up_self]

@[simp]
theorem count_up_succ_succ : count_up i (i+2) = of i  * of (i + 1) := by
  unfold count_up; simp [count_up_self]

@[simp]
theorem count_down_succ_succ : count_down (i+2) i = of (i + 1) * of i:= by
  unfold count_down; simp [count_up_self, FreeMonoid.reverse_mul]

theorem count_up_empty_iff : count_up i j = 1 ↔ j ≤ i := by
  unfold count_up; simp

theorem count_down_empty_iff : count_down i j = 1 ↔ i ≤ j := by
  unfold count_down
  have := @reverse_eq_one _ (count_up j i)
  have := @count_up_empty_iff j i
  aesop

theorem count_up_pop {b n : ℕ} (h : b < n) : count_up b n = count_up b (n - 1) * of (n - 1) := by
  have : ∀ t, ∀ i j, j - i = t → i < j → count_up i j = count_up i (j - 1) * ↑(j - 1) := by
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
      · have : i = j - 1 := by omega
        rw [eq', this, count_up_self, count_up_self, mul_one, one_mul]
      linarith
  exact this (n-b) _ _ rfl h

theorem count_down_first {i j : ℕ} (h : i ≤ j) : count_down (j+1) i = ↑j * count_down j i := by
  unfold count_down
  rw [count_up_pop]
  · simp [FreeMonoid.reverse_mul]
  linarith

theorem count_down_pop {i j : ℕ} (h : i < j) : count_down j i = count_down j (i + 1) * ↑i := by
  unfold count_down
  conv => lhs; unfold count_up
  split
  · rw [reverse_mul, reverse_of]
  rw [reverse_mul, reverse_of]

theorem count_up_bounded (k : ℕ) {j b : ℕ} : j ∈ count_up b k → j < k := by
  intro h
  rcases Nat.lt_or_ge b k with lt | ge
  · induction k with
    | zero => aesop
    | succ n ih =>
      rw [count_up_pop] at h
      simp only [add_tsub_cancel_right, mem_mul, mem_of] at h
      rcases h with h1 | h2
      · rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
        · exact Nat.lt_add_right 1 (ih h1 lt)
        rw [count_up_self] at h1
        exact (not_mem_one h1).elim
      linarith
      assumption
  rw [count_up_empty_iff.mpr ge] at h
  exact (not_mem_one h).elim

theorem count_down_bounded (k : ℕ) {j : ℕ} : j ∈ count_down k b → j < k := by
  intro h
  rw [count_down, mem_reverse] at h
  exact count_up_bounded _ h

theorem map_count_up_bounded (n k : ℕ) : ∀ x, x ∈ FreeMonoid.map (fun x => x + k)
    (count_up b n) → x < (n + k) := by
  intro x x_in
  rcases FreeMonoid.mem_map.mp x_in with ⟨m, m_in, m_eq⟩
  apply count_up_bounded at m_in
  linarith

-- FreeMonoid word counting from i to j, including the smaller and excluding the larger
def sigma_braid (i j : ℕ) : FreeMonoid ℕ :=
  if i ≤ j then count_up i j else count_down i j

theorem sigma_braid_self {i} : sigma_braid i i = 1 := by
  unfold sigma_braid
  simp

theorem sigma_braid_succ_ascending {i} : sigma_braid i (i + 1) = of i := by
  unfold sigma_braid
  simp

theorem sigma_braid_succ_descending {i} : sigma_braid (i + 1) i = of i := by
  unfold sigma_braid
  simp

theorem sigma_braid_succ_succ_ascending {i} : sigma_braid i (i + 2) = of i * of (i + 1) := by
  unfold sigma_braid count_up
  simp

theorem sigma_braid_succ_succ_descending {i} : sigma_braid (i + 2) i = of (i + 1) * of i := by
  unfold sigma_braid count_up count_down
  simp [FreeMonoid.reverse_mul]

theorem sigma_braid_ascending_first {i j : ℕ} (h: i < j) : sigma_braid i j =
    of i * sigma_braid (i + 1) j := by
  simp only [sigma_braid, mul_ite]
  split
  · next h1 =>
    split
    · next h3 =>
      conv => lhs; unfold count_up
      simp [h]
    linarith
  next h2 =>
  linarith

theorem sigma_braid_ascending_pop {i j : ℕ} (h: i < j) : sigma_braid i j = sigma_braid i (j - 1) *
    of (j-1) := by
  simp only [sigma_braid, mul_ite]
  split
  · next h1 =>
    split
    · next h2 => exact count_up_pop h
    next h3 =>
    have : i = j - 1 := by omega
    rw [this, count_down_self, one_mul]
    have : j = (j - 1) + 1 := by omega
    conv =>
    {
      enter [1, 2]
      rw [this]
    }
    exact count_up_succ
  next h2 =>
  linarith

theorem sigma_braid_descending_first {i j : ℕ} (h: i ≥ j) :
    sigma_braid (i + 1) j = (of i) * sigma_braid i j := by
  simp only [sigma_braid, mul_ite]
  split
  · next h1 => linarith
  next h2 =>
  split
  · rw [count_down_first h]
    have : i = j := by linarith
    rw [this, count_down_self, count_up_self]
  rw [count_down_first h]

theorem sigma_braid_descending_pop {i j : ℕ} (h: i<j) : sigma_braid j i = sigma_braid j (i + 1) *
    (of i : FreeMonoid ℕ) := by
  simp only [sigma_braid, ite_mul]
  split
  · next h1 => linarith
  next h2 =>
  split
  · next h3 =>
    have : j = i + 1 := by linarith
    rw [this, count_down_succ, count_up_self, one_mul]
  rw [count_down_pop h]

theorem sigma_braid_length {i j : ℕ} (h : i < j) : length (sigma_braid i j) = j - i := by
  induction j, h using Nat.le_induction with
  | base => unfold sigma_braid; simp
  | succ h lt_k ih =>
    rw [sigma_braid_ascending_pop]
    · rw [add_tsub_cancel_right, length_mul, ih, FreeMonoid.length_of]
      exact (Nat.sub_add_comm (Nat.lt_succ.mp (Nat.le.step lt_k))).symm
    exact Nat.le.step lt_k

theorem sigma_braid_ascending_bounded (n : ℕ) {k : ℕ}: k ∈ (sigma_braid n 0) → k < n := by
  intro k_in
  unfold sigma_braid at k_in
  cases n with
  | zero =>
    simp only [le_refl, ↓reduceIte, count_up_self] at k_in
    exact (not_mem_one k_in).elim
  | succ n =>
    simp only [nonpos_iff_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte] at k_in
    exact count_down_bounded _ k_in

theorem sigma_braid_descending_bounded (n : ℕ) {k : ℕ}: k ∈ sigma_braid 0 n → k < n := by
  intro k_in
  unfold sigma_braid at k_in
  simp only [zero_le, ↓reduceIte] at k_in
  exact count_up_bounded _ k_in

theorem map_sigma_braid_bounded (n k : ℕ): ∀ x, x ∈ (FreeMonoid.map (fun x => x + k)) (sigma_braid 0 n) →
    x < (n + k) := by
  intro x h
  rcases mem_map.mp h with ⟨w, w_in, rfl⟩
  linarith [sigma_braid_descending_bounded _ w_in]
