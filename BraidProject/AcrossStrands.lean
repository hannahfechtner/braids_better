import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.Linarith

theorem mem_nil : (a : α) ∈ (∅ : Finset α) ↔ False := List.mem_nil_iff a


open FreeMonoid

local instance : Coe ℕ (FreeMonoid ℕ) :=
  ⟨of⟩

def count_up_helper : ℕ → ℕ → ℕ → FreeMonoid ℕ
| 0, _, _ => 1
| n+1, i, j => (of i) * (count_up_helper n (i+1) j)

def count_up (i j : ℕ) : FreeMonoid ℕ := count_up_helper (j - i) i j

def count_down_helper : ℕ → ℕ → ℕ → FreeMonoid ℕ
| 0, _, _ => 1
| n+1, i, j => (count_down_helper n i (j+1)) * (j)

def count_down (i j : ℕ) : FreeMonoid ℕ := count_down_helper (i - j) i j

set_option profiler true

theorem not_dense : j < k → k < j+1 → False := by
  intro lower upper
  cases Nat.lt_trichotomy k (j+1)
  · have : k < j ∨ k = j := by exact Nat.lt_succ_iff_lt_or_eq.mp upper
    cases this
    · rename_i k_lt_j
      exact Nat.lt_asymm lower k_lt_j
    rename_i this
    rw [this] at lower
    exact Nat.not_lt.mpr Nat.le.refl lower
  rename_i last_two
  cases last_two
  · rename_i eq
    rw [eq] at upper
    exact Nat.not_lt.mpr Nat.le.refl upper
  rename_i lt
  exact Nat.not_lt.mpr Nat.le.refl (lt.trans upper)

theorem count_up_pop {b n : ℕ} {h : n > b} : count_up b n =
                  (count_up b (n-1)) * (of (n-1)) := by
  have H : ∀ t, ∀ i j, j-i = t → i < j → count_up i j = (count_up i (j-1)) * ↑(j-1) := by
    intro t
    induction t
    · intro i j h1 lt
      exfalso
      have ij : i=j := by
        apply Nat.le_antisymm
        · exact Nat.le_of_lt lt
        exact Nat.le_of_sub_eq_zero h1
      linarith [ij, lt]
    rename_i h hk
    intro k l eq_h lt
    cases Nat.lt_trichotomy (k + 1) l
    · next plus_one_lt =>
      have sub : l-(k+1)=h := by
        rw [Nat.sub_succ l k, eq_h]
        rfl
      conv => lhs; unfold count_up
      rw [eq_h]
      simp only [count_up_helper, ge_iff_le, tsub_le_iff_right]
      have H := hk (k+1) l sub plus_one_lt
      unfold count_up at H
      rw [← sub, H]
      have H : k * count_up_helper (l - 1 - (k + 1)) (k + 1) (l - 1) = count_up_helper (l - 1 - k) k (l - 1) := by
        conv => rhs; unfold count_up
        have H : l-1-k=Nat.succ (l-1 - (k+1)) := by
          have bigger_zero: l-1-k >0 := by
            rw [(tsub_add_eq_tsub_tsub_swap l k 1).symm]
            exact Nat.sub_pos_of_lt plus_one_lt
          exact (Nat.succ_pred_eq_of_pos bigger_zero).symm
        simp only [H]
        rfl
      rw [← mul_assoc, H]
      rfl
    next eq_or_gt =>
    cases eq_or_gt
    · next eq_case =>
      rw [← eq_case]
      simp only [count_up, add_tsub_cancel_left, count_up_helper, length_one, mul_one,
        add_tsub_cancel_right, ge_iff_le, le_refl, tsub_eq_zero_of_le, length_eq_zero,
        one_mul]
    next gt_case =>
    exfalso
    exact not_dense lt gt_case
  apply H (n-b)
  · simp only
  exact h

theorem count_down_pop {i j : ℕ} { h : i <= j} : count_down (j+1) i =
                  j * (count_down j i) := by
  have H : ∀ t, ∀ i j, j-i = t → i <= j → count_down (j+1) i =
                  j * (count_down j i) := by
    intro t
    induction t
    · intro i j h1 lt
      rw [Nat.le_antisymm lt <| Nat.le_of_sub_eq_zero h1]
      simp only [ge_iff_le, add_le_iff_nonpos_right, add_tsub_cancel_left, le_refl,
        tsub_eq_zero_of_le, count_down, count_down_helper, mul_one, one_mul]
    rename_i h hk
    intro k l eq_h lt
    cases le_or_gt (k + 1) l
    · next plus_one_lt =>
      specialize hk (k+1) (l)
      have sub : l-(k+1)=h := by
        rw [Nat.sub_succ l k, eq_h]
        rfl
      specialize hk sub plus_one_lt
      conv => lhs; unfold count_down count_down_helper
      rw [Nat.succ_sub lt]
      simp only
      have H : count_down_helper (l - k) (l + 1) (k + 1) = count_down (l + 1) (k + 1) := by
        unfold count_down
        have H2 : l + 1 - (k + 1) = l - k := by omega
        rw [H2]
      rw [H, hk]
      conv => rhs; unfold count_down count_down_helper
      rw [eq_h, mul_assoc, mul_right_inj]
      simp only
      rw [ ← sub]
      rfl
    next gt =>
    rw [(Nat.eq_of_le_of_lt_succ lt gt).symm]
    unfold count_down count_down_helper
    simp only [add_tsub_cancel_left, one_mul, ge_iff_le, le_refl, tsub_eq_zero_of_le, mul_one]
    rfl
  apply H (j-i)
  · rfl
  exact h

-- FreeMonoid counting between two numbers, including the little and excluding the highest
def sigma_bar (i j : ℕ) : FreeMonoid (ℕ) :=
  if i = j then 1 else if i < j then count_up i j else count_down i j

theorem sigma_bar_last {i j : ℕ} (h: i<j) : sigma_bar i j = sigma_bar i (j - 1) * (of (j-1)) := by
  induction j, h using Nat.le_induction
  · induction i
    · unfold sigma_bar
      simp only [Nat.zero_eq, Nat.reduceSucc, zero_ne_one, ↓reduceIte, zero_lt_one, tsub_zero,
        ge_iff_le, le_refl, tsub_eq_zero_of_le, one_mul]
      exact rfl
    rename_i n _
    simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero, add_eq_zero, and_false, tsub_zero]
    unfold sigma_bar
    simp only [Nat.succ.injEq, left_eq_add, one_ne_zero, ↓reduceIte, Nat.lt_succ_self,
      Nat.succ_sub_succ_eq_sub, add_tsub_cancel_left, one_mul, count_up]
    rfl
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
      simp only [Nat.zero_eq, zero_add, one_ne_zero, ↓reduceIte, not_lt_zero', tsub_zero, mul_one]
      exact rfl
    -- i = n+1
    rename_i n _
    unfold sigma_bar
    simp only [add_eq_left, add_lt_iff_neg_left, ge_iff_le, le_add_iff_nonneg_right, tsub_eq_zero_of_le,
      add_le_iff_nonpos_right, add_tsub_cancel_left, ite_false, lt_self_iff_false, le_refl, ite_true, count_down]
    rfl
  --j = k+1
  rename_i n n_is _
  have h1 : ¬ n + 1 + 1 = i := by omega
  have h2 : ¬ n + 1 + 1 < i := by omega
  simp only [sigma_bar, h1, h2, ge_iff_le, ite_false]
  rw [count_down_pop]
  have h' : ¬ n + 1 = i := by linarith [n_is]
  have h'' : ¬ n + 1 < i := by linarith [n_is]
  simp only [ge_iff_le, h', h'', ite_false]
  exact Nat.le.step n_is

theorem sigma_bar_first {i j : ℕ} (h: i<j) : sigma_bar i j = of i * (sigma_bar (i+1) j) := by
  induction j, h using Nat.le_induction
  · induction i
    · unfold sigma_bar
      simp only [Nat.zero_eq, Nat.reduceSucc, zero_ne_one, ↓reduceIte, zero_lt_one, tsub_zero,
        zero_add, mul_one]
      exact rfl
    rename_i n _
    unfold sigma_bar
    simp only [Nat.succ.injEq, left_eq_add, Nat.lt_succ_self, ge_iff_le, Nat.succ_sub_succ_eq_sub,
      add_le_iff_nonpos_right, add_tsub_cancel_left, le_add_iff_nonneg_right, tsub_eq_zero_of_le, ite_true, ite_false,
      lt_self_iff_false, le_refl, count_up]
    rfl
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
      simp only [Nat.zero_eq, Nat.reduceSucc, one_ne_zero, ↓reduceIte, not_lt_zero', tsub_zero,
        zero_add, one_mul]
      exact rfl
    rename_i k _
    unfold sigma_bar
    have : ¬ Nat.succ (Nat.succ k) < Nat.succ k := by
      intro h
      apply Nat.not_lt.mpr (Nat.le.step Nat.le.refl)
      exact Nat.succ_lt_succ_iff.mp h
    simp only [Nat.succ.injEq, add_eq_left, one_ne_zero, ↓reduceIte, this,
      Nat.succ_sub_succ_eq_sub, add_tsub_cancel_left, one_mul, count_down]
    rfl
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
    simp only [count_up, Nat.succ_eq_add_one, add_tsub_cancel_left, count_up_helper, length_one,
      mul_one, length_of]
  rename_i h lt_k ih
  rw [sigma_bar_last]
  · rw [add_tsub_cancel_right, length_mul, ih, FreeMonoid.length_of]
    exact (Nat.sub_add_comm (Nat.lt_succ.mp (Nat.le.step lt_k))).symm
  exact Nat.le.step lt_k

theorem count_up_bounded (k : ℕ) {j : ℕ} : j ∈ (count_up 1 k.succ) → j < Nat.succ k := by
    intro h
    induction k
    · exfalso
      exact not_mem_one h
    rename_i n hn
    have h1 : j ∈ (count_up 1 (Nat.succ (Nat.succ n))) := by
      simp only [count_up, Nat.succ_sub_succ_eq_sub, tsub_zero]
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
  exact NeZero.one_le

theorem map_count_up_bounded (n k : ℕ): ∀ x, x ∈ (FreeMonoid.map (fun x => x +k)) (count_up 0 n) →
    x < (n + k) := by
  intro x x_in
  induction n
  · simp only [count_up, count_up_helper, length_one, map_one, length_eq_zero] at x_in
    exact (not_mem_one x_in).elim
  rename_i n ih
  rcases n
  · simp only [count_up, count_up_helper, length_one, mul_one, map_of, zero_add, mem_of] at x_in
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
      simp only [tsub_zero, zero_add, mem_mul, mem_of, count_up, count_up_helper] at hw
      rcases hw.1 with w_is | w_in
      · rw [w_is]
        exact Fin.pos ⟨m, Nat.le.step Nat.le.refl⟩
      exact Nat.le.step (@count_up_bounded m w w_in)
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
  simp only [Nat.succ_ne_zero, not_lt_zero', ge_iff_le, zero_le, tsub_eq_zero_of_le, nonpos_iff_eq_zero, tsub_zero,
    ite_false] at k_in
  cases (mem_mul.mp k_in)
  · next left =>
    simp only [zero_add] at left
    exact count_down_bounded _ left
  next right =>
  rw [mem_of.mp right]
  exact Fin.pos { val := n, isLt := Nat.le.refl }

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
  · simp only [sigma_bar, zero_add, zero_ne_one, ↓reduceIte, zero_lt_one, count_up, length_one,
    mul_one, map_of, mem_of, count_up_helper] at h
    rw [h]
    linarith
  simp only [right_eq_add, add_eq_zero, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
    lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, tsub_zero, mem_map] at h
  rcases h with ⟨m, hm, hm2⟩
  apply map_count_up_bounded _ _ _
  rw [← hm2]
  apply mem_map.mpr
  use m
  exact ⟨hm, rfl⟩
