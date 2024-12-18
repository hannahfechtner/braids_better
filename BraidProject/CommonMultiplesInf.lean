import BraidProject.BraidMonoid
import BraidProject.SigmaBar
import BraidProject.InductionWithBounds
import BraidProject.FreeMonoid_mine
--part two : common right multiples


open FreeMonoid'
-- --lemma 3.9 property
def three_nine (i j : ℕ) := ∀ k,  j>=i+2 → i<k∧k<j → BraidMonoidInf.mk (of k * sigma_neg i j) =
    BraidMonoidInf.mk (sigma_neg i j * of (k-1))

-- --lemma 3.10 property
def three_ten (i j : ℕ) := ∀ k,  j>=i+2 → i<k∧k<j → (BraidMonoidInf.mk (of (k-1) * sigma_neg j i) =
  BraidMonoidInf.mk (sigma_neg j i * of k))

theorem ad_step (h : i+1<j) : 3 <= Nat.dist i j →  2 ≤ Nat.dist (i + 1) j := by
  intro three
  apply or_dist_iff.mpr
  rcases or_dist_iff.mp three with h1 | h2
  · exact Or.inl h1
  exfalso
  linarith


--these should all go in the braid monoid file. or rather, they should go in the presentedmonoid file
-- theorem BraidMonoidInf.append_left_mk {a b c : FreeMonoid' ℕ} (h : BraidMonoidInf.mk b = BraidMonoidInf.mk c) :
--   BraidMonoidInf.mk (a * b) = BraidMonoidInf.mk (a * c) := by
--   show BraidMonoidInf.mk a * BraidMonoidInf.mk b = BraidMonoidInf.mk a * BraidMonoidInf.mk c
--   rw [h]

-- theorem BraidMonoidInf.append_right_mk {a b c : FreeMonoid' ℕ} (h : BraidMonoidInf.mk b = BraidMonoidInf.mk c) :
--   BraidMonoidInf.mk (b * a) = BraidMonoidInf.mk (c * a) := by
--   show BraidMonoidInf.mk b * BraidMonoidInf.mk a = BraidMonoidInf.mk c * BraidMonoidInf.mk a
--   rw [h]

theorem prepend_k' (i j k : ℕ) (h1: j>=i+2) (h2 : i<k∧k<j) :
      BraidMonoidInf.mk (of k * (sigma_neg i j)) = BraidMonoidInf.mk ((sigma_neg i j) * (of (k-1))) := by
  have i_lt_j : i<j := by linarith [h1]
  have H : 2 ≤ j-i := by exact Nat.le_sub_of_add_le' h1
  apply induction_above_diff i j H three_nine _ _ _ h1 h2
  · intro i' j' j'i' k' worthless tween
    unfold sigma_neg
    have lt : i'<j' := Nat.lt_of_sub_eq_succ j'i'
    have H : k' = i' + 1 := by sorry
    rw [H]
    simp [lt, Nat.ne_of_lt lt]
    rw [j'i']
    symm
    apply BraidMonoidInf.braid
    exact dist_succ
  intro i' j' ge_three ih k' _ h2'
  have H : k' = i' + 1 ∨ k' >= i' + 2 := by
    rcases Nat.lt_or_ge k' (i' + 1) with ha | hb
    · exfalso
      linarith [h2'.1]
    exact LE.le.eq_or_gt hb
  have ha : 2 ≤ j' - 1 - i' := by
    refine Nat.le_sub_of_add_le' ?_
    refine (Nat.lt_iff_le_pred ?_).mp ?_
    · exact Nat.zero_lt_of_lt (by assumption)
    exact Nat.add_lt_of_lt_sub' ge_three
  have hb : j' - 1 - i' < j' - i' := by
    have H : j' >= 1 := Nat.one_le_of_lt (by assumption)
    refine (Nat.sub_lt_sub_iff_right ?_).mpr ?_
    · refine Nat.le_sub_one_of_lt ?refine_1.a
      exact h2'.1.trans h2'.2
    refine Nat.sub_lt H ?refine_2.a
    exact Nat.one_pos
  have hc : j' - 1 ≥ i' + 2 := by
    refine Nat.le_sub_one_of_lt ?_
    exact Nat.add_lt_of_lt_sub' ge_three
  rcases H with base | other
  · rw [base]
    have H2 : BraidMonoidInf.mk (of (i'+1) * (sigma_neg i' (j'-1))) = BraidMonoidInf.mk
        ((sigma_neg i' (j'-1)) * of i') :=
      ih (i') (j'-1) ha
        hb (i'+1) hc ⟨Nat.lt.base i', hc⟩
    have H7: (of (i'+1) * (sigma_neg i' j')) =
        of (i'+1) * ((sigma_neg i' (j'-1)))* of (j'-1) := by
      rw [mul_assoc, mul_right_inj]
      apply sigma_neg_last (h2'.1.trans h2'.2)
    have H9 : BraidMonoidInf.mk ((sigma_neg i' (j'-1)) * of i' * of (j'-1)) =
        BraidMonoidInf.mk ((sigma_neg i' (j'-1)) * of (j'-1) * of i') := by
      rw [mul_assoc, mul_assoc]
      apply BraidMonoidInf.append_left_mk <| BraidMonoidInf.comm (or_dist_iff.mpr (Or.inl hc))
    have H10 : ((sigma_neg i' (j'-1))* of (j'-1) * of (i')) =
        (sigma_neg (i') j') * of ((i'+1)-1) := by
      simp only [add_tsub_cancel_right, mul_left_inj]
      rw [← sigma_neg_last (h2'.1.trans h2'.2)]
    rw [H7, ← H10]
    apply @BraidMonoidInf.append_right_mk _ _ (of (j'-1)) at H2
    exact H2.trans H9
  have H7: (of k' * (sigma_neg i' j')) = of k' * of i' * (sigma_neg (i'+1) j') := by
    rw [mul_assoc, mul_right_inj]
    exact sigma_neg_first (h2'.1.trans h2'.2)
  have H8 : BraidMonoidInf.mk (of k' * of i' * (sigma_neg (i'+1) j')) = BraidMonoidInf.mk
                      (of i' * of k' * (sigma_neg (i'+1) j')) :=
    -- from the original braid rels, because i and k are far enough apart
    BraidMonoidInf.append_right_mk (BraidMonoidInf.comm
      (or_dist_iff.mpr (Or.inl other))).symm
  have H9 : BraidMonoidInf.mk (of i' * (of k' * (sigma_neg (i'+1) j'))) =
      BraidMonoidInf.mk (of i' * ((sigma_neg (i'+1) j') * of (k'-1))) := by
    have H10 : BraidMonoidInf.mk ((of k' * (sigma_neg (i'+1) j'))) =
        BraidMonoidInf.mk (((sigma_neg (i'+1) j') * of (k'-1))) := by
      apply ih
      · refine Nat.le_sub_of_add_le' ?_
        refine Nat.succ_le_of_lt ?_
        exact Nat.add_lt_of_lt_sub' ge_three
      · refine Nat.sub_succ_lt_self j' i' ?_
        exact h2'.1.trans h2'.2
      · simp only [ge_iff_le]
        linarith [h2'.2, other]
      exact And.imp_left (fun a ↦ other) h2'
    apply BraidMonoidInf.append_left_mk
    rw [H10]
  rw [H7, mul_assoc, sigma_neg_first (h2'.1.trans h2'.2)]
  exact H8.trans H9

theorem prepend_k (i j k : ℕ) (h1: j>=i+2) (h2 : i<k∧k<j) :
      BraidMonoidInf.mk (of k * (sigma_neg i j)) = BraidMonoidInf.mk ((sigma_neg i j) * (of (k-1))) := by
  have H_absdiff : Nat.dist i j >= 2 := by
    apply or_dist_iff.mpr
    left
    exact h1
  have H18 : ∀ i j, i < j → Nat.dist i j = 2 → j=i+2 := by
    intro i j lt dist_two
    rcases or_dist_iff_eq.mp dist_two with h1 | h2
    · exact h1.symm
    exfalso
    rw [← h2] at lt
    linarith [lt]
  apply induction_above i j H_absdiff three_nine
  · intro i' j' two_case k' _ h2'
    have lt_prime : i' < j' := h2'.1.trans h2'.2
    have H': k'=i'+1 := by linarith [h2', H18 i' j' lt_prime two_case]
    rw [H', H18 i' j' lt_prime two_case]
    unfold sigma_neg
    simp only [self_eq_add_right, OfNat.ofNat_ne_zero, ↓reduceIte, lt_add_iff_pos_right,
      Nat.ofNat_pos, add_tsub_cancel_left, add_tsub_cancel_right]
    apply (BraidMonoidInf.braid dist_succ).symm
  · intro i' j' ge_three ih k' _ h2'
    have hk : k'>= i'+1 := by linarith [h2'.1]
    have lt : i' < j' := h2'.1.trans h2'.2
    have lt_plus : i'+1<j' := by linarith
    have ge_three' : j' ≥ i' + 3 := by
      simp at ge_three
      have H := or_dist_iff.mp ge_three
      rcases H with h1 | h2
      · exact h1
      exfalso
      linarith [lt, h2]
    have minus_two : j'-1>=i'+2 := Nat.le_pred_of_lt ge_three'
    apply induction_in_between_with_fact k' hk h2'.2
    · have H2 : BraidMonoidInf.mk (of (i'+1) * (sigma_neg i' (j'-1))) = BraidMonoidInf.mk
          ((sigma_neg i' (j'-1)) * of i') :=
        ih (i') (j'-1) (or_dist_iff.mpr (Or.inl minus_two))
          (Nat.dist_lt_of_decrease_greater lt_plus) (i'+1) minus_two ⟨Nat.lt.base i', minus_two⟩
      have H7: (of (i'+1) * (sigma_neg i' j')) =
          of (i'+1) * ((sigma_neg i' (j'-1)))* of (j'-1) := by
        rw [mul_assoc, mul_right_inj]
        apply sigma_neg_last (h2'.1.trans h2'.2)
      have H9 : BraidMonoidInf.mk ((sigma_neg i' (j'-1)) * of i' * of (j'-1)) =
          BraidMonoidInf.mk ((sigma_neg i' (j'-1)) * of (j'-1) * of i') := by
        rw [mul_assoc, mul_assoc]
        apply BraidMonoidInf.append_left_mk <| BraidMonoidInf.comm (or_dist_iff.mpr (Or.inl minus_two))
      have H10 : ((sigma_neg i' (j'-1))* of (j'-1) * of (i')) =
          (sigma_neg (i') j') * of ((i'+1)-1) := by
        simp only [add_tsub_cancel_right, mul_left_inj]
        rw [← sigma_neg_last lt]
      rw [H7, ← H10]
      apply @BraidMonoidInf.append_right_mk _ _ (of (j'-1)) at H2
      exact H2.trans H9
    --induction case of the inductive case
    intro new_k k_bigger new_k_lt _
    have H7: (of new_k * (sigma_neg i' j')) = of new_k * of i' * (sigma_neg (i'+1) j') := by
      rw [mul_assoc, mul_right_inj]
      exact sigma_neg_first lt
    have H8 : BraidMonoidInf.mk (of new_k * of i' * (sigma_neg (i'+1) j')) = BraidMonoidInf.mk
                        (of i' * of new_k * (sigma_neg (i'+1) j')) :=
      -- from the original braid rels, because i and k are far enough apart
      BraidMonoidInf.append_right_mk (BraidMonoidInf.comm
        (or_dist_iff.mpr (Or.inl k_bigger))).symm
    have H9 : BraidMonoidInf.mk (of i' * (of new_k * (sigma_neg (i'+1) j'))) =
        BraidMonoidInf.mk (of i' * ((sigma_neg (i'+1) j') * of (new_k-1))) := by
      have H10 : BraidMonoidInf.mk ((of new_k * (sigma_neg (i'+1) j'))) =
          BraidMonoidInf.mk (((sigma_neg (i'+1) j') * of (new_k-1))) := by
        apply ih
        · exact ad_step lt_plus ge_three
        · exact Nat.dist_lt_of_increase_smaller lt_plus
        · simp only [ge_iff_le]
          apply ge_three'
        exact ⟨k_bigger, new_k_lt⟩
      apply BraidMonoidInf.append_left_mk
      rw [H10]
    rw [H7, mul_assoc, sigma_neg_first lt]
    apply H8.trans H9
  · exact h1
  exact h2

theorem append_k' (i j k : ℕ) (h1: j>=i+2) (h2 : i<k∧k<j) :
      BraidMonoidInf.mk (of (k-1) * (sigma_neg j i)) = BraidMonoidInf.mk ((sigma_neg j i) * of k) := by
  have H : 2 ≤ j-i := by exact Nat.le_sub_of_add_le' h1
  apply induction_above_diff i j H three_ten _ _ _ h1 h2
  · sorry
  sorry


theorem append_k (i j k : ℕ) (h1: j>=i+2) (h2 : i<k∧k<j) :
      BraidMonoidInf.mk (of (k-1) * (sigma_neg j i)) = BraidMonoidInf.mk ((sigma_neg j i) * of k) := by
  have i_lt_j : i<j := by linarith [h1]
  have H_absdiff : Nat.dist i j >= 2 := or_dist_iff.mpr (Or.inl h1)
  have H18 : ∀ i j, i < j → Nat.dist i j = 2 → j=i+2 := by
    intro i j lt h
    rcases or_dist_iff_eq.mp h with h1 | h2
    · exact h1.symm
    exfalso
    linarith [h1, h2]
  apply induction_above i j H_absdiff three_ten
  · intro i' j' two_case k' h1' h2'
    have H': k'=i'+1 := by linarith [h1', h2', H18 i' j' (h2'.1.trans h2'.2) two_case]
    rw [H', H18 i' j' (h2'.1.trans h2'.2) two_case]
    unfold sigma_neg
    simp only [add_tsub_cancel_right, add_right_eq_self, OfNat.ofNat_ne_zero, ↓reduceIte,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left]
    apply BraidMonoidInf.braid
    exact dist_succ
  · intro i' j' ge_three ih k' h1' h2'
    have hk : k'>= i'+1 := by linarith [h2'.1]
    have lt : i' < j' := by exact h2'.1.trans h2'.2
    have ge_three' : j' >= i'+3 := by
      rcases or_dist_iff.mp ge_three with h1 | h2
      · exact h1
      exfalso
      linarith
    apply induction_in_between_with_fact k' hk h2'.2
    · have H2 : BraidMonoidInf.mk (of i' * (sigma_neg (j'-1) i')) =
          BraidMonoidInf.mk ((sigma_neg (j'-1) i') * of (i' +1)) := by
        have ad_h : Nat.dist i' (j'-1) < Nat.dist i' j' :=
          Nat.dist_lt_of_decrease_greater h1'
        have two_helper: 2 ≤ Nat.dist i' (j' - 1) := or_dist_iff.mpr (Or.inl (Nat.le_sub_one_of_lt ge_three'))
        apply (ih (i') (j'-1) two_helper ad_h (i'+1) (Nat.le_sub_one_of_lt ge_three') _)
        constructor
        · exact lt_add_one i'
        exact Nat.lt_sub_of_add_lt ge_three'
      simp only [add_tsub_cancel_right]
      have j_minus_plus : j'-1+1 = j' := Nat.sub_add_cancel <| Nat.one_le_of_lt h1'
      have H7: (of i' * (sigma_neg j' i')) =  of i' * of (j'-1) * ((sigma_neg (j'-1) i')):= by
        rw [mul_assoc, mul_right_inj]
        conv => lhs; rw [← j_minus_plus]
        apply sigma_neg_big_first <| Nat.le_pred_of_lt lt
      have H9 : BraidMonoidInf.mk (of (j'-1) * of i' * ((sigma_neg (j'-1) i'))) =
          BraidMonoidInf.mk (of (j'-1) * (sigma_neg (j'-1) i') * of (i'+1)) := by
        rw [mul_assoc, mul_assoc]
        exact BraidMonoidInf.append_left_mk H2
      have H10 : (of (j'-1) * (sigma_neg (j'-1) i') * of (i'+1)) = (sigma_neg j' i')* of (i'+1) := by
        conv => rhs; rw [← j_minus_plus]
        rw [sigma_neg_big_first]
        exact Nat.le_pred_of_lt lt
      rw [H7, ← H10, ← H9]
      apply BraidMonoidInf.append_right_mk
      apply BraidMonoidInf.comm
      apply or_dist_iff.mpr
      left
      exact Nat.le_sub_one_of_lt ge_three'
    --induction case of the inductive case
    intro new_k k_bigger new_k_lt _ --NEED THIS for it to guess at the last step
    have lt : i'<j' := by apply h2'.1.trans h2'.2
    have H7: (of (new_k -1) * (sigma_neg j' i')) = of (new_k -1) * (sigma_neg j' (i'+1)) * of i' := by
      rw [sigma_neg_big_last lt, mul_assoc]
    have H8 : BraidMonoidInf.mk ((of (new_k -1) * (sigma_neg j' (i'+1))) * of i') =
      BraidMonoidInf.mk ((sigma_neg j' (i'+1)) * of (new_k) * of i') := by
      -- from the original braid rels, because i and k are far enough apart
      apply BraidMonoidInf.append_right_mk
      apply ih (i'+1) (j')
      · apply or_dist_iff.mpr
        left
        exact ge_three'
      · exact Nat.dist_lt_of_increase_smaller h1'
      · simp only [ge_iff_le]
        exact ge_three'
      exact ⟨k_bigger, new_k_lt⟩
    have H9 : BraidMonoidInf.mk ((sigma_neg j' (i'+1))* of new_k * of i') =
        BraidMonoidInf.mk ((sigma_neg j' (i'+1)) * of i' * of new_k) := by
      rw [mul_assoc, mul_assoc]
      apply BraidMonoidInf.append_left_mk
      symm
      apply BraidMonoidInf.comm
      apply or_dist_iff.mpr
      left
      exact k_bigger
    rw [H7, sigma_neg_big_last lt]
    exact H8.trans H9
  · exact h1
  exact h2

def delta_neg : ℕ → FreeMonoid' ℕ
  | 0 => 1
  | n+1 => (sigma_neg 0 (n+1)) * (delta_neg n)

theorem delta_neg_bounded (n : ℕ) : ∀ k ∈ delta_neg n, k<n := by
  intro k h
  induction n
  · exact (mem_one_iff.mp h).elim
  rename_i i hi
  cases' mem_mul.mp h
  · apply sigma_neg_bounded'
    next ih =>
    exact ih
  next ih =>
    exact Nat.le.step (hi ih)

theorem map_delta_neg_bounded (n k : ℕ): ∀ x, x∈ (FreeMonoid'.map (fun x => x +k)) (delta_neg n) →
    x < n + k := by
  intro x h
  induction n
  · simp [delta_neg] at h
    exfalso
    exact mem_one_iff.mp h
  rename_i n ih
  unfold delta_neg at h
  rw [map_mul, mem_mul] at h
  rcases h
  · rename_i outer
    apply map_sigma_neg_bounded n.succ k _ outer
  rename_i inner
  exact lt_add_of_lt_add_right (ih inner) (Nat.le.step Nat.le.refl)

theorem move_bigger_across (m : ℕ) (word : FreeMonoid' ℕ) : (∀ k ∈ word, k+1<m) →
    BraidMonoidInf.mk (of m * word) = BraidMonoidInf.mk (word * of m) := by
  induction word
  · exact fun _ => rfl
  · rename_i x
    intro h
    symm
    apply BraidMonoidInf.comm
    specialize h x mem_of_self
    apply or_dist_iff.mpr
    left
    exact h
  rename_i x y hx hy
  intro h_in
  have first : BraidMonoidInf.mk (of m * (x * y)) = BraidMonoidInf.mk (x * (of m * y)) := by
    rw [← mul_assoc, ← mul_assoc]
    exact BraidMonoidInf.append_right_mk (hx fun k hk =>
          h_in k (Eq.mpr (id (congrArg (fun _a => _a) (propext mem_mul))) (Or.inl hk)))
  have second : BraidMonoidInf.mk (x * (of m * y)) = BraidMonoidInf.mk (x * y * of m) := by
    rw [mul_assoc]
    exact BraidMonoidInf.append_left_mk (hy fun k hk =>
          h_in k (Eq.mpr (id (congrArg (fun _a => _a) (propext mem_mul))) (Or.inr hk)))
  exact first.trans second

-- m is the moved, n is what delta_neg is
theorem sigma_delta_swap (n m : ℕ) {h : m>n}: BraidMonoidInf.mk (of m * delta_neg (n)) =
    BraidMonoidInf.mk (delta_neg (n) * of m) := by
  induction n
  · rfl
  rename_i n _
  exact move_bigger_across m (delta_neg (Nat.succ n)) fun k h' =>
      Nat.lt_of_le_of_lt (delta_neg_bounded (Nat.succ n) k h') h

theorem factor_delta (n : ℕ) : n>=1 → BraidMonoidInf.mk (delta_neg n) =
    BraidMonoidInf.mk ((delta_neg (n-1))*(sigma_neg n 0)) := by
  cases n
  · exact fun h => (Set.right_mem_Ico.mp ⟨h, h⟩).elim
  rename_i at_least_one
  induction at_least_one
  · exact fun _ => rfl
  intro _
  rename_i n hn _
  have ih := hn (NeZero.one_le)
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
  have first : delta_neg (n+2) = (sigma_neg 0 (n+2)) * (delta_neg ((n+2)-1)) := by
    conv => lhs ; unfold delta_neg
    rfl
  have second : (sigma_neg 0 (n+2)) * (delta_neg ((n+2)-1)) =
      (sigma_neg 0 ((n+2)-1)) * of ((n+2)-1) * (delta_neg ((n+2)-1)) := by
    have LHS : sigma_neg 0 (n + 2) = sigma_neg 0 (n + 1) * of (n + 1) := by
      rename_i ha
      rw [sigma_neg_last ha]
      exact rfl
    rw [LHS]
    exact rfl
  have third : BraidMonoidInf.mk ((sigma_neg 0 ((n+2)-1)) * of ((n+2)-1) * (delta_neg ((n+2)-1))) =
      BraidMonoidInf.mk ((sigma_neg 0 ((n+2)-1)) * of ((n+2)-1) * (delta_neg ((n+2)-2)) * (sigma_neg ((n+2)-1) 0)) := by
    repeat
      rw [mul_assoc]
    exact BraidMonoidInf.append_left_mk <| BraidMonoidInf.append_left_mk ih
  have fourth : BraidMonoidInf.mk ((sigma_neg 0 ((n+2)-1)) * of ((n+2)-1) * (delta_neg ((n+2)-2)) * (sigma_neg ((n+2)-1) 0)) =
      BraidMonoidInf.mk ((sigma_neg 0 ((n+2)-1)) * (delta_neg ((n+2)-2)) * of ((n+2)-1) * (sigma_neg ((n+2)-1) 0)) := by
    apply BraidMonoidInf.append_right_mk
    rw [mul_assoc, mul_assoc]
    apply BraidMonoidInf.append_left_mk
    apply sigma_delta_swap (n) (n+1)
    exact Nat.le.refl
  have fifth : ((sigma_neg 0 ((n+2)-1)) * (delta_neg ((n+2)-2)) * of ((n+2)-1) * (sigma_neg ((n+2)-1) 0)) =
      delta_neg ((n+2)-1) * sigma_neg (n+2) 0 := by
    conv => rhs ; unfold delta_neg
    rw [mul_assoc, sigma_neg_big_first <| Nat.zero_le (n + 1)]
    rfl
  have sixth : delta_neg ((n+2)-1) * sigma_neg (n+2) 0  = delta_neg (n+1) * sigma_neg (n+2) 0 := rfl
  rw [first, second, ← sixth, ← fifth]
  apply third.trans fourth

theorem swap_sigma_delta (n : ℕ)  : ∀ i : ℕ , (i<= n-1) →
    BraidMonoidInf.mk (of i * (delta_neg n)) = BraidMonoidInf.mk (delta_neg n * of (n-1-i)) := by
    cases n
    · intro i h1
      simp only [Nat.zero_eq, ge_iff_le, zero_le, tsub_eq_zero_of_le, nonpos_iff_eq_zero] at h1
      rw [h1]
      rfl
    rename_i n
    induction n
    · simp only [Nat.zero_eq, Nat.reduceSucc, ge_iff_le, le_refl, tsub_eq_zero_of_le,
      nonpos_iff_eq_zero, zero_le, forall_eq]
      rfl
    rename_i n hn
    intro i i_between
    induction i
    · simp only [Nat.zero_eq, Nat.succ_sub_succ_eq_sub, tsub_zero]
      have step_one : BraidMonoidInf.mk (of (0) * delta_neg (Nat.succ (Nat.succ n))) =
          BraidMonoidInf.mk (of (0) * delta_neg (Nat.succ n) * (sigma_neg (n+2) 0)) := by
        apply BraidMonoidInf.append_left_mk
        apply factor_delta (n+2)
        linarith
      have step_two : BraidMonoidInf.mk ((of 0 * delta_neg (Nat.succ n))*(sigma_neg (n+2) 0)) =
          BraidMonoidInf.mk ((delta_neg (Nat.succ n))* of ((Nat.succ n)-1)*(sigma_neg (n+2) 0)) := by
        apply BraidMonoidInf.append_right_mk
        apply hn
        linarith
      have step_three :
          BraidMonoidInf.mk ((delta_neg (Nat.succ n))*of ((Nat.succ n)-1)*(sigma_neg (n+2) 0)) =
          BraidMonoidInf.mk ((delta_neg (Nat.succ n))*(sigma_neg (n+2) 0)*of (n+1)) := by
        rw [mul_assoc, mul_assoc]
        apply BraidMonoidInf.append_left_mk
        apply append_k
        · linarith
        constructor
        · linarith
        exact Nat.le.refl
      have step_four: BraidMonoidInf.mk ((delta_neg (Nat.succ n))*(sigma_neg (n+2) 0)*of (n+1)) =
          BraidMonoidInf.mk ((delta_neg (Nat.succ (Nat.succ n)))*of (n+1)) := by
        apply BraidMonoidInf.append_right_mk
        symm
        apply factor_delta
        linarith
      exact ((step_one.trans step_two).trans step_three).trans step_four
    rename_i k _
    have step_one : (of (Nat.succ k) * delta_neg (Nat.succ (Nat.succ n))) =
        (of (Nat.succ k) * sigma_neg 0 (Nat.succ (Nat.succ n)) *
        delta_neg (Nat.succ (Nat.succ n) -1)) := by
      rw [mul_assoc]
      conv => lhs; unfold delta_neg
      rfl
    have step_two : BraidMonoidInf.mk (of (Nat.succ k) * sigma_neg 0 (Nat.succ (Nat.succ n))
        * delta_neg (Nat.succ (Nat.succ n) -1)) = BraidMonoidInf.mk
        (sigma_neg 0 (Nat.succ (Nat.succ n)) * of (Nat.succ k -1) *
        delta_neg (Nat.succ (Nat.succ n) -1)) := by
      apply BraidMonoidInf.append_right_mk
      apply prepend_k
      · linarith
      exact ⟨Fin.pos ⟨k, Nat.le.refl⟩, Nat.lt_succ.mpr i_between⟩
    have step_three : BraidMonoidInf.mk (sigma_neg 0 (Nat.succ (Nat.succ n))
        * of (Nat.succ k -1) * delta_neg (Nat.succ (Nat.succ n) -1)) = BraidMonoidInf.mk
        (sigma_neg 0 (Nat.succ (Nat.succ n)) * delta_neg (Nat.succ (Nat.succ n) -1)
        * of ((Nat.succ (Nat.succ n) -1 -1) - (Nat.succ k -1))) := by
      rw [mul_assoc, mul_assoc]
      exact BraidMonoidInf.append_left_mk (hn k (Nat.lt_succ.mp i_between))
    have step_four : (sigma_neg 0 (Nat.succ (Nat.succ n)) * delta_neg (Nat.succ (Nat.succ n) -1)
        * of ((Nat.succ (Nat.succ n) -1 -1) - (Nat.succ k -1))) =
        (delta_neg (Nat.succ (Nat.succ n)) * of ((Nat.succ (Nat.succ n) -1)-Nat.succ k)) := by
      have last_part : (Nat.succ (Nat.succ n) -1 - 1) - (Nat.succ k -1)
          = (Nat.succ (Nat.succ n) -1)-Nat.succ k := by simp
      have first_part : sigma_neg 0 (Nat.succ (Nat.succ n)) *
          delta_neg (Nat.succ (Nat.succ n) -1) = delta_neg (Nat.succ (Nat.succ n)) := by
        conv => rhs; unfold sigma_neg
        rfl
      rw [last_part, first_part]
    rw [step_one, ← step_four]
    exact step_two.trans step_three

theorem swap_sigma_delta_souped {n : ℕ} {w : FreeMonoid' ℕ} : (∀x, x∈w → x<n) →
    BraidMonoidInf.mk (w * delta_neg n) = BraidMonoidInf.mk  (delta_neg n * FreeMonoid'.map (λ i => (n-1)-i) w) := by
  induction w using FreeMonoid'.inductionOn
  · intro _
    simp only [one_mul, map_one, mul_one]
  · rename_i y
    intro y_in
    apply swap_sigma_delta
    specialize y_in y mem_of_self
    exact Nat.le_sub_one_of_lt y_in
  rename_i z w hx hy
  intro hxy
  rw [map_mul]
  have step_one : BraidMonoidInf.mk (delta_neg n * ((map fun i => n - 1 - i) z * (map fun i => n - 1 - i) w)) =
      BraidMonoidInf.mk (z * ((delta_neg n) * (map fun i => n - 1 - i) w)) := by
    rw [← mul_assoc, ← mul_assoc]
    apply BraidMonoidInf.append_right_mk
    symm
    apply hx
    intro a ha
    apply hxy
    rw [mem_mul]
    exact Or.inl ha
  have step_two : BraidMonoidInf.mk (z * ((delta_neg n) * (map fun i => n - 1 - i) w)) =
      BraidMonoidInf.mk (z * w * (delta_neg n)) := by
    rw [mul_assoc]
    apply BraidMonoidInf.append_left_mk
    symm
    apply hy
    intro a ha
    apply hxy
    rw [mem_mul]
    exact Or.inr ha
  exact (step_one.trans step_two).symm

theorem rw_pow : delta_neg n ^ (Nat.succ j) = (delta_neg n ^ j) * delta_neg n := by
  induction j with
  | zero =>
    simp only [Nat.zero_eq, Nat.reduceSucc, pow_one, pow_zero]
    rfl
  | succ k hk =>
    rw [pow_succ' (delta_neg n) (k + 1)]
    conv => lhs; rw [hk]
    rw [← mul_assoc]
    exact mul_right_cancel_iff.mpr (pow_succ' (delta_neg n) k).symm

def boundary (n i: ℕ) : FreeMonoid' ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | k+2 => if i = n-1 then
            (sigma_neg (n-1) 0)*(FreeMonoid'.map (λ i => i+1) (delta_neg (n-1)))
          else (boundary (k+1) i) * (sigma_neg n 0)

theorem boundary_spec (i n : ℕ) (h_n : n>0) (h : i<=n-1) : BraidMonoidInf.mk
  (delta_neg n) = BraidMonoidInf.mk (of (i)*(boundary n i)) := by
    cases n with
    | zero => exfalso; linarith [h_n]
    | succ n =>
    induction n with
    | zero =>
      simp at h -- n=1
      rw [h]
      rfl
    | succ n ih =>
    cases Nat.lt_trichotomy i (n + 1) with
    | inl lt =>
      have boundary_is : boundary (Nat.succ (Nat.succ n)) i =
              (boundary (Nat.succ n) i) * (sigma_neg (n+2) 0) := by
        conv => lhs; unfold boundary
        have H : ¬ i=n+1 := by linarith [ih]
        simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, H, ↓reduceIte]
      rw [boundary_is]
      apply (factor_delta _ h_n).trans
      rw [← mul_assoc]
      apply BraidMonoidInf.append_right_mk
      apply ih
      · exact Fin.pos ⟨i, lt⟩
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      exact Nat.lt_succ.mp lt
    | inr last_two =>
        cases last_two with
        | inl eq =>
            have boundary_is : boundary (Nat.succ (Nat.succ n)) i =
                (sigma_neg (n+2-1) 0)*(FreeMonoid'.map (λ i => i+1) (delta_neg (n+2-1))) := by
              conv => lhs; unfold boundary
              simp [eq]
            rw [boundary_is]
            simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
            rw [eq]
            have step_one : BraidMonoidInf.mk (delta_neg (Nat.succ (Nat.succ n))) =
                BraidMonoidInf.mk (delta_neg (Nat.succ n) * sigma_neg (n+2) 0) := by
              apply factor_delta
              linarith
            have step_two' : ∀ L, (∀ x, x∈L → x <n+1) → BraidMonoidInf.mk (L * sigma_neg (n+2) 0) =
                BraidMonoidInf.mk ((sigma_neg (n+2) 0) * (FreeMonoid'.map (λ i => i+1) (L))) := by
              intro L
              induction L
              · intro _
                simp only [one_mul, map_one, mul_one]
              · rename_i y
                intro h
                simp only [map_of]
                apply append_k _ _ (y+1)
                · exact Nat.le_add_left (0 + 2) n
                exact ⟨Nat.add_pos_right y Nat.le.refl, Nat.add_lt_add_right (h y mem_of_self) 1⟩
              rename_i x y hx hy
              intro hxy
              simp only [_root_.map_mul]
              have first_step : BraidMonoidInf.mk (x * y * sigma_neg (n + 2) 0) =
                  BraidMonoidInf.mk (x * sigma_neg (n + 2) 0 * ((map fun i => i + 1) y)) := by
                rw [mul_assoc, mul_assoc]
                apply BraidMonoidInf.append_left_mk
                apply hy
                intro x in_y
                apply hxy
                rw [mem_mul]
                right
                exact in_y
              apply first_step.trans
              rw [← mul_assoc]
              apply BraidMonoidInf.append_right_mk
              apply hx
              intro x in_x
              apply hxy
              rw [mem_mul]
              exact Or.inl in_x
            apply step_one.trans
            apply (step_two' (delta_neg n.succ) (delta_neg_bounded n.succ)).trans
            conv => rhs; rw [← mul_assoc]
            apply BraidMonoidInf.append_right_mk
            have H : (sigma_neg (n + 2) 0) = ((n + 1) :: sigma_neg (n + 1) 0) := by
              have helper : 0 <= n+1 := by linarith
              rw [sigma_neg_big_first helper]
              exact rfl
            rw [H]
            rfl
        | inr bigger =>
        exfalso
        simp at h
        linarith [bigger, h]

theorem boundary_bounded (i n : ℕ) (h_n : n>0) (h : i<=n-1) : ∀ x, x ∈ boundary n i → x < n := by
  cases n
  · exfalso
    exact LT.lt.false h_n
  rename_i k
  induction k
  · exact fun x h_empty => (mem_one_iff.mp h_empty).elim
  rename_i j hj
  intro x h_boundary
  unfold boundary at h_boundary
  simp at h_boundary
  have three_cases : i < j+1 ∨ i = j+1 ∨ i > j+1 := by exact Nat.lt_trichotomy i (j + 1)
  rcases three_cases
  · next lt =>
    have not_eq : ¬ i = j+1 := by linarith [lt]
    rw [if_neg not_eq, mem_mul] at h_boundary
    rcases h_boundary
    · next in_bound =>
      have H : x < Nat.succ j := by
        apply hj
        · exact Fin.pos { val := i, isLt := lt }
        · simp
          exact Nat.lt_succ.mp lt
        exact in_bound
      exact Nat.lt.step H
    next in_sigma =>
    exact sigma_neg_bounded _ in_sigma
  next eq_or_bigger =>
  rcases eq_or_bigger
  · next eq =>
    simp only [eq] at h_boundary
    rw [ite_true] at h_boundary
    rw [mem_mul] at h_boundary
    rcases h_boundary
    · next in_sigma =>
      apply sigma_neg_bounded
      unfold sigma_neg
      have H : ¬ Nat.succ (Nat.succ j) = 0 := by exact Nat.succ_ne_zero (j + 1)
      simp [H]
      unfold sigma_neg at in_sigma
      have : ¬ j+1=0 := by exact Nat.succ_ne_zero j
      simp [this] at in_sigma
      have H : (j + 1) + 1 = (Nat.succ j) + 1 - 0 := by
        simp
      conv =>
      {
        enter [2]
        enter [1]
        rw [H]
      }
      rw [@count_down_pop 0 (Nat.succ j)]
      · rw [mem_mul]
        right
        exact in_sigma
      exact Nat.zero_le (Nat.succ j)
    next in_delta =>
    induction j
    · simp only [Nat.zero_eq, zero_add, mem_map] at in_delta
      unfold delta_neg at in_delta
      unfold delta_neg at in_delta
      unfold sigma_neg at in_delta
      unfold count_up at in_delta
      unfold count_up at in_delta
      simp only [zero_add, zero_ne_one, ↓reduceIte, zero_lt_one, mul_one, mem_of,
        exists_eq_left] at in_delta
      rw [← in_delta]
      exact Nat.le.refl
    rename_i n _
    exact map_delta_neg_bounded n.succ.succ 1 _ in_delta
  next bigger =>
  exfalso
  rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h
  linarith [bigger, h]

theorem multiple_delta_neg_bounded {n k : ℕ} : ∀ x ∈ delta_neg n ^ k, x < n := by
  induction k
  · intro x h
    exfalso
    exact mem_one_iff.mp h
  rename_i k hk
  intro x h
  have H : delta_neg n ^ Nat.succ k = delta_neg n * delta_neg n ^ k := pow_succ' (delta_neg n) k
  rw [H] at h
  rcases (FreeMonoid'.mem_mul.mp h)
  · next in_delta => exact delta_neg_bounded _ _ in_delta
  next ic => exact hk _ ic

theorem multiple_delta_neg (u : FreeMonoid' ℕ) (l n : ℕ) (h : FreeMonoid'.length u <= l)
  (bounded : ∀ x, x ∈ u → x < n)
  : ∃ w, BraidMonoidInf.mk (u * w) = BraidMonoidInf.mk ((delta_neg n)^l) ∧
    (∀ x, x ∈ w → x < n)  := by
  have helper : ∀ l, ∀ n, ∀ u, (u.length <= l) → (∀ x, x ∈ u → x < n) →
      ∃ w, BraidMonoidInf.mk (u * w) = BraidMonoidInf.mk ((delta_neg n)^l) ∧ (∀ x, x ∈ w → x < n) := by
    intro l
    induction l
    · intro n u u_length _
      rw [pow_zero]
      rw [FreeMonoid'.eq_one_of_length_eq_zero (Nat.eq_zero_of_le_zero u_length)]
      use 1
      constructor
      · rfl
      intro x h
      exfalso
      exact mem_one_iff.mp h
    rename_i j hj
    intro n u u_length bounded_u
    rcases FreeMonoid'.eq_one_or_has_last_elem u with ⟨thing, prf⟩
    · use delta_neg n ^ Nat.succ j
      constructor
      · rfl
      exact fun x a => multiple_delta_neg_bounded x a
    rename_i u_is
    rcases u_is with ⟨front, caboose, h⟩
    rw [h]
    have front_length : FreeMonoid'.length front <= j := by
      have helper : FreeMonoid'.length u = FreeMonoid'.length front + FreeMonoid'.length (of caboose) := by
        rw [h, FreeMonoid'.length_mul]
      rw [helper] at u_length
      rw [FreeMonoid'.length_of] at u_length
      exact Nat.lt_succ.mp u_length
    have front_bounded : ∀ x, x ∈ front → x < n := by
      rw [h] at bounded_u
      intro x x_in
      apply bounded_u
      apply FreeMonoid'.mem_mul.mpr
      left
      exact x_in
    rcases hj n front front_length front_bounded with ⟨w', hw⟩
    let phi_w' := FreeMonoid'.map (λ i => n-1-i) w'
    use boundary n caboose * phi_w'
    have H : ∀ a b, BraidMonoidInf.mk (a * b) = BraidMonoidInf.mk a * BraidMonoidInf.mk b := by
      unfold BraidMonoidInf.mk
      intro a b
      rfl
    have caboose_bounded : caboose < n := by
      apply bounded_u
      rw [h, FreeMonoid'.mem_mul]
      right
      apply FreeMonoid'.mem_of.mpr
      rfl
    have step_one : BraidMonoidInf.mk (front * (of caboose) * (boundary n caboose * phi_w')) =
      BraidMonoidInf.mk (front * delta_neg n * phi_w') := by
      repeat rw [H]
      have H2 : BraidMonoidInf.mk (of caboose) * BraidMonoidInf.mk (boundary n caboose) =
        BraidMonoidInf.mk (delta_neg n) := by
        rw [← H, boundary_spec caboose]
        · exact Fin.pos (Fin.mk caboose caboose_bounded)
        exact Nat.le_sub_one_of_lt caboose_bounded
      rw [← H2]
      repeat rw [mul_assoc]
    have step_two : BraidMonoidInf.mk (front * (delta_neg n) * phi_w') =
        BraidMonoidInf.mk (front * w' * (delta_neg n)) := by
      rw [mul_assoc, H]; conv => rhs; rw [mul_assoc, H]
      rw [(swap_sigma_delta_souped hw.right).symm]
    constructor
    · apply step_one.trans
      apply step_two.trans
      rw [rw_pow, H]
      conv => rhs; rw [H]
      rw [hw.1]
    intro x x_in
    cases FreeMonoid'.mem_mul.mp x_in
    · rename_i in_boundary
      apply boundary_bounded caboose n
      rcases n
      · exfalso
        have H : caboose < 0 := by
          apply bounded_u
          rw [h, FreeMonoid'.mem_mul]
          exact Or.inr (mem_of.mpr (Eq.refl caboose))
        exact Nat.not_lt_zero caboose H
      rename_i n
      · exact Fin.pos { val := n, isLt := Nat.le.refl }
      · exact Nat.le_sub_one_of_lt caboose_bounded
      exact in_boundary
    rename_i in_phi
    simp only at in_phi
    rcases FreeMonoid'.mem_map.mp in_phi with ⟨w, hw⟩
    rw [← hw.2]
    have H :=
      fun n x n_big => Nat.lt_of_le_of_lt (Nat.sub_le (n - 1) x)
        (Nat.sub_one_lt_of_le n_big Nat.le.refl)
    exact H _ _ (Fin.pos (Fin.mk caboose caboose_bounded))
  exact helper _ _ _ h bounded

-- though this one is quickly done!
theorem is_bounded (u : FreeMonoid' ℕ) : ∃ k, ∀ x∈ u, x<k := by
  induction u using FreeMonoid'.inductionOn'
  · use 1
    exact fun _ h => (mem_one_iff.mp h).elim
  rename_i head tail tail_ih
  rcases tail_ih with ⟨old_k, kh⟩
  use Nat.max old_k (head+1)
  intro x x_in
  cases x_in
  · exact lt_max_of_lt_right Nat.le.refl
  next x_in_tail =>
  specialize kh x x_in_tail
  exact lt_max_iff.mpr (Or.inl kh)

theorem common_right_mul_inf_mk (u v : FreeMonoid' ℕ) : ∃ (u' v' : FreeMonoid' ℕ), BraidMonoidInf.mk (u*v') = BraidMonoidInf.mk (v*u') := by
  rcases (is_bounded u) with ⟨k1, hk1⟩
  rcases (is_bounded v) with ⟨k2, hk2⟩
  have u_under : ∀ x ∈u, x < Nat.max k1 k2 :=
    fun x h => Nat.lt_of_lt_of_le (hk1 x h) (Nat.le_max_left k1 k2)
  have v_under : ∀ x ∈v, x < Nat.max k1 k2 :=
    fun x h => Nat.lt_of_lt_of_le (hk2 x h) (Nat.le_max_right k1 k2)
  have u_length := Nat.le_max_left u.length v.length
  have v_length := Nat.le_max_right u.length v.length
  rcases (multiple_delta_neg u (Nat.max u.length v.length) (Nat.max k1 k2)
    u_length u_under) with ⟨v', hv', _⟩
  rcases (multiple_delta_neg v (Nat.max u.length v.length) (Nat.max k1 k2)
    v_length v_under) with ⟨u', hu', _⟩
  exact Exists.intro u' (Exists.intro v' (hv'.trans hu'.symm))

theorem common_right_mul_inf (u v : PresentedMonoid (@braid_rels_m_inf)) :
    ∃ (u' v' : FreeMonoid' ℕ ), ((u * (PresentedMonoid.mk (braid_rels_m_inf) v'))) =
    v * PresentedMonoid.mk (braid_rels_m_inf) u' := by
  induction u
  induction v
  exact common_right_mul_inf_mk _ _