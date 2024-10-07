import BraidProject.BraidMonoid
import BraidProject.AcrossStrands
import BraidProject.InductionWithBounds
--import KnotProject.Induction_Principles
import BraidProject.FreeMonoid_mine
--part two : common right multiples


open FreeMonoid'
-- --lemma 3.9 property
def three_nine (i j : ℕ) := ∀ k,  j>=i+2 → i<k∧k<j → BraidMonoidInf.mk (of k * sigma_neg i j) =
    BraidMonoidInf.mk (sigma_neg i j * of (k-1))

-- --lemma 3.10 property
def three_ten (i j : ℕ) := ∀ k,  j>=i+2 → i<k∧k<j → (BraidMonoidInf.mk (of (k-1) * sigma_neg j i) =
  BraidMonoidInf.mk (sigma_neg j i * of k))

theorem Nat.dist_step {k : ℕ} (h : i<j) : k + 1 <= Nat.dist i j → k ≤ Nat.dist (i + 1) j := by
  intro three
  rw [Nat.dist_eq_sub_of_le h]
  rw [Nat.dist_eq_sub_of_le (Nat.succ_le_succ_iff.mp (by linarith [h]))] at three
  exact Nat.sub_le_sub_right three 1

--these should all go in the braid monoid file. or rather, they should go in the presentedmonoid file
-- theorem left_side {a b c : FreeMonoid' ℕ} (h : BraidMonoidInf.mk b = BraidMonoidInf.mk c) :
--   BraidMonoidInf.mk (a * b) = BraidMonoidInf.mk (a * c) := by
--   show BraidMonoidInf.mk a * BraidMonoidInf.mk b = BraidMonoidInf.mk a * BraidMonoidInf.mk c
--   rw [h]

-- theorem right_side {a b c : FreeMonoid' ℕ} (h : BraidMonoidInf.mk b = BraidMonoidInf.mk c) :
--   BraidMonoidInf.mk (b * a) = BraidMonoidInf.mk (c * a) := by
--   show BraidMonoidInf.mk b * BraidMonoidInf.mk a = BraidMonoidInf.mk c * BraidMonoidInf.mk a
--   rw [h]

-- namespace PresentedMonoid
-- theorem sound {α : Type} {rel : (FreeMonoid' α) → (FreeMonoid' α) → Prop} {a b : FreeMonoid' α}
--     (h : (StepsTo rel) a b) : PresentedMonoid.mk rel a = PresentedMonoid.mk rel b := Quot.sound h

-- end PresentedMonoid
-- theorem comm_rel {a b : ℕ} (h : a +2 <= b) : BraidMonoidInf.mk (of a * of b) = BraidMonoidInf.mk (of b * of a) := by
--   apply PresentedMonoid.sound
--   apply StepsTo.basic
--   exact braid_rels_m_inf.separated _ _ h

-- theorem braid_rel {a : ℕ} : BraidMonoidInf.mk (of a * of (a+1) * of a) = BraidMonoidInf.mk (of (a+1) * of a * of (a+1)) := by
--   apply PresentedMonoid.sound
--   apply StepsTo.basic
--   exact braid_rels_m_inf.adjacent _

theorem prepend_k (i j k : ℕ) (h1: j>=i+2) (h2 : i<k∧k<j) :
    BraidMonoidInf.mk (of k * (sigma_neg i j)) = BraidMonoidInf.mk ((sigma_neg i j) *
    (of (k-1))) := by
  have i_lt_j : i<j := by linarith [h1]
  have H_absdiff : Nat.dist i j >= 2 := or_dist_iff.mpr (Or.inl h1)
  have H18 : ∀ i j, i < j → Nat.dist i j = 2 → j=i+2 := by
    intro i j lt dist
    have H := or_dist_iff_eq.mp dist
    rcases H with h1 | h2
    · exact h1.symm
    linarith [i_lt_j, h2]
  apply induction_above i j H_absdiff three_nine
  · intro i' j' two_case k' _ h2'
    have H': k'=i'+1 := by linarith [h2', H18 i' j' (h2'.1.trans h2'.2) two_case]
    rw [H', H18 i' j' (h2'.1.trans h2'.2) two_case]
    simp only [sigma_neg, self_eq_add_right, OfNat.ofNat_ne_zero, ↓reduceIte, lt_add_iff_pos_right,
      Nat.ofNat_pos, add_tsub_cancel_left, add_tsub_cancel_right]
    exact (BraidMonoidInf.braid dist_succ).symm
  · intro i' j' ge_three ih k' _ h2'
    have hk : k'>= i'+1 := by linarith [h2'.1]
    have lt : i' < j' := h2'.1.trans h2'.2
    have lt_plus : i'+1<j' := by linarith
    have ge_three' : j' ≥ i' + 3 := by
      have helper : 3 <= j'-i' := by
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_succ_le lt)] at ge_three
        exact ge_three
      apply (le_tsub_iff_left _).mp helper
      exact Nat.le_of_lt lt
    have minus_two : j'-1>=i'+2 := Nat.le_pred_of_lt ge_three'
    apply induction_in_between_with_fact k' hk h2'.2
    · have H2 : BraidMonoidInf.mk (of (i'+1) * (sigma_neg i' (j'-1))) = BraidMonoidInf.mk
          ((sigma_neg i' (j'-1)) * of i') := by
        apply ih (i') (j'-1) _ (Nat.dist_lt_of_decrease_greater lt_plus) (i'+1) minus_two ⟨Nat.lt.base i', minus_two⟩
        rw [Nat.dist_eq_sub_of_le (Nat.le_sub_one_of_lt lt)]
        exact le_tsub_of_add_le_left minus_two
      have H7: (of (i'+1) * (sigma_neg i' j')) =
          of (i'+1) * ((sigma_neg i' (j'-1)))* of (j'-1) := by
        rw [mul_assoc, mul_right_inj]
        apply sigma_neg_last (h2'.1.trans h2'.2)
      have H9 : BraidMonoidInf.mk ((sigma_neg i' (j'-1)) * of i' * of (j'-1)) =
          BraidMonoidInf.mk ((sigma_neg i' (j'-1)) * of (j'-1) * of i') := by
        rw [mul_assoc, mul_assoc]
        apply BraidMonoidInf.append_left_mk
        apply BraidMonoidInf.comm
        rw [Nat.dist_eq_sub_of_le (Nat.le_sub_one_of_lt lt)]
        exact Nat.le_sub_of_add_le' minus_two
      have H10 : ((sigma_neg i' (j'-1))* of (j'-1) * of (i')) =
          (sigma_neg (i') j') * of ((i'+1)-1) := by
        simp only [add_tsub_cancel_right, mul_left_inj]
        rw [← sigma_neg_last lt]
      rw [H7, ← H10]
      have H := @PresentedMonoid.append_right _ _ _ _ (of (j'-1)) (PresentedMonoid.exact H2)
      exact (PresentedMonoid.sound H).trans H9
    --induction case of the inductive case
    intro new_k k_bigger new_k_lt _
    have H7: (of new_k * (sigma_neg i' j')) = of new_k * of i' * (sigma_neg (i'+1) j') := by
      rw [mul_assoc, mul_right_inj]
      exact sigma_neg_first lt
    have H8 : BraidMonoidInf.mk (of new_k * of i' * (sigma_neg (i'+1) j')) = BraidMonoidInf.mk
                        (of i' * of new_k * (sigma_neg (i'+1) j')) := by
      -- from the original braid rels, because i and k are far enough apart
      apply BraidMonoidInf.append_right_mk
      apply BraidMonoidInf.comm
      have H : new_k >= i' := by linarith [k_bigger]
      rw [Nat.dist_eq_sub_of_le_right H]
      exact (Nat.le_sub_iff_add_le' H).mpr k_bigger
    have H9 : BraidMonoidInf.mk (of i' * (of new_k * (sigma_neg (i'+1) j'))) =
        BraidMonoidInf.mk (of i' * ((sigma_neg (i'+1) j') * of (new_k-1))) := by
      have H10 : BraidMonoidInf.mk ((of new_k * (sigma_neg (i'+1) j'))) =
          BraidMonoidInf.mk (((sigma_neg (i'+1) j') * of (new_k-1))) := by
        apply ih _ _ (Nat.dist_step lt ge_three)
        · apply Nat.dist_lt_of_increase_smaller
          assumption
        · simp only [ge_iff_le]
          exact ge_three'
        exact ⟨k_bigger, new_k_lt⟩
      apply BraidMonoidInf.append_left_mk
      rw [H10]
    rw [H7, mul_assoc, sigma_neg_first lt]
    apply H8.trans H9
  · exact h1
  exact h2

theorem append_k (i j k : ℕ) (h1: j>=i+2) (h2 : i<k∧k<j) :
      BraidMonoidInf.mk (of (k-1) * (sigma_neg j i)) = BraidMonoidInf.mk ((sigma_neg j i) * of k) := by
  have i_lt_j : i<j := by linarith [h1]
  have H_absdiff : Nat.dist i j >= 2 := or_dist_iff.mpr (Or.inl h1)
  have H18 : ∀ i j, i < j → Nat.dist i j = 2 → j=i+2 := by
    intro i j lt dist
    have H := or_dist_iff_eq.mp dist
    rcases H with h1 | h2
    · exact h1.symm
    linarith [i_lt_j, h2]
  apply induction_above i j H_absdiff three_ten
  · intro i' j' two_case k' h1' h2'
    have H': k'=i'+1 := by linarith [h1', h2', H18 i' j' (h2'.1.trans h2'.2) two_case]
    rw [H', H18 i' j' (h2'.1.trans h2'.2) two_case]
    simp only [sigma_neg, add_tsub_cancel_right, add_right_eq_self, OfNat.ofNat_ne_zero, ↓reduceIte,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left]
    apply BraidMonoidInf.braid
    exact dist_succ
  · intro i' j' ge_three ih k' h1' h2'
    have hk : k'>= i'+1 := by linarith [h2'.1]
    have lt : i' < j' := by exact h2'.1.trans h2'.2
    have lt_plus : i'+1<j' := by linarith [h1']
    have ge_three' : j' >= i'+3 := by
      have helper : 3 <= j'-i' := by
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_succ_le lt)] at ge_three
        exact ge_three
      apply (le_tsub_iff_left _).mp helper
      exact Nat.le_of_lt lt
    apply induction_in_between_with_fact k' hk h2'.2
    · have H2 : BraidMonoidInf.mk (of i' * (sigma_neg (j'-1) i')) =
          BraidMonoidInf.mk ((sigma_neg (j'-1) i') * of (i' +1)) := by
        have ad_h : Nat.dist i' (j'-1) < Nat.dist i' j' := Nat.dist_lt_of_decrease_greater lt_plus
        -- have two_helper: 2 ≤ Nat.dist i' (j' - 1) := by
        --   have sub_1 : j'-1>= i' + 2 := Nat.le_pred_of_lt ge_three'
        --   unfold Nat.dist
        --   have helper : ¬ i'>j'-1 := by
        --     intro h_exf
        --     have last_one : i' > i' +2 := by exact Nat.lt_of_le_of_lt sub_1 h_exf
        --     linarith [last_one]
        --   simp
        apply (ih (i') (j'-1) _ ad_h (i'+1) _ _)
        · sorry
        · exact Nat.le_sub_one_of_lt ge_three'
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
      rw [H7, ← H10]
      apply (BraidMonoidInf.append_right_mk (BraidMonoidInf.comm _)).trans H9
      sorry
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
      · have H2 : j'-(i'+1)=j'-i'-1 := by exact rfl
        exact Nat.dist_step lt ge_three
      · exact Nat.dist_lt_of_increase_smaller lt_plus
      · simp only [ge_iff_le]
        exact ge_three'
      exact ⟨k_bigger, new_k_lt⟩
    have H9 : BraidMonoidInf.mk ((sigma_neg j' (i'+1))* of new_k * of i') =
        BraidMonoidInf.mk ((sigma_neg j' (i'+1)) * of i' * of new_k) := by
      rw [mul_assoc, mul_assoc]
      apply BraidMonoidInf.append_left_mk
      apply BraidMonoidInf.comm
      sorry
    rw [H7, sigma_neg_big_last lt]
    exact H8.trans H9
  · exact h1
  exact h2
#exit
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
  · intro h
    rename_i y
    apply BraidMonoidInf.comm
    specialize h y FreeMonoid'.mem_of_self
    rw [Nat.dist_eq_sub_of_le_right]
    · linarith [h]
    linarith [h]
    --(Nat.succ_le.mpr (h x mem_singleton_self))).symm
  rename_i x y hx hy
  intro h_in
  have first : BraidMonoidInf.mk (of m * (x * y)) = BraidMonoidInf.mk (x * (of m * y)) := by
    rw [← mul_assoc, ← mul_assoc]
    apply BraidMonoidInf.append_right_mk
    apply hx
    intro k k_in
    have k_in_mul : k∈ x * y := by
      apply mem_mul.mpr
      left
      exact k_in
    exact h_in k k_in_mul
  have second : BraidMonoidInf.mk (x * (of m * y)) = BraidMonoidInf.mk (x * y * of m) := by
    rw [mul_assoc]
    apply BraidMonoidInf.append_left_mk
    apply hy
    intro k k_in
    have k_in_mul : k ∈ x * y := by
      apply mem_mul.mpr
      right
      exact k_in
    exact h_in k k_in_mul
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
  have first : delta_neg (n+2) = (sigma_neg 0 (n+2)) * (delta_neg ((n+2)-1)) := rfl
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
    apply BraidMonoidInf.append_left_mk
    apply BraidMonoidInf.append_left_mk
    exact ih
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
          = (Nat.succ (Nat.succ n) -1)-Nat.succ k := by
        simp only [Nat.succ_eq_add_one, add_tsub_cancel_right, Nat.reduceSubDiff]
      have first_part : sigma_neg 0 (Nat.succ (Nat.succ n)) *
          delta_neg (Nat.succ (Nat.succ n) -1) = delta_neg (Nat.succ (Nat.succ n)) := rfl
      rw [last_part, first_part]
    rw [step_one, ← step_four]
    exact step_two.trans step_three

theorem swap_sigma_delta_souped {n : ℕ} {w : FreeMonoid' ℕ} : (∀x, x∈w → x<n) →
    BraidMonoidInf.mk (w * delta_neg n) = BraidMonoidInf.mk  (delta_neg n * FreeMonoid'.map (λ i => (n-1)-i) w) := by
  induction w
  · intro _
    simp only [one_mul, map_one, mul_one]
  · intro y_in
    rename_i y
    exact swap_sigma_delta n y (Nat.le_sub_one_of_lt (y_in y mem_of_self))
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

theorem rw_pow : delta_neg n ^ (Nat.succ j) = (delta_neg n ^ j) * delta_neg n := rfl

def boundary (n i: ℕ) : FreeMonoid' ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | k+2 => if i = n-1 then
            (sigma_neg (n-1) 0)*(FreeMonoid'.map (λ i => i+1) (delta_neg (n-1)))
          else (boundary (k+1) i) * (sigma_neg n 0)

theorem boundary_spec (i n : ℕ) (h_n : n>0) (h : i<=n-1) : BraidMonoidInf.mk
  (delta_neg n) = BraidMonoidInf.mk (of (i)*(boundary n i)) := by
    cases n
    · exfalso -- n=0
      linarith [h_n]
    next n =>
    induction n
    · simp at h -- n=1
      rw [h]
      rfl
    rename_i n ih
    have H : i<n+1 ∨ i=n+1 ∨ i>n+1 := by exact Nat.lt_trichotomy i (n + 1)
    cases' H
    · next lt =>
      have boundary_is : boundary (Nat.succ (Nat.succ n)) i =
              (boundary (Nat.succ n) i) * (sigma_neg (n+2) 0) := by
        conv => lhs; unfold boundary
        have H : ¬ i=n+1 := by linarith [ih]
        simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, H, ↓reduceIte]
      rw [boundary_is]
      have old_lemma : BraidMonoidInf.mk (delta_neg (Nat.succ (Nat.succ n))) =
          BraidMonoidInf.mk ((delta_neg (Nat.succ n))*(sigma_neg (n+2) 0)) := by
            apply factor_delta
            exact h_n
      apply old_lemma.trans
      rw [← mul_assoc]
      apply BraidMonoidInf.append_right_mk
      apply ih
      · exact Fin.pos { val := i, isLt := lt }
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      exact Nat.lt_succ.mp lt
    · next last_two =>
        cases' last_two
        · next eq =>
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
              · intro h
                rename_i y
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
            have step_two : BraidMonoidInf.mk (delta_neg (Nat.succ n) * sigma_neg (n+2) 0) =
                BraidMonoidInf.mk ((sigma_neg (n+2) 0) * (FreeMonoid'.map (λ i => i+1) (delta_neg (n+1)))) := by
              apply step_two'
              apply delta_neg_bounded
            apply step_one.trans
            apply step_two.trans
            conv => rhs; rw [← mul_assoc]
            apply BraidMonoidInf.append_right_mk
            have H : (sigma_neg (n + 2) 0) = ((n + 1) :: sigma_neg (n + 1) 0) := by
              have helper : 0 <= n+1 := by linarith
              rw [sigma_neg_big_first helper]
              exact rfl
            rw [H]
            rfl
        next bigger =>
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
      change x ∈ count_down ((Nat.succ j) + 1 - 0) _ 0
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
  rw [pow_succ' (delta_neg n) k] at h
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
      rw [nonpos_iff_eq_zero] at u_length
      have : u = 1 := by
        exact FreeMonoid'.eq_one_of_length_eq_zero u_length
      rw [this]
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
      rw [h, FreeMonoid'.length_mul, FreeMonoid'.length_of] at u_length
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

theorem common_right_mul_inf_mk (u v : FreeMonoid' ℕ) : ∃ (u' v' : FreeMonoid' ℕ ), BraidMonoidInf.mk (u*v') = BraidMonoidInf.mk (v*u') := by
  rcases (is_bounded u) with ⟨k1, hk1⟩
  rcases (is_bounded v) with ⟨k2, hk2⟩
  have u_under : ∀ x ∈u, x < Nat.max k1 k2 :=
    fun x h => Nat.lt_of_lt_of_le (hk1 x h) (Nat.le_max_left k1 k2)
  have v_under : ∀ x ∈v, x < Nat.max k1 k2 :=
    fun x h => Nat.lt_of_lt_of_le (hk2 x h) (Nat.le_max_right k1 k2)
  have u_length := Nat.le_max_left (FreeMonoid'.length u) (FreeMonoid'.length v)
  have v_length := Nat.le_max_right (FreeMonoid'.length u) (FreeMonoid'.length v)
  rcases (multiple_delta_neg u (Nat.max (FreeMonoid'.length u) (FreeMonoid'.length v)) (Nat.max k1 k2)
    u_length u_under) with ⟨v', hv', _⟩
  rcases (multiple_delta_neg v (Nat.max (FreeMonoid'.length u) (FreeMonoid'.length v)) (Nat.max k1 k2)
    v_length v_under) with ⟨u', hu', _⟩
  exact Exists.intro u' (Exists.intro v' (hv'.trans hu'.symm))

theorem common_right_mul_inf (u v : PresentedMonoid (@braid_rels_m_inf)) :
    ∃ (u' v' : FreeMonoid' ℕ ), ((u * (PresentedMonoid.mk (braid_rels_m_inf) v'))) =
    v * PresentedMonoid.mk (braid_rels_m_inf) u' := by
  induction u
  induction v
  exact common_right_mul_inf_mk _ _
