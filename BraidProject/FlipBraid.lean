import BraidProject.BraidMonoid
import BraidProject.AcrossStrands
import BraidProject.InductionWithBounds
import BraidProject.FreeMonoid_mine

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

theorem prepend_k (i j k : ℕ) (h1: j>=i+2) (h2 : i<k∧k<j) :
    BraidMonoidInf.mk (of k * (sigma_neg i j)) = BraidMonoidInf.mk ((sigma_neg i j) *
    (of (k-1))) := by
  have i_lt_j : i<j := by linarith [h1]
  have H_absdiff : Nat.dist i j >= 2 := or_dist_iff.mpr (Or.inl h1)
  have H18 : ∀ i j, i < j → Nat.dist i j = 2 → j=i+2 := by
    intro i j lt dist
    rcases or_dist_iff_eq.mp dist with h1 | h2
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
    rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_succ_le (Nat.lt_of_succ_lt h))]
    exact Nat.le_sub_of_add_le' h
  rename_i x y hx hy
  intro h_in
  have first : BraidMonoidInf.mk (of m * (x * y)) = BraidMonoidInf.mk (x * (of m * y)) := by
    rw [← mul_assoc, ← mul_assoc]
    exact BraidMonoidInf.append_right_mk <| hx <| fun k k_in => h_in k (mem_mul.mpr (Or.inl k_in))
  have second : BraidMonoidInf.mk (x * (of m * y)) = BraidMonoidInf.mk (x * y * of m) := by
    rw [mul_assoc]
    exact BraidMonoidInf.append_left_mk <| hy <| fun k k_in => h_in k (mem_mul.mpr (Or.inr k_in))
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
  cases n with
  | zero => exact fun h => (Set.right_mem_Ico.mp ⟨h, h⟩).elim
  | succ n =>
    induction n with
    | zero => exact fun _ => rfl
    | succ n ih =>
      intro hn
      have third : BraidMonoidInf.mk ((sigma_neg 0 ((n+2)-1)) * of ((n+2)-1) * (delta_neg ((n+2)-1))) =
          BraidMonoidInf.mk ((sigma_neg 0 ((n+2)-1)) * of ((n+2)-1) * (delta_neg ((n+2)-2)) * (sigma_neg ((n+2)-1) 0)) := by
        repeat rw [mul_assoc]
        apply BraidMonoidInf.append_left_mk
        apply BraidMonoidInf.append_left_mk
        simp only [Nat.add_succ_sub_one, add_tsub_cancel_right]
        exact ih NeZero.one_le
      have fourth : BraidMonoidInf.mk ((sigma_neg 0 ((n+2)-1)) * of ((n+2)-1) * (delta_neg ((n+2)-2)) * (sigma_neg ((n+2)-1) 0)) =
          BraidMonoidInf.mk ((sigma_neg 0 ((n+2)-1)) * (delta_neg ((n+2)-2)) * of ((n+2)-1) * (sigma_neg ((n+2)-1) 0)) := by
        apply BraidMonoidInf.append_right_mk
        rw [mul_assoc, mul_assoc]
        apply BraidMonoidInf.append_left_mk
        apply sigma_delta_swap (n) (n+1)
        exact Nat.le.refl
      change BraidMonoidInf.mk ((sigma_neg 0 (n+2)) * (delta_neg ((n+2)-1))) = _
      rw [sigma_neg_last hn, sigma_neg_big_first <| Nat.zero_le (n + 1), ← mul_assoc]
      apply third.trans fourth

theorem swap_sigma_delta (n : ℕ)  : ∀ i : ℕ , (i<= n-1) →
    BraidMonoidInf.mk (of i * (delta_neg n)) = BraidMonoidInf.mk (delta_neg n * of (n-1-i)) := by
    cases n with
    | zero =>
      intro i h1
      simp only [Nat.zero_eq, ge_iff_le, zero_le, tsub_eq_zero_of_le, nonpos_iff_eq_zero] at h1
      rw [h1]
      rfl
    | succ n =>
      induction n with
      | zero =>
        simp only [Nat.zero_eq, Nat.reduceSucc, ge_iff_le, le_refl, tsub_eq_zero_of_le,
        nonpos_iff_eq_zero, zero_le, forall_eq]
        rfl
      | succ n hn =>
        intro i i_between
        cases i with
        | zero =>
          simp only [Nat.zero_eq, Nat.succ_sub_succ_eq_sub, tsub_zero]
          apply (BraidMonoidInf.append_left_mk (factor_delta (n + 2) (Nat.le_add_left 1 _))).trans
          apply (BraidMonoidInf.append_right_mk (hn 0 (Nat.zero_le (n + 1 - 1)))).trans
          rw [mul_assoc]
          apply (BraidMonoidInf.append_left_mk (append_k 0 _ n.succ (Nat.le_add_left _ n)
              ⟨Nat.zero_lt_succ n, Nat.le.refl⟩)).trans
          rw [← mul_assoc]
          exact (BraidMonoidInf.append_right_mk (factor_delta n.succ.succ NeZero.one_le).symm)
        | succ k =>
          apply (BraidMonoidInf.append_right_mk (prepend_k 0 n.succ.succ k.succ
            (tsub_add_cancel_iff_le.mp rfl) ⟨Fin.pos ⟨k, Nat.le.refl⟩,
            Nat.lt_succ.mpr i_between⟩)).trans
          rw [mul_assoc]
          apply (BraidMonoidInf.append_left_mk (hn k (Nat.lt_succ.mp i_between))).trans
          rw [← mul_assoc]
          simp only [Nat.succ_eq_add_one, add_tsub_cancel_right, Nat.reduceSubDiff]
          rfl

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
    exact BraidMonoidInf.append_right_mk (Eq.symm (hx fun a ha ↦ hxy a (mem_mul.mpr (Or.inl ha))))
  have step_two : BraidMonoidInf.mk (z * ((delta_neg n) * (map fun i => n - 1 - i) w)) =
      BraidMonoidInf.mk (z * w * (delta_neg n)) := by
    rw [mul_assoc]
    exact BraidMonoidInf.append_left_mk (Eq.symm (hy fun a ha ↦ hxy a (mem_mul.mpr (Or.inr ha))))
  exact (step_one.trans step_two).symm

def boundary (n i: ℕ) : FreeMonoid' ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | k+2 => if i = n-1 then
            (sigma_neg (n-1) 0)*(FreeMonoid'.map (λ i => i+1) (delta_neg (n-1)))
          else (boundary (k+1) i) * (sigma_neg n 0)

theorem boundary_spec (i n : ℕ) (h_n : n > 0) (h : i ≤ n-1) : BraidMonoidInf.mk
    (delta_neg n) = BraidMonoidInf.mk (of (i)*(boundary n i)) := by
  cases n with
  | zero =>
    exfalso -- n=0
    linarith [h_n]
  | succ n =>
    induction n with
    | zero =>
      simp only [zero_add, ge_iff_le, le_refl, tsub_eq_zero_of_le, nonpos_iff_eq_zero] at h -- n=1
      rw [h]
      rfl
    | succ n ih =>
      have H : i<n+1 ∨ i=n+1 ∨ i>n+1 := by exact Nat.lt_trichotomy i (n + 1)
      rcases H with lt | last_two
      · have boundary_is : boundary (Nat.succ (Nat.succ n)) i =
                (boundary (Nat.succ n) i) * (sigma_neg (n+2) 0) := by
          conv => lhs; unfold boundary
          have H : ¬ i=n+1 := by linarith [ih]
          simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, H, ↓reduceIte]
        rw [boundary_is]
        apply (factor_delta n.succ.succ h_n).trans
        rw [← mul_assoc]
        apply BraidMonoidInf.append_right_mk
        apply ih (Fin.pos ⟨i, lt⟩)
        simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
        exact Nat.lt_succ.mp lt
      · rcases last_two with eq | bigger
        · have boundary_is : boundary (Nat.succ (Nat.succ n)) i =
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
            rw [mul_assoc, BraidMonoidInf.append_left_mk
                (hy fun x1 in_y ↦ hxy x1 (mem_mul.mpr (Or.inr in_y))), ← mul_assoc, ← mul_assoc]
            exact BraidMonoidInf.append_right_mk (hx fun x nx ↦ hxy x (mem_mul.mpr (Or.inl nx)))
          apply step_one.trans
          apply (step_two' _ (delta_neg_bounded n.succ)).trans
          conv => rhs; rw [← mul_assoc]
          apply BraidMonoidInf.append_right_mk
          have helper : 0 <= n+1 := by linarith
          rw [sigma_neg_big_first helper]
        exfalso
        simp only [add_tsub_cancel_right] at h
        linarith [bigger, h]

theorem boundary_bounded (i n : ℕ) (h_n : n>0) (h : i<=n-1) : ∀ x, x ∈ boundary n i → x < n := by
  cases n with
  | zero => exact (LT.lt.false h_n).elim
  | succ k =>
    induction k with
    | zero => exact fun x h_empty => (mem_one_iff.mp h_empty).elim
    | succ j hj =>
      intro x h_boundary
      unfold boundary at h_boundary
      rw [add_tsub_cancel_right] at h_boundary
      rcases Nat.lt_trichotomy i (j + 1) with lt | eq_or_bigger
      · have not_eq : ¬ i = j+1 := by linarith [lt]
        rw [if_neg not_eq, mem_mul] at h_boundary
        rcases h_boundary with in_bound | in_sigma
        · exact Nat.lt.step (hj (Fin.pos ⟨i, lt⟩) (Nat.lt_succ.mp lt) _ in_bound)
        exact sigma_neg_bounded _ in_sigma
      rcases eq_or_bigger with eq | bigger
      · simp only [eq] at h_boundary
        rw [ite_true, mem_mul] at h_boundary
        rcases h_boundary with in_sigma | in_delta
        · apply sigma_neg_bounded
          unfold sigma_neg
          simp only [Nat.succ_ne_zero (j + 1), ↓reduceIte, not_lt_zero', tsub_zero]
          unfold sigma_neg at in_sigma
          simp only [Nat.succ_ne_zero j, ↓reduceIte, not_lt_zero', tsub_zero] at in_sigma
          change x ∈ count_down ((Nat.succ j) + 1 - 0) _ 0
          rw [@count_down_pop 0 (Nat.succ j) (Nat.zero_le (Nat.succ j)), mem_mul]
          exact Or.inr in_sigma
        induction j with
        | zero =>
          simp only [Nat.zero_eq, zero_add, mem_map] at in_delta
          repeat unfold delta_neg at in_delta
          unfold sigma_neg at in_delta
          repeat unfold count_up at in_delta
          simp only [zero_add, zero_ne_one, ↓reduceIte, zero_lt_one, mul_one, mem_of,
            exists_eq_left] at in_delta
          rw [← in_delta]
          exact Nat.le.refl
        | succ n _ => exact map_delta_neg_bounded n.succ.succ 1 _ in_delta
      rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h
      linarith [bigger, h]

theorem multiple_delta_neg_bounded {n k : ℕ} : ∀ x ∈ delta_neg n ^ k, x < n := by
  induction k with
  | zero => exact fun _ h => (mem_one_iff.mp h).elim
  | succ k hk =>
    intro x h
    rw [pow_succ' (delta_neg n) k] at h
    rcases (FreeMonoid'.mem_mul.mp h) with in_delta | ic
    · exact delta_neg_bounded _ _ in_delta
    exact hk _ ic

theorem multiple_delta_neg (u : FreeMonoid' ℕ) (l n : ℕ) (h : FreeMonoid'.length u <= l)
  (bounded : ∀ x, x ∈ u → x < n)
  : ∃ w, BraidMonoidInf.mk (u * w) = BraidMonoidInf.mk ((delta_neg n)^l) ∧
    (∀ x, x ∈ w → x < n)  := by
  have helper : ∀ l, ∀ n, ∀ u, (u.length <= l) → (∀ x, x ∈ u → x < n) →
      ∃ w, BraidMonoidInf.mk (u * w) = BraidMonoidInf.mk ((delta_neg n)^l) ∧ (∀ x, x ∈ w → x < n) := by
    intro l
    induction l with
    | zero =>
      intro n u u_length _
      rw [FreeMonoid'.eq_one_of_length_eq_zero (nonpos_iff_eq_zero.mp u_length)]
      use 1
      exact ⟨rfl, fun _ h => (mem_one_iff.mp h).elim⟩
    | succ j hj =>
      intro n u u_length bounded_u
      rcases FreeMonoid'.eq_one_or_has_last_elem u with ⟨thing, prf⟩ | ⟨front, caboose, h⟩
      · use delta_neg n ^ Nat.succ j
        exact ⟨rfl, multiple_delta_neg_bounded⟩
      rw [h]
      have front_length : FreeMonoid'.length front <= j := by
        rw [h, FreeMonoid'.length_mul, FreeMonoid'.length_of] at u_length
        exact Nat.lt_succ.mp u_length
      have front_bounded : ∀ x, x ∈ front → x < n := by
        rw [h] at bounded_u
        exact fun x x_in => bounded_u _ <| FreeMonoid'.mem_mul.mpr <| Or.inl x_in
      rcases hj n front front_length front_bounded with ⟨w', hw⟩
      let phi_w' := FreeMonoid'.map (λ i => n-1-i) w'
      use boundary n caboose * phi_w'
      have H : ∀ a b, BraidMonoidInf.mk (a * b) = BraidMonoidInf.mk a * BraidMonoidInf.mk b :=
        fun _ _ => rfl
      have caboose_bounded : caboose < n := by
        apply bounded_u
        rw [h, FreeMonoid'.mem_mul]
        exact Or.inr (FreeMonoid'.mem_of.mpr rfl)
      have step_one : BraidMonoidInf.mk (front * (of caboose) * (boundary n caboose * phi_w')) =
        BraidMonoidInf.mk (front * delta_neg n * phi_w') := by
        repeat rw [H]
        rw [boundary_spec caboose _ (Fin.pos (Fin.mk caboose caboose_bounded)) (Nat.le_sub_one_of_lt caboose_bounded), H]
        repeat rw [mul_assoc]
      have step_two : BraidMonoidInf.mk (front * (delta_neg n) * phi_w') =
          BraidMonoidInf.mk (front * w' * (delta_neg n)) := by
        rw [mul_assoc, H, (swap_sigma_delta_souped hw.right).symm, mul_assoc, H]
        rfl
      constructor
      · apply step_one.trans
        apply step_two.trans
        show BraidMonoidInf.mk (front * w') * BraidMonoidInf.mk (delta_neg n) = _
        rw [hw.1]
        rfl
      intro x x_in
      rcases FreeMonoid'.mem_mul.mp x_in with in_boundary | in_phi
      · apply boundary_bounded caboose n _ (Nat.le_sub_one_of_lt caboose_bounded) _ in_boundary
        cases n with
        | zero =>
          have H : caboose < 0 := by
            apply bounded_u
            rw [h, FreeMonoid'.mem_mul]
            exact Or.inr (mem_of.mpr (Eq.refl caboose))
          exact (Nat.not_lt_zero caboose H).elim
        | succ n => exact Fin.pos ⟨n, Nat.le.refl⟩
      rcases FreeMonoid'.mem_map.mp in_phi with ⟨w, hw⟩
      rw [← hw.2]
      exact Nat.lt_of_le_of_lt (Nat.sub_le (n - 1) _)
          (Nat.sub_one_lt_of_le (Fin.pos (Fin.mk caboose caboose_bounded)) Nat.le.refl)
  exact helper _ _ _ h bounded

-- though this one is quickly done!
theorem is_bounded (u : FreeMonoid' ℕ) : ∃ k, ∀ x ∈ u, x < k := by
  induction u using FreeMonoid'.inductionOn'
  · use 1
    exact fun _ h => (mem_one_iff.mp h).elim
  rename_i head tail tail_ih
  rcases tail_ih with ⟨old_k, kh⟩
  use Nat.max old_k (head+1)
  intro x x_in
  rcases x_in
  · exact lt_max_of_lt_right Nat.le.refl
  next x_in_tail =>
  exact lt_max_iff.mpr (Or.inl (kh x x_in_tail))

theorem common_right_mul_inf_mk (u v : FreeMonoid' ℕ) : ∃ (u' v' : FreeMonoid' ℕ ), BraidMonoidInf.mk (u*v') = BraidMonoidInf.mk (v*u') := by
  rcases (is_bounded u) with ⟨k1, hk1⟩
  rcases (is_bounded v) with ⟨k2, hk2⟩
  have u_under : ∀ x ∈ u, x < Nat.max k1 k2 :=
    fun x h => Nat.lt_of_lt_of_le (hk1 x h) (Nat.le_max_left k1 k2)
  have v_under : ∀ x ∈ v, x < Nat.max k1 k2 :=
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
