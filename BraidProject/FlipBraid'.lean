import BraidProject.BraidMonoid
import BraidProject.AcrossStrands'
import BraidProject.Additions.Induction
import BraidProject.Additions.NatDist
import BraidProject.Additions.FreeMonoid

open FreeMonoid

--lemma 3.9 property
theorem generator_sigma_braid_through (i j k : ℕ) (h1: i + 2 ≤ j) (h2 : i < k ∧ k < j) :
    BraidMonoidInf.mk (of k * sigma_braid i j) = BraidMonoidInf.mk (sigma_braid i j * of (k-1)) := by
  induction dist : j - i - 2 generalizing i j k
  · have hk : k= i + 1 := by omega
    have hj : j = i + 2 := by omega
    rw [hj, hk]
    simp only [sigma_braid_succ_succ_ascending, add_tsub_cancel_right]
    exact (BraidMonoidInf.braid dist_succ).symm
  rename_i n ih
  have hk : k ≥ i+1 := by omega
  apply induction_bounded k hk h2.2
  · rw [sigma_braid_ascending_pop, ← mul_assoc, map_mul, ih i (j - 1),
    ← map_mul, mul_assoc, mul_assoc]
    any_goals omega
    apply BraidMonoidInf.append_left_mk
    apply BraidMonoidInf.comm
    unfold Nat.dist; omega
  intro new_k k_bigger new_k_lt _
  rw [sigma_braid_ascending_first, ← mul_assoc, map_mul, BraidMonoidInf.comm,
    ← map_mul, mul_assoc, map_mul, ih]; rfl
  any_goals omega
  unfold Nat.dist ; omega

--lemma 3.10 property
theorem sigma_braid_generator_through (i j k : ℕ) (h1: i + 2 ≤ j) (h2 : i<k∧k<j) :
      BraidMonoidInf.mk (of (k-1) * (sigma_braid j i)) =
      BraidMonoidInf.mk ((sigma_braid j i) * of k) := by
  unfold sigma_braid count_down
  have : ¬ j ≤ i := by omega
  simp only [this, ↓reduceIte]
  rw [← @reverse_reverse _ (of (k -1)), ← @reverse_reverse _ (of k), ← reverse_mul, ← reverse_mul,
    reverse_of, reverse_of, ← BraidMonoidInf.reverse_braid_mk, ← BraidMonoidInf.reverse_braid_mk]
  apply BraidMonoidInf.reverse_eq_reverse_iff.mp
  symm
  have : count_up i j = sigma_braid i j := by
    have : i ≤ j := by linarith
    simp [sigma_braid, this]
  rw [this]
  apply generator_sigma_braid_through
  all_goals omega

theorem word_sigma_braid_through (L) (hb : ∀ x, x ∈ L → x ≥ j ∧ x < n) : BraidMonoidInf.mk (L * sigma_braid (n+1) j) =
    BraidMonoidInf.mk ((sigma_braid (n+1) j) * (FreeMonoid.map (λ i => i+1) L)) := by
  induction L with
  | one =>
    simp only [one_mul, map_one, mul_one]
  | of y =>
    simp only [map_of]
    have : y ∈ of y := by simp
    specialize hb y this
    apply sigma_braid_generator_through _ _ (y + 1)
    · linarith
    omega
  | mul x y hx hy =>
    rw [mul_assoc, BraidMonoidInf.append_left_mk
        (hy fun x1 in_y ↦ hb x1 (mem_mul.mpr (Or.inr in_y))), ← mul_assoc]
    nth_rewrite 3 [map_mul]
    rw [← mul_assoc]
    apply BraidMonoidInf.append_right_mk (hx fun x nx ↦ hb x (mem_mul.mpr (Or.inl nx)))

def delta_braid : ℕ → FreeMonoid ℕ
  | 0 => 1
  | n+1 => (sigma_braid 0 (n+1)) * (delta_braid n)

@[simp]
theorem delta_braid_zero : delta_braid 0 = 1 := rfl

@[simp]
theorem delta_braid_one : delta_braid 1 = of 0 := by simp [delta_braid, sigma_braid]

theorem delta_braid_bounded (n : ℕ) : ∀ k ∈ delta_braid n, k < n := by
  intro k h
  induction n with
  | zero =>  exact (notMem_one h).elim
  | succ n ih =>
    rcases mem_mul.mp h with _ | h1
    · apply sigma_braid_descending_bounded
      assumption
    exact Nat.le.step (ih h1)

theorem map_delta_braid_bounded (n k x : ℕ) (h : x ∈ FreeMonoid.map (fun x => x + k) (delta_braid n)) :
    x < n + k := by
  rcases mem_map.mp h with ⟨w, hw, rfl⟩
  apply delta_braid_bounded at hw
  linarith

theorem generator_sigma_braid_past (m : ℕ) (w : FreeMonoid ℕ) : (∀ k ∈ w, k + 1 < m) →
    BraidMonoidInf.mk (of m * w) = BraidMonoidInf.mk (w * of m) := by
  induction w with
  | one => exact fun _ => rfl
  | of x =>
    intro h
    apply BraidMonoidInf.comm
    specialize h _ FreeMonoid.mem_of_self
    unfold Nat.dist; omega
  | mul x y hx hy =>
    intro h_in
    apply (BraidMonoidInf.append_right_mk <| hx <| fun k k_in => h_in k (mem_mul.mpr (Or.inl k_in))).trans
    rw [mul_assoc, mul_assoc]
    exact BraidMonoidInf.append_left_mk <| hy <| fun k k_in => h_in k (mem_mul.mpr (Or.inr k_in))

-- m is the moved, n is what delta_braid is
theorem generator_delta_braid_past (n m : ℕ) {h : n < m}: BraidMonoidInf.mk (of m * delta_braid n) =
    BraidMonoidInf.mk (delta_braid n * of m) := by
  induction n
  · rfl
  exact generator_sigma_braid_past m (delta_braid _) fun k h1 =>
    Nat.lt_of_le_of_lt (delta_braid_bounded _ k h1) h

theorem factor_delta_braid (n : ℕ) : 1 ≤ n → BraidMonoidInf.mk (delta_braid n) =
    BraidMonoidInf.mk (delta_braid (n-1) * sigma_braid n 0 ) := by
  cases n with
  | zero => aesop
  | succ n =>
    induction n with
    | zero =>
      intro _
      simp [sigma_braid]
    | succ n ih =>
      intro hn
      conv => lhs; unfold delta_braid
      rw [sigma_braid_ascending_pop hn, sigma_braid_descending_first <| Nat.zero_le (n + 1),
        ← mul_assoc, map_mul, ih (by linarith), add_tsub_cancel_right,
        add_tsub_cancel_right, ← map_mul, ← mul_assoc, mul_assoc _ (of (n + 1)),
        map_mul, map_mul, @generator_delta_braid_past (n) (n+1) Nat.le.refl]
      conv => rhs; unfold delta_braid
      repeat rw [map_mul, mul_assoc]

theorem generator_delta_braid_through (n : ℕ)  : ∀ i : ℕ , (i≤  n-1) →
    BraidMonoidInf.mk (of i * (delta_braid n)) = BraidMonoidInf.mk (delta_braid n * of (n-1-i)) := by
    cases n with
    | zero =>
      intro i h1
      simp only [zero_le, tsub_eq_zero_of_le, nonpos_iff_eq_zero] at h1
      rw [h1]
      rfl
    | succ n =>
      induction n with
      | zero =>
        simp
      | succ n hn =>
        intro i i_between
        cases i with
        | zero =>
          simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
          apply (BraidMonoidInf.append_left_mk (factor_delta_braid (n + 2) (Nat.le_add_left 1 _))).trans
          apply (BraidMonoidInf.append_right_mk (hn 0 (Nat.zero_le (n + 1 - 1)))).trans
          rw [mul_assoc]
          apply (BraidMonoidInf.append_left_mk (sigma_braid_generator_through 0 _ n.succ (Nat.le_add_left _ n)
              ⟨Nat.zero_lt_succ n, Nat.le.refl⟩)).trans
          rw [← mul_assoc]
          exact (BraidMonoidInf.append_right_mk (factor_delta_braid n.succ.succ NeZero.one_le).symm)
        | succ k =>
          apply (BraidMonoidInf.append_right_mk (generator_sigma_braid_through 0 n.succ.succ k.succ
            (tsub_add_cancel_iff_le.mp rfl) ⟨Fin.pos ⟨k, Nat.le.refl⟩,
            Nat.lt_succ_iff.mpr i_between⟩)).trans
          rw [mul_assoc]
          apply (BraidMonoidInf.append_left_mk (hn k (Nat.lt_succ_iff.mp i_between))).trans
          rw [← mul_assoc]
          simp only [Nat.succ_eq_add_one, add_tsub_cancel_right, Nat.reduceSubDiff]
          rfl

theorem word_delta_braid_through {n : ℕ} {w : FreeMonoid ℕ} (w_bounded : ∀x, x ∈ w → x < n) :
    BraidMonoidInf.mk (w * delta_braid n) = BraidMonoidInf.mk  (delta_braid n * FreeMonoid.map (λ i => (n-1)-i) w) := by
  induction w
  · simp only [one_mul, map_one, mul_one]
  · rename_i y
    exact generator_delta_braid_through n y (Nat.le_sub_one_of_lt (w_bounded y mem_of_self))
  rename_i z w hx hy
  nth_rewrite 3 [map_mul]
  rw [← mul_assoc]
  rw [← BraidMonoidInf.append_right_mk (hx fun a ha ↦ w_bounded a (mem_mul.mpr (Or.inl ha)))]
  rw [mul_assoc, mul_assoc]
  exact BraidMonoidInf.append_left_mk (hy fun a ha ↦ w_bounded a (mem_mul.mpr (Or.inr ha)))

def additional_braid (n i: ℕ) : FreeMonoid ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | k+2 => if i = n - 1 then sigma_braid (n-1) 0 * FreeMonoid.map (λ i => i+1) (delta_braid (n-1))
          else additional_braid (k+1) i * sigma_braid n 0

theorem additional_braid_spec (i n : ℕ) (h_n : n > 0) (h : i < n) : BraidMonoidInf.mk (delta_braid n) =
    BraidMonoidInf.mk (of i * additional_braid n i) := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => aesop
    | succ n ih =>
      rcases Nat.lt_trichotomy i (n + 1) with lt | eq | bigger
      · have : additional_braid (Nat.succ (Nat.succ n)) i =
                (additional_braid (Nat.succ n) i) * (sigma_braid (n+2) 0) := by
          conv => lhs; unfold additional_braid
          aesop
        rw [this]
        apply (factor_delta_braid n.succ.succ h_n).trans
        rw [← mul_assoc]
        apply BraidMonoidInf.append_right_mk
        apply ih
        all_goals omega
      · have : additional_braid (Nat.succ (Nat.succ n)) i =
            (sigma_braid (n+2-1) 0)*(FreeMonoid.map (λ i => i+1) (delta_braid (n+2-1))) := by
          conv => lhs; unfold additional_braid
          aesop
        rw [this]
        simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
        rw [eq]
        have step_two : ∀ L, (∀ x, x ∈ L → x < n+1) → BraidMonoidInf.mk (L * sigma_braid (n+2) 0) =
            BraidMonoidInf.mk ((sigma_braid (n+2) 0) * (FreeMonoid.map (λ i => i+1) (L))) := by
          intro L hb
          apply word_sigma_braid_through
          aesop
        apply (factor_delta_braid _ (by linarith)).trans
        apply (step_two _ (delta_braid_bounded n.succ)).trans
        conv => rhs; rw [← mul_assoc]
        apply BraidMonoidInf.append_right_mk
        have helper : 0 <= n+1 := by linarith
        rw [sigma_braid_descending_first helper]
      omega

theorem additional_braid_bounded (i n : ℕ) (h : i ≤ n - 1) (x) (x_in : x ∈ additional_braid n i) :
    x < n := by
  cases n with
  | zero => exact (notMem_one x_in).elim
  | succ k =>
    induction k with
    | zero => exact  (notMem_one x_in).elim
    | succ j hj =>
      unfold additional_braid at x_in
      rw [add_tsub_cancel_right] at x_in
      rcases Nat.lt_trichotomy i (j + 1) with lt | rfl | bigger
      · have not_eq : ¬ i = j + 1 := by linarith [lt]
        rw [if_neg not_eq, mem_mul] at x_in
        rcases x_in with in_bound | in_sigma
        · exact Nat.lt_succ_of_lt (hj (Nat.lt_succ_iff.mp lt) in_bound)
        exact sigma_braid_ascending_bounded _ in_sigma
      · simp only [↓reduceIte, mem_mul] at x_in
        rcases x_in with in_sigma | in_delta
        · apply sigma_braid_descending_bounded
          simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, sigma_braid]
          rw [@count_up_pop 0 (j + 2) (by linarith), mem_mul]
          exact Or.inl (mem_reverse.mp in_sigma)
        induction j with
        | zero =>
          simp only [zero_add, delta_braid_one, map_of, mem_of] at in_delta
          aesop
        | succ n _ => exact map_delta_braid_bounded n.succ.succ 1 _ in_delta
      omega

theorem multiple_delta_braid_bounded {n k : ℕ} : ∀ x ∈ delta_braid n ^ k, x < n := by
  induction k with
  | zero => exact fun _ h => (notMem_one h).elim
  | succ k hk =>
    intro x h
    rw [pow_succ' (delta_braid n) k] at h
    rcases (FreeMonoid.mem_mul.mp h) with in_delta | ic
    · exact delta_braid_bounded _ _ in_delta
    exact hk _ ic

theorem equiv_multiple_delta_braid (u : FreeMonoid ℕ) (l n : ℕ) (h : FreeMonoid.length u ≤ l)
    (bounded : ∀ x, x ∈ u → x < n) : ∃ w, BraidMonoidInf.mk (u * w) = ⟦(delta_braid n)^l⟧ ∧
    ∀ x, x ∈ w → x < n := by
  induction l generalizing u with
  | zero =>
    rw [FreeMonoid.length_eq_zero.mp (nonpos_iff_eq_zero.mp h)]
    use 1
    exact ⟨rfl, fun _ h => (notMem_one h).elim⟩
  | succ j hj =>
    rcases FreeMonoid.eq_one_or_has_last_elem u with rfl | ⟨front, caboose, rfl⟩
    · use delta_braid n ^ Nat.succ j
      exact ⟨rfl, multiple_delta_braid_bounded⟩
    have front_length : front.length ≤ j := by
      rw [FreeMonoid.length_mul, FreeMonoid.length_of] at h
      exact Nat.lt_succ_iff.mp h
    have front_bounded : ∀ x, x ∈ front → x < n :=
      fun x x_in => bounded _ <| FreeMonoid.mem_mul.mpr <| .inl x_in
    rcases hj front front_length front_bounded with ⟨w', hw⟩
    let phi_w' := FreeMonoid.map (λ i => n - 1 - i) w'
    use additional_braid n caboose * phi_w'
    have caboose_bounded : caboose < n := by
      apply bounded
      rw [FreeMonoid.mem_mul]
      exact Or.inr (FreeMonoid.mem_of.mpr rfl)
    constructor
    · rw [mul_assoc, map_mul, ← mul_assoc, map_mul]
      rw [← additional_braid_spec caboose _ (Nat.zero_lt_of_lt caboose_bounded) caboose_bounded,
        ← map_mul, ← (word_delta_braid_through hw.right)]
      rw [← map_mul, ← mul_assoc, map_mul, hw.1]
      rfl
    intro x x_in
    rcases FreeMonoid.mem_mul.mp x_in with in_additional_braid | in_phi
    · exact additional_braid_bounded caboose n (by omega) _ in_additional_braid
    rcases FreeMonoid.mem_map.mp in_phi with ⟨w, hw⟩
    omega

theorem common_right_mul_inf (u v : BraidMonoidInf) : ∃ u' v', u * v' = v * u' := by
  induction u with | h u
  induction v with | h v
  rcases (FreeMonoid.bounded u) with ⟨k1, hk1⟩
  rcases (FreeMonoid.bounded v) with ⟨k2, hk2⟩
  rcases (equiv_multiple_delta_braid u (Nat.max (FreeMonoid.length u) (FreeMonoid.length v)) (Nat.max k1 k2)
    (by aesop) (by aesop)) with ⟨v', hv', _⟩
  rcases (equiv_multiple_delta_braid v (Nat.max (FreeMonoid.length u) (FreeMonoid.length v)) (Nat.max k1 k2)
    (by aesop) (by aesop)) with ⟨u', hu', _⟩
  exact .intro ⟦u'⟧ (.intro ⟦v'⟧ (hv'.trans hu'.symm))

theorem common_right_mul_inf_mk (u v) : ∃ u' v', BraidMonoidInf.mk (u*v') = ⟦v*u'⟧ := by
  rcases common_right_mul_inf ⟦u⟧ ⟦v⟧ with ⟨u', v', huv⟩
  induction u' with | h u''
  induction v' with | h v''
  use u'', v''
  exact huv

theorem common_left_mul_inf (u v : BraidMonoidInf) : ∃ u' v', u' * u = v' * v := by
  rcases common_right_mul_inf (BraidMonoidInf.reverse_braid u)
    (BraidMonoidInf.reverse_braid v) with ⟨a, b, hab⟩
  use BraidMonoidInf.reverse_braid b, BraidMonoidInf.reverse_braid a
  have this := congr_arg BraidMonoidInf.reverse_braid hab
  simp only [BraidMonoidInf.reverse_braid_mul, BraidMonoidInf.reverse_reverse] at this
  simp [this]
