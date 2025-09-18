import BraidProject.Solver_G
import BraidProject.ConvertToFin

def is_bounded_by (k : ℕ) (u : List (ℕ × Bool)) := ∀ x ∈ u, x.1 < k

def bb_to_fin (L : List (ℕ × Bool)) (n : ℕ) (hL : is_bounded_by n L) : List (Fin n × Bool) :=
  List.pmap (fun x => fun h => ⟨⟨x.1, by apply hL x; apply h⟩, x.2⟩) L (fun x h => h)

def is_bounded_by_no_bool (k : ℕ) (u : List ℕ) := ∀ x ∈ u, x < k

#check make_fin

def bbnb_to_fin (L : List ℕ) (n : ℕ) (hL : is_bounded_by_no_bool n L) : List (Fin n) :=
  List.pmap (fun x => fun h => ⟨x, by apply hL x; apply h⟩) L (fun x h => h)

def make_fin_no_pred  (n : ℕ) (a : FreeMonoid ℕ) (bound : ∀ x ∈ a, x<n) : FreeMonoid (Fin n) :=
  (FreeMonoid.pmap (λ i => Fin.mk i ) a) bound

theorem braid_rel_inf_to_fin_no_pred (n : ℕ) (a b : FreeMonoid ℕ) (bounded_a: ∀ x, (x ∈ a) → x<n)
    (bounded_b: ∀ x, x∈ b→ x<n) (h : BraidMonoidInf.mk a = BraidMonoidInf.mk b) :
    BraidMonoid.mk _ (make_fin_no_pred n a bounded_a) = BraidMonoid.mk _ (make_fin_no_pred n b bounded_b) := by
  have ba' : ∀ x, x ∈ a → x < (n+1).pred := by convert bounded_a
  have bb' : ∀ x, x ∈ b → x < (n+1).pred := by convert bounded_b
  have H := braid_rel_inf_to_fin (n+1) a b ba' bb' h
  convert H

theorem correct_one_dir_fin {n : ℕ} (ha : ∀ x ∈ a, x < n) (hb : ∀ x ∈ b, x < n)
  (h : final_solver a b) : PresentedMonoid.mk (braid_rels_m n) (make_fin_no_pred n a ha) =
  PresentedMonoid.mk (braid_rels_m n) (make_fin_no_pred n b hb) := by
  match a with
  | [] =>
    match b with
    | [] => rfl
    | b1 :: b2 =>
      simp [final_solver] at h
  | a1 :: a2 =>
    match b with
    | [] => simp [final_solver] at h
    | b1 :: b2 =>
      simp [final_solver] at h
      apply braid_rel_inf_to_fin_no_pred
      rw [← List.append_nil (a1 :: a2), ← List.append_nil (b1 :: b2)]
      apply bm_equiv_of_reversing (by simp) (by simp)
      conv =>
        enter [3]
        rw [to_over_plain, to_up_plain]
        simp
      have H := @solver_equiv (a1 :: a2) (b1 :: b2) (by simp) (by simp)
      rw [h] at H
      exact H

theorem is_bounded_by_append : is_bounded_by n (a ++ b) ↔ is_bounded_by n a ∧ is_bounded_by n b := by
  constructor
  · intro h
    constructor
    · intro x hx
      apply h
      exact List.mem_append_left b hx
    intro x hx
    apply h
    exact List.mem_append_right a hx
  intro h x hx
  apply List.mem_append.mp at hx
  cases hx with
  | inl h1 => apply h.1 _ h1
  | inr h2 => apply h.2 _ h2

theorem reversing_bounded (h : is_bounded_by n a) (hr : reversing a b) : is_bounded_by n b := by
  cases hr with
  | basic h => intro x hx; simp at hx
  | apart h =>
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h3 | h4
    · apply h
      aesop
    apply h
    aesop
  | close h =>
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h3 | h4 | h5 | h6
    · apply h
      aesop
    · rw [h4]
      rename_i i j hij
      apply h (i, false)
      aesop
    · rw [h5]
      rename_i i j hij
      apply h (j, true)
      aesop
    apply h
    aesop

theorem Semi_Thue_reversing_bounded (h : is_bounded_by n L) (h2 : SemiThue reversing L L1) :
  is_bounded_by n L1 := by
  induction h2 with
  | refl a => exact h
  | reduction h1 =>
    rw [is_bounded_by_append, is_bounded_by_append]
    rw [is_bounded_by_append, is_bounded_by_append] at h
    have h3 := reversing_bounded h.1.2 h1
    aesop
  | trans a b c _ _ _ _ => aesop

theorem reverse_complex_bounded (ha : is_bounded_by n a) : is_bounded_by n (reverse_complex a).1 := by
  exact Semi_Thue_reversing_bounded ha (reverse_complex a).2.2

theorem FreeGroup.invRev_bounded_by (ha : is_bounded_by n a) : is_bounded_by n (FreeGroup.invRev a) := by
  intro x hx
  unfold invRev at hx
  simp only [List.mem_map, List.mem_reverse, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨a1, ha1⟩
  rw [← ha1.2]
  apply ha (a1.1, a1.2) ha1.1

set_option pp.proofs true in
theorem List.pmap_inj {α β : Type*} {P : α → Prop} (f : ∀ a, P a → β)
  (hf : ∀ a b ha hb, f a ha = f b hb → a = b) (l1 l2 : List α)
  (h1 : ∀ a ∈ l1, P a) (h2 : ∀ a ∈ l2, P a) :
  List.pmap f l1 h1 = List.pmap f l2 h2 → l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    intro hx
    simp only [pmap_nil, nil_eq, pmap_eq_nil_iff] at hx
    exact hx.symm
  | cons head tail ih =>
    intro hx
    simp at hx
    cases l2 with
    | nil => simp at hx
    | cons head1 tail1 =>
      simp at hx
      refine cons_eq_cons.mpr ?_
      constructor
      · apply hf _ _ _ _ hx.1
      apply ih
      exact hx.2

theorem make_fin_no_pred_inj {n : ℕ} {a b : FreeMonoid ℕ}
  (bound_a : ∀ x ∈ a, x < n) (bound_b : ∀ x ∈ b, x < n)
  (ha : make_fin_no_pred n a bound_a = make_fin_no_pred n b bound_b) :
  a = b := by
  unfold make_fin_no_pred at ha
  apply List.pmap_inj at ha
  exact ha
  intro a b ha hb hx
  simp only [Fin.mk.injEq] at hx
  exact hx

theorem bm_to_bg_fin' {n : ℕ} {a1 b1 : FreeMonoid (Fin n)}(h : PresentedMonoid.mk (braid_rels_m n) a1 =
  PresentedMonoid.mk (braid_rels_m n) b1):
  (PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk (to_over_plain a1)) =
  (PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk (to_over_plain b1)) := by
  apply PresentedMonoid.exact at h
  induction h with
  | of x y h =>
    unfold braid_rels_m at h
    match n with
    | 0 => simp at h
    | 1 => simp at h
    | Nat.succ (Nat.succ n) =>
      simp at h
      cases h with
      | adjacent i =>
        sorry
      | separated i j h =>
        rw [to_over_plain_mul, to_over_plain_mul]
        simp [to_over_plain]
        change PresentedGroup.mk (Braid.braid_rels_fin_coexeter (n + 2))
          (FreeGroup.mk [(i.castSucc.castSucc, true), (j.succ.succ, true)]) =
        PresentedGroup.mk (Braid.braid_rels_fin_coexeter (n + 2))
          (FreeGroup.mk [(j.succ.succ, true), (i.castSucc.castSucc, true)])
        sorry

  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | mul _ _ ih1 ih2 =>
    rw [to_over_plain_mul, to_over_plain_mul, ← FreeGroup.mul_mk,  ← FreeGroup.mul_mk,
    PresentedGroup.mk_mul, PresentedGroup.mk_mul, ih1, ih2]

open Braid in
theorem bm_to_bg_fin {n : ℕ} {a1 b1 : FreeMonoid (Fin n)}(h : PresentedMonoid.mk (braid_rels_m n) a1 =
  PresentedMonoid.mk (braid_rels_m n) b1)
  (bound_a_1 : ∀ x ∈ (List.map (fun x => x.1) a), x < n)
  (ha : a1 = make_fin_no_pred n (List.map (fun x => x.1) a) bound_a_1)
  (bound_a : is_bounded_by n a)
  (bound_b_1 : ∀ x ∈ (List.map (fun x => x.1) b), x < n)
  (hb : b1 = make_fin_no_pred n (List.map (fun x => x.1) b) bound_b_1)
  (bound_b : is_bounded_by n b) :
  (PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk (bb_to_fin a n bound_a)) =
  (PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk (bb_to_fin b n bound_b)) := by
  apply bm_to_bg_fin' at h
  convert h
  · rw [ha]
    unfold bb_to_fin
    unfold to_over_plain
    sorry
  sorry

theorem pg_mk_fg_inv_fin : ((PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk a))⁻¹ =
  (PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk (FreeGroup.invRev a)) := by
  rw [PresentedGroup.mk_inv, FreeGroup.inv_mk]

theorem pg_mk_to_over_plain_inv_fin :
  ((PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk (to_over_plain a)))⁻¹ =
  (PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk (to_up_plain a)) := by
  rw [pg_mk_fg_inv_fin]
  congr
  unfold to_over_plain to_up_plain FreeGroup.invRev
  simp

theorem recover_from_is_true_fin (h : is_true d) : to_over_plain (List.map (fun x ↦ x.1) d) = (d : List (ℕ × Bool)) := by
  induction d with
  | nil => simp [to_over_plain]
  | cons head tail ih =>
    have tt : is_true tail := (is_true_split h).2
    specialize ih tt
    simp only [to_over_plain, List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · have ht : is_true [head] := (is_true_split h).1
      specialize ht head ⟨by simp⟩
      simp [← ht.1]
    rw [← ih]
    unfold to_over_plain
    simp

theorem SemiThue_reversing_to_braid_group_equiv_fin (h : SemiThue reversing a b) (ha : is_bounded_by n a):
  (PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk (make_fin n a sorry)) =
  (PresentedGroup.mk (Braid.braid_rels_fin_coexeter n)) (FreeGroup.mk b) := by
  induction h with
  | refl a => rfl
  | reduction h =>
    rename_i e f g i
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
      PresentedGroup.mk_mul, PresentedGroup.mk_mul, PresentedGroup.mk_mul, PresentedGroup.mk_mul,
      mul_left_inj, mul_right_inj]
    cases h with
    | basic =>
      rename_i i j hij
      apply Nat.eq_of_dist_eq_zero at hij
      rw [← hij]
      change (PresentedGroup.mk Braid.braid_rels_coexeter)
        (FreeGroup.mk ([(i, false)] ++ [(i, true)])) = _
      rw [← FreeGroup.mul_mk]
      unfold FreeGroup.mk
      congr
      exact eq_div_iff_mul_eq'.mp rfl
    | apart h =>
      rename_i i j
      change (Braid.σi i)⁻¹ * Braid.σi j = Braid.σi j * (Braid.σi i)⁻¹
      apply (mul_right_inj (Braid.σi i)).mp
      apply (mul_left_inj (Braid.σi i)).mp
      group
      symm
      exact Braid.braid_group_inf.comm h
    | close h =>
      rename_i i j
      change (Braid.σi i)⁻¹ * Braid.σi j = Braid.σi j *  Braid.σi i * (Braid.σi j)⁻¹ * (Braid.σi i)⁻¹
      apply (mul_right_inj (Braid.σi i)).mp
      apply (mul_left_inj (Braid.σi i)).mp
      apply (mul_left_inj (Braid.σi j)).mp
      group
      symm
      exact Braid.braid_group_inf.braid_dist h
  | trans a b c _ _ ih1 ih2 =>
    exact ih1.trans ih2

theorem solver_g_correct_one_direction_fin {n : ℕ} (ha : is_bounded_by n a) (hb : is_bounded_by n b) :
    solver_g a b = true →
  PresentedGroup.mk (Braid.braid_rels_fin_coexeter n) (FreeGroup.mk (bb_to_fin a n ha)) =
  PresentedGroup.mk (Braid.braid_rels_fin_coexeter n) (FreeGroup.mk (bb_to_fin b n hb)) := by
  intro h
  unfold solver_g at h
  rcases dede : (reverse_complex (a ++ (FreeGroup.invRev b))).2.1 with ⟨d, e, hde⟩
  have H := @correct_one_dir_fin _ _ n (by
    intro x hx
    simp at hx
    rcases hx with h1 | h1
    · have h1' : (x, false) ∈ (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.1 ++
        (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.2.fst := by simp [h1]
      have H := (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.2.2.2.2.1
      rw [← H] at h1'
      apply reverse_complex_bounded _ (x, false) h1'
      apply is_bounded_by_append.mpr
      constructor
      · exact ha
      apply FreeGroup.invRev_bounded_by hb
    have h1' : (x, true) ∈ (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.1 ++
        (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.2.fst := List.mem_append_right _ h1
    have H := (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.2.2.2.2.1
    rw [← H] at h1'
    apply reverse_complex_bounded _ (x, true) h1'
    apply is_bounded_by_append.mpr
    constructor
    · exact ha
    apply FreeGroup.invRev_bounded_by hb)
    (by
    intro x hx
    simp at hx
    rcases hx with h1 | h1
    · have h1' : (x, false) ∈ (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.1 ++
        (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.2.fst := by simp [h1]
      have H := (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.2.2.2.2.1
      rw [← H] at h1'
      apply reverse_complex_bounded _ (x, false) h1'
      apply is_bounded_by_append.mpr
      constructor
      · exact ha
      apply FreeGroup.invRev_bounded_by hb
    have h1' : (x, true) ∈ (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.1 ++
        (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.2.fst := List.mem_append_left _ h1
    have H := (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.2.2.2.2.1
    rw [← H] at h1'
    apply reverse_complex_bounded _ (x, true) h1'
    apply is_bounded_by_append.mpr
    constructor
    · exact ha
    apply FreeGroup.invRev_bounded_by hb) h
  have H2 := SemiThue_reversing_to_braid_group_equiv ((reverse_complex (a ++ (FreeGroup.invRev b))).2.2)
  rw [hde.2.2.1] at H2
  rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
    PresentedGroup.mk_mul, PresentedGroup.mk_mul] at H2
  have d_is : (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.fst = d := by aesop
  simp only [List.map_reverse, d_is] at H
  have e_is : (reverse_complex (a ++ FreeGroup.invRev b)).2.1.2.1 = e := by
     rw [dede]
  simp only [e_is] at H
  apply bm_to_bg_fin' at H
  apply (mul_right_inj ((PresentedGroup.mk (Braid.braid_rels_fin_coexeter n))
    (FreeGroup.mk (to_over_plain (make_fin_no_pred n (List.map (fun x ↦ x.1) e.reverse) (by sorry)))))⁻¹).mpr at H
  simp only [List.map_reverse, inv_mul_cancel] at H
  rw [pg_mk_to_over_plain_inv_fin] at H
  -- rw [pg_mk_to_over_plain_inv, recover_from_is_true hde.1, recover_from_is_false hde.2.1] at H
  -- apply (mul_right_inj (((PresentedGroup.mk Braid.braid_rels_coexeter)
  --       (FreeGroup.mk e))⁻¹)).mpr at H
  -- apply (mul_left_inj ((PresentedGroup.mk Braid.braid_rels_coexeter)
  --       (FreeGroup.mk e))).mpr at H
  -- rw [mul_one, inv_mul_cancel, inv_mul_cancel_left] at H
  -- rw [← H] at H2
  -- apply (mul_left_inj ((PresentedGroup.mk Braid.braid_rels_coexeter)
  --   (FreeGroup.mk (FreeGroup.invRev b)))⁻¹).mpr at H2
  -- rw [mul_inv_cancel_right, one_mul] at H2
  -- rw [H2, PresentedGroup.mk_inv, FreeGroup.inv_mk, FreeGroup.invRev_invRev]

theorem solver_g_correct_fin {n : ℕ} (ha : is_bounded_by n a) (hb : is_bounded_by n b) :
  solver_g a b ↔
  PresentedGroup.mk (Braid.braid_rels_fin_coexeter n) (FreeGroup.mk (bb_to_fin a n ha)) =
  PresentedGroup.mk (Braid.braid_rels_fin_coexeter n) (FreeGroup.mk (bb_to_fin b n hb)) := by
  constructor
  · intro sgt
    exact solver_g_correct_one_direction_fin ha hb sgt
  intro h1
  apply solver_g_correct_other_direction

  sorry
-- #check Quotient.ind
