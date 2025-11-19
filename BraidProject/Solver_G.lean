import BraidProject.Solver_ST
import BraidProject.BraidGroup
import BraidProject.OreLocalizationPresented
import BraidProject.Cancellability
import BraidProject.Widgets

-- give a list, returns the maximal true prefix, and then the rest as a pair
def separate_maximal_true_prefix (c : List (ℕ × Bool)) : List (ℕ × Bool) × List (ℕ × Bool) :=
  match c with
  | [] => ([], [])
  | (c1, false) :: c2 => ([], (c1, false) :: c2)
  | (c1, true) :: c2 => ((c1, true) :: (separate_maximal_true_prefix c2).1, (separate_maximal_true_prefix c2).2)

theorem separate_maximal_true_prefix_correct :
    (separate_maximal_true_prefix L).1 ++ (separate_maximal_true_prefix L).2 = L := by
  induction L with
  | nil => exact List.append_nil _
  | cons d e ih =>
    match d with
    | (d1, false) => exact List.nil_append _
    | (d2, true) =>
      simp only [separate_maximal_true_prefix, List.cons_append, ih]

def separate_maximal_true_prefix_is_true : is_true (separate_maximal_true_prefix L).1 := by
  induction L with
  | nil =>
    exact is_true_nil
  | cons d e ih =>
    match d with
    | (d1, false) =>
      exact is_true_nil
    | (d2, true) =>
      exact is_true_cons _ ih

-- give a list, returns the maximal false prefix, and then the rest as a pair
def separate_maximal_false_prefix (c : List (ℕ × Bool)) : List (ℕ × Bool) × List (ℕ × Bool) :=
  match c with
  | [] => ([], [])
  | (c2, true) :: c1 => ([], (c2, true) :: c1)
  | (d, false) :: e => ((d, false) :: (separate_maximal_false_prefix e).1, (separate_maximal_false_prefix e).2)

theorem separate_maximal_false_prefix_correct :
    (separate_maximal_false_prefix L).1 ++ (separate_maximal_false_prefix L).2 = L := by
  induction L with
  | nil => simp [separate_maximal_false_prefix]
  | cons d e ih =>
    match d with
    | (d1, true) =>
      simp [separate_maximal_false_prefix, ih]
    | (d2, false) =>
      simp [separate_maximal_false_prefix, ih]

def separate_maximal_false_prefix_is_false : is_false (separate_maximal_false_prefix L).1 := by
  induction L with
  | nil =>
    simp [separate_maximal_false_prefix]
    exact is_false_nil
  | cons d e =>
    match d with
    | (d1, true) =>
      simp [separate_maximal_false_prefix]
      exact is_false_nil
    | (d2, false) =>
      simp [separate_maximal_false_prefix]
      apply is_false_cons
      assumption

-- makes a list into the first run of falses, then the run of trues, then the rest
def separate_first_pair (L) := ((separate_maximal_false_prefix L).1,
  (separate_maximal_true_prefix (separate_maximal_false_prefix L).2).1,
  (separate_maximal_true_prefix (separate_maximal_false_prefix L).2).2)

theorem separate_first_pair_correct (L) :
    (separate_first_pair L).1 ++ (separate_first_pair L).2.1 ++ (separate_first_pair L).2.2 = L := by
  unfold separate_first_pair
  simp [separate_maximal_true_prefix_correct, separate_maximal_false_prefix_correct]

def separate_first_pair_first_false (L) : is_false (separate_first_pair L).1 := by
  apply separate_maximal_false_prefix_is_false

def separate_first_pair_second_true (L) : is_true (separate_first_pair L).2.1 := by
  apply separate_maximal_true_prefix_is_true

theorem separate_first_pair_length_disj (hl : L.length > 0) :
    (separate_first_pair L).1.length > 0 ∨ (separate_first_pair L).2.1.length > 0 := by
  match L with
  | [] => simp at hl
  | (a, false) :: L1 =>
    simp [separate_first_pair, separate_maximal_false_prefix]
  | (b, true) :: L2 =>
    simp [separate_first_pair, separate_maximal_false_prefix, separate_maximal_true_prefix]

theorem separate_first_pair_length (hl : L.length > 0) :
    (separate_first_pair L).1.length + (separate_first_pair L).2.1.length > 0 := by
  match L with
  | [] => simp at hl
  | (a, false) :: L1 =>
    simp [separate_first_pair, separate_maximal_false_prefix]
  | (b, true) :: L2 =>
    simp [separate_first_pair, separate_maximal_false_prefix, separate_maximal_true_prefix]

theorem separate_first_pair_nil_nil (h : separate_first_pair L = ([], [], c)) : c = [] := by
  match c with
  | [] => rfl
  | c1 :: c2 =>
    have H := separate_first_pair_correct L
    have H : L = c1 :: c2 := by simp_all
    have H2 := @separate_first_pair_length L (by rw [H]; simp)
    simp_all

theorem to_up_plain_no_bool {L : List (ℕ × Bool)} (h : is_false L) :
  to_up_plain (List.map (fun x ↦ x.1) L.reverse) = L := by
  induction L using List.reverseRecOn with
  | nil => simp [to_up_plain]
  | append_singleton l a ih =>
    have hl : is_false l :=(is_false_append h).1
    simp [to_up_plain]
    rw [← List.concat_eq_append, ← List.concat_eq_append, List.concat_inj]
    constructor
    · unfold to_up_plain at ih
      specialize ih hl
      rw [← ih]
      simp
    have ha : is_false [a] := (is_false_append h).2
    specialize ha a ⟨by simp⟩
    simp [← ha.1]

theorem to_over_plain_no_bool {L : List (ℕ × Bool)} (h : is_true L) :
  to_over_plain (List.map (fun x ↦ x.1) L) = L := by
  induction L with
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

theorem separate_first_pair_cons_false(h : separate_first_pair L = (a, b, c)) :
  separate_first_pair ((d, false) :: L) = ((d, false) :: a, b, c) := by
  unfold separate_first_pair
  simp [separate_maximal_false_prefix]
  unfold separate_first_pair at h
  simp [separate_maximal_false_prefix] at h
  simp_all

theorem c_nil_of_separate_no_true (h : separate_first_pair L = (a, ([], c))) : c = [] := by
  induction L generalizing a c with
  | nil =>
    have H := separate_first_pair_correct []
    simp_all
  | cons head tail ih =>
    match head with
    | (d, false) =>
      have H := separate_first_pair_correct (head :: tail)
      simp_all
      match a with
      | [] =>
        apply separate_first_pair_nil_nil h
      | a1 :: a2 =>
        simp [separate_first_pair, separate_maximal_false_prefix] at h
        specialize @ih a2 c
        apply ih
        unfold separate_first_pair
        simp_all
    | (d, true) =>
      match a with
      | [] =>
        apply separate_first_pair_nil_nil h
      | a1 :: a2 =>
        simp [separate_first_pair, separate_maximal_false_prefix] at h

def reverse_complex (L : List (ℕ × Bool)) : (L1 : List (ℕ × Bool)) × in_order L1 ×
    SemiThue reversing L L1 :=
  match L with
  | [] => by
    use []
    constructor
    · exact in_order_nil
    exact SemiThue.refl _
  | l1 :: l2 =>
  match hs : separate_first_pair (l1 :: l2) with
  | ([], (b, c)) => by
    have hc : c.length < (l1 :: l2).length := by
      have H := separate_first_pair_correct (l1 :: l2)
      have c_is : c = (separate_first_pair (l1 :: l2)).2.2 := by simp [hs]
      rw [c_is]
      apply congr_arg List.length at H
      simp only [List.append_assoc, List.length_append, List.length_cons] at H
      rw [List.length_cons, ← H, ← add_assoc]
      refine Nat.lt_add_of_pos_left ?_
      apply separate_first_pair_length ?_
      simp
    use (b++ (reverse_complex c).1)
    have H : is_true b := by
      have H : b = (separate_first_pair (l1 :: l2)).2.1 := by simp [hs]
      rw [H]
      apply separate_first_pair_second_true
    rcases (reverse_complex c).2.1 with ⟨d, e, hde⟩
    constructor
    · use b++d, e
      constructor
      · apply is_true_of_true_true H hde.1
      constructor
      · exact hde.2.1
      constructor
      rw [hde.2.2.1]
      simp
    have H := separate_first_pair_correct (l1 :: l2)
    simp [hs] at H
    rw [← H]
    apply SemiThue_append_left (reverse_complex c).2.2
  | (a1::a2, ([], c)) => by
    have hc : c = [] := by apply c_nil_of_separate_no_true hs
    use a1 :: a2
    have af : is_false (a1 :: a2) := by
      have H : a1 :: a2 = (separate_first_pair (l1 :: l2)).1 := by simp [hs]
      rw [H]
      apply separate_first_pair_first_false
    have H1 := separate_first_pair_correct (l1 :: l2)
    have : l1 :: l2 = a1 :: a2 := by simp_all
    rw [this]
    constructor
    · exact in_order_of_false af
    exact SemiThue.refl _
  | (a1::a2, (b1::b2, c)) => by
    have H := solver_long (List.map (fun x => x.1) (a1 :: a2).reverse)
      (List.map (fun x => x.1) (b1 :: b2)) (by simp) (by simp)
    have H1 : in_order _ := solver_long_in_order (List.map (fun x => x.1) (a1 :: a2).reverse)
      (List.map (fun x => x.1) (b1 :: b2)) (by simp) (by simp)
    rcases H1 with ⟨d, e, hde⟩
    have hc : c.length < (l1 :: l2).length := by
      have H := separate_first_pair_correct (l1 :: l2)
      have c_is : c = (separate_first_pair (l1 :: l2)).2.2 := by simp [hs]
      rw [c_is]
      apply congr_arg List.length at H
      simp only [List.append_assoc, List.length_append, List.length_cons] at H
      rw [List.length_cons, ← H, ← add_assoc]
      refine Nat.lt_add_of_pos_left ?_
      apply separate_first_pair_length ?_
      simp
    have H2 := reverse_complex c
    rcases H2.2.1 with ⟨f, g, hfg⟩
    match e with
    | [] =>
      use d++f++g
      constructor
      · use (d ++ f), g
        constructor
        · apply is_true_of_true_true hde.1 hfg.1
        constructor
        · exact hfg.2.1
        constructor
        rfl
      have H' := separate_first_pair_correct (l1 :: l2)
      simp only [hs, List.cons_append, List.append_assoc] at H'
      rw [List.append_nil] at hde
      rw [← H', ← hde.2.2.1, List.append_assoc _ f g, ← hfg.2.2.1,
        ← List.cons_append, ← List.cons_append, ← List.append_assoc]
      apply SemiThue_both_sides
      · have H'' := @solver_equiv (List.map (fun x => x.1) (a1 :: a2).reverse)
          (List.map (fun x => x.1) (b1 :: b2)) (by simp) (by simp)
        have H3 : (to_up_plain (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
          to_over_plain (List.map (fun x ↦ x.1) (b1 :: b2))) = a1 :: a2 ++ b1 :: b2 := by
          have af := (separate_first_pair_first_false (l1 :: l2))
          rw [hs] at af
          have bt := (separate_first_pair_second_true (l1 :: l2))
          rw [hs] at bt
          rw [to_up_plain_no_bool af, to_over_plain_no_bool bt]
        rw [← H3]
        exact H''
      apply H2.2.2
    | e1 :: e2 =>
      match f with
      | [] =>
        use d ++ (e1 :: e2) ++ g
        constructor
        · use d, (e1::e2) ++ g
          constructor
          · exact hde.1
          constructor
          · apply is_false_of_false_false hde.2.1 hfg.2.1
          constructor
          simp
        have H' := separate_first_pair_correct (l1 :: l2)
        simp only [hs, List.cons_append, List.append_assoc] at H'
        rw [List.nil_append] at hfg
        rw [← H', ← hde.2.2.1, ← hfg.2.2.1,
          ← List.cons_append, ← List.cons_append, ← List.append_assoc]
        apply SemiThue_both_sides
        · have H3 := @solver_equiv (List.map (fun x => x.1) (a1 :: a2).reverse)
            (List.map (fun x => x.1) (b1 :: b2)) (by simp) (by simp)
          have H4 : (to_up_plain (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
            to_over_plain (List.map (fun x ↦ x.1) (b1 :: b2))) = a1 :: a2 ++ b1 :: b2 := by
            have af := (separate_first_pair_first_false (l1 :: l2))
            rw [hs] at af
            have bt := (separate_first_pair_second_true (l1 :: l2))
            rw [hs] at bt
            rw [to_up_plain_no_bool af, to_over_plain_no_bool bt]
          rw [← H4]
          exact H3
        apply H2.2.2
      | f1 :: f2 =>
        have H3 := solver_long (List.map (fun x => x.1) (e1 :: e2).reverse)
          (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)
        have H4 : in_order _ := solver_long_in_order (List.map (fun x => x.1) (e1 :: e2).reverse)
          (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)
        rcases H4 with ⟨i, j, hij⟩
        use d ++ i ++ j ++ g
        constructor
        · use (d ++ i), j ++ g
          constructor
          · apply is_true_of_true_true hde.1 hij.1
          constructor
          · apply is_false_of_false_false hij.2.1 hfg.2.1
          constructor
          simp
        have H' := separate_first_pair_correct (l1 :: l2)
        simp only [hs, List.cons_append, List.append_assoc] at H'
        rw [← H', List.append_assoc d i j, ← hij.2.2.1]
        have H5 := @solver_equiv (List.map (fun x => x.1) (e1 :: e2).reverse)
            (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)
        have H6 : (to_up_plain (List.map (fun x ↦ x.1) (e1 :: e2).reverse) ++
            to_over_plain (List.map (fun x ↦ x.1) (f1 :: f2))) = e1 :: e2 ++ f1 :: f2 := by
          rw [to_up_plain_no_bool hde.2.1, to_over_plain_no_bool hfg.1]
        have H7 : SemiThue reversing (a1 :: (a2 ++ b1 :: (b2 ++ c)))
          (d ++ (e1 :: e2 ++ f1 :: f2 ++ g)) := by
          rw [List.append_assoc (e1 :: e2), ← List.append_assoc d,
            ← List.cons_append, ← List.cons_append, ← List.append_assoc]
          apply SemiThue_both_sides
          · rw [← hde.2.2.1]
            have long_eq := @solver_equiv (List.map (fun x ↦ x.1) (a1 :: a2).reverse)
              (List.map (fun x ↦ x.1) (b1 :: b2)) (by simp) (by simp)
            apply SemiThue.trans _ _ _ _ long_eq
            convert SemiThue.refl (a1 :: a2 ++ b1 :: b2)
            · apply to_up_plain_no_bool
              have a_is : a1 :: a2 = (separate_first_pair (l1 :: l2)).1 := by simp [hs]
              rw [a_is]
              exact separate_first_pair_first_false _
            apply to_over_plain_no_bool
            have b_is : b1 :: b2 = (separate_first_pair (l1 :: l2)).2.1 := by simp [hs]
            rw [b_is]
            exact separate_first_pair_second_true _
          rw [← hfg.2.2.1]
          exact H2.2.2
        apply H7.trans
        rw [← List.append_assoc]
        apply SemiThue_center
        rw [← H6]
        exact H5
  termination_by L.length

def solver_g (L1 L2 : List (ℕ × Bool)) : Bool := by
  rcases (reverse_complex (L1 ++ (FreeGroup.invRev L2))).2.1 with ⟨d, e, hde⟩
  exact final_solver (List.map (fun x => x.1) e.reverse) (List.map (fun x => x.1) d)


-- lemma mul_inv_mem_of_mk_eq_mk {rels : Set (FreeGroup α)} {x y : FreeGroup α}
--   (h :  PresentedGroup.mk rels x = PresentedGroup.mk rels y) : x * y⁻¹ ∈ rels:= by
--   sorry
--   --eq_of_mul_inv_eq_one <| one_of_mem hx

theorem PresentedGroup.mk_mul : PresentedGroup.mk rels (a * b) =
  PresentedGroup.mk rels a * PresentedGroup.mk rels b := rfl

theorem SemiThue_reversing_to_braid_group_equiv (h : SemiThue reversing a b) :
  (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk a) =
  (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk b) := by
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
      exact Braid.braid_group_inf.braid h
  | trans a b c _ _ ih1 ih2 =>
    exact ih1.trans ih2

theorem to_over_plain_of (i : ℕ) : to_over_plain (FreeMonoid.of i) = [(i, true)] := by rfl

open Braid in
theorem bm_to_bg (h : PresentedMonoid.mk braid_rels_m_inf a =
  PresentedMonoid.mk braid_rels_m_inf b) :
  (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk (to_over_plain a)) =
  (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk (to_over_plain b)) := by
  apply PresentedMonoid.exact at h
  induction h with
  | of x y h =>
    cases h with
    | adjacent i => exact braid_group_inf.braid dist_succ
    | separated i j h =>
      apply braid_group_inf.comm
      apply or_dist_iff.mpr
      left; exact h
  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | mul _ _ ih1 ih2 =>
    rw [to_over_plain_mul, to_over_plain_mul, ← FreeGroup.mul_mk,  ← FreeGroup.mul_mk,
      PresentedGroup.mk_mul, PresentedGroup.mk_mul, ih1, ih2]

theorem PresentedGroup.mk_inv {rels : Set (FreeGroup α)} : (PresentedGroup.mk rels a)⁻¹ =
  (PresentedGroup.mk rels) a⁻¹ := by rfl

theorem pg_mk_fg_inv : ((PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk a))⁻¹ =
  (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk (FreeGroup.invRev a)) := by
  rw [PresentedGroup.mk_inv, FreeGroup.inv_mk]

theorem pg_mk_to_over_plain_inv :
  ((PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk (to_over_plain a)))⁻¹ =
  (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk (to_up_plain a)) := by
  rw [pg_mk_fg_inv]
  congr
  unfold to_over_plain to_up_plain FreeGroup.invRev
  simp

theorem to_up_plain_reverse : to_up_plain a.reverse = (to_up_plain a).reverse := by
  simp [to_up_plain]

theorem recover_from_is_false (h : is_false d) : to_up_plain (List.map (fun x ↦ x.1) d).reverse = (d : List (ℕ × Bool)) := by
  rw [to_up_plain_reverse]
  have H : (to_up_plain (List.map (fun x ↦ x.1) d)).reverse.reverse = d.reverse := by
    rw [List.reverse_reverse]
    induction d with
    | nil => simp [to_up_plain]
    | cons head tail ih =>
      have tf : is_false tail := (is_false_split h).2
      unfold to_up_plain at ih
      simp [to_up_plain, ih tf]
      have H2 := (is_false_split h).1
      specialize H2 head ⟨by simp⟩
      simp [← H2.1]
  exact List.reverse_injective H

theorem recover_from_is_true (h : is_true d) : to_over_plain (List.map (fun x ↦ x.1) d) = (d : List (ℕ × Bool)) := by
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

theorem solver_g_correct_one_direction : solver_g a b = true →
    (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk a) =
    (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk b) := by
  intro h
  unfold solver_g at h
  rcases dede : (reverse_complex (a ++ (FreeGroup.invRev b))).2.1 with ⟨d, e, hde⟩
  have H := correct_one_dir h
  have H2 := SemiThue_reversing_to_braid_group_equiv ((reverse_complex (a ++ (FreeGroup.invRev b))).2.2)
  rw [hde.2.2.1] at H2
  rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
    PresentedGroup.mk_mul, PresentedGroup.mk_mul] at H2
  have d_is : (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.fst = d := by aesop
  rw [d_is] at H
  have e_is : (reverse_complex (a ++ FreeGroup.invRev b)).2.1.2.1 = e := by
    rw [dede]
  rw [e_is] at H
  apply bm_to_bg at H
  apply (mul_right_inj ((PresentedGroup.mk Braid.braid_rels_coexeter)
    (FreeGroup.mk (to_over_plain (List.map (fun x ↦ x.1) e.reverse))))⁻¹).mpr at H
  simp at H
  rw [pg_mk_to_over_plain_inv, recover_from_is_true hde.1, recover_from_is_false hde.2.1] at H
  apply (mul_right_inj (((PresentedGroup.mk Braid.braid_rels_coexeter)
        (FreeGroup.mk e))⁻¹)).mpr at H
  apply (mul_left_inj ((PresentedGroup.mk Braid.braid_rels_coexeter)
        (FreeGroup.mk e))).mpr at H
  rw [mul_one, inv_mul_cancel, inv_mul_cancel_left] at H
  rw [← H] at H2
  apply (mul_left_inj ((PresentedGroup.mk Braid.braid_rels_coexeter)
    (FreeGroup.mk (FreeGroup.invRev b)))⁻¹).mpr at H2
  rw [mul_inv_cancel_right, one_mul] at H2
  rw [H2, PresentedGroup.mk_inv, FreeGroup.inv_mk, FreeGroup.invRev_invRev]

def invRev_true_of_is_false (h : is_false e) : is_true (FreeGroup.invRev e) := by
  intro a ⟨ha⟩
  unfold FreeGroup.invRev at ha
  constructor
  simp only [List.mem_reverse, List.mem_map, Prod.exists, Bool.exists_bool, Bool.not_false,
    Bool.not_true] at ha
  rcases ha with ⟨c, hc | hd⟩
  · simp [← hc.2]
  exfalso
  specialize h (c, true) ⟨hd.1⟩
  simp only [Bool.true_eq_false] at h
  exact h.1

theorem lift_of_group : (FreeMonoid.lift FreeGroup.of) (FreeMonoid.of i) = FreeGroup.of i := by rfl

theorem lift_of_group_two {a : FreeMonoid ℕ} : (FreeMonoid.lift FreeGroup.of) a =
  FreeGroup.mk (to_over_plain a) := by
  induction a using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of b a ih =>
    simp [to_over_plain_mul, ih, ← FreeGroup.mul_mk]
    change FreeGroup.of b = FreeGroup.mk [(b, true)]
    rfl

open FreeMonoid in
inductive braid_rels_m_inf_one_symm : FreeMonoid ℕ → FreeMonoid ℕ → Prop
  | adjacent (i j : ℕ) (h : i.dist j = 1) : braid_rels_m_inf_one_symm (of i * of j * of i) (of j * of i * of j)
  | separated (i j : ℕ) (h : i.dist j ≥ 2) : braid_rels_m_inf_one_symm (of i * of j) (of j * of i)
  | basic (i) : braid_rels_m_inf_one_symm (of i) (of i)

theorem connect_monoid_group_braid_rels : pm_rels_to_pg_rels braid_rels_m_inf_one_symm =
  Braid.braid_rels_coexeter := by
  unfold pm_rels_to_pg_rels
  ext
  rename_i y
  constructor
  · intro h
    simp at h
    rcases h with ⟨a, b, hbr, hl⟩
    rw [← hl, lift_of_group_two, lift_of_group_two]
    cases hbr with
    | adjacent i j hd =>
      simp only [to_over_plain_mul, ← FreeGroup.mul_mk]
      simp only [to_over_plain_of]
      unfold Braid.braid_rels_coexeter
      use (i, j)
      simp only [Function.uncurry_apply_pair, Braid.artin_tits_rel, Braid.M_braid_inf, dist_succ, Braid.alternate, hd]
      rfl
    | separated i j h =>
      simp only [to_over_plain_mul, ← FreeGroup.mul_mk]
      simp only [to_over_plain_of]
      unfold Braid.braid_rels_coexeter
      use (i, j)
      have H : ∃ n, i.dist (j) = Nat.succ (Nat.succ n) := by
        match hij : i.dist j with
        | 0 =>
          have : i = j := Nat.eq_of_dist_eq_zero hij
          omega
        | Nat.succ n1 =>
          match n1 with
          | 0 =>
            have H := or_dist_iff_eq.mp hij
            omega
          | Nat.succ n2 => use n2
      rcases H with ⟨n, hn⟩
      simp only [Function.uncurry_apply_pair, Braid.artin_tits_rel, Braid.M_braid_inf, hn, Braid.alternate]
      rfl
    | basic i =>
      rw [mul_inv_cancel (FreeGroup.mk (to_over_plain (FreeMonoid.of i)))]
      use (i, i)
      simp [Function.uncurry_apply_pair, Braid.artin_tits_rel, Braid.M_braid_inf, Braid.alternate]
  intro h
  simp only [Set.mem_setOf_eq, Prod.exists]
  unfold Braid.braid_rels_coexeter at h
  simp only [Set.mem_range, Prod.exists, Function.uncurry_apply_pair] at h
  rcases h with ⟨a, b, br⟩
  unfold Braid.artin_tits_rel at br
  unfold Braid.M_braid_inf at br
  cases hab : a.dist b with
  | zero =>
    simp [hab, Braid.alternate] at br
    rw [← br]
    use [27], [27]
    constructor
    · apply braid_rels_m_inf_one_symm.basic _
    simp
  | succ n =>
    cases hn : n with
    | zero =>
      simp [hn, hab, Braid.alternate] at br
      rw [← br]
      use [a, b, a], [b, a, b]
      constructor
      · rw [hn, zero_add] at hab
        exact braid_rels_m_inf_one_symm.adjacent _ _ hab
      rfl
    | succ n2 =>
      simp [hn, hab, Braid.alternate] at br
      rw [← br]
      use [a, b], [b, a]
      constructor
      · apply braid_rels_m_inf_one_symm.separated
        aesop
      rfl

open PresentedMonoid in
theorem one_symm_is_really_the_same : mk braid_rels_m_inf a = mk braid_rels_m_inf b ↔
  mk braid_rels_m_inf_one_symm a = mk braid_rels_m_inf_one_symm b := by
  constructor
  · intro h
    apply BraidMonoidInf.exact at h
    apply PresentedMonoid.sound
    induction h with
    | of x y h2 =>
      cases h2 with
      | adjacent i =>
        exact PresentedMonoid.rel_alone <| braid_rels_m_inf_one_symm.adjacent _ _ dist_succ
      | separated i j h =>
        apply PresentedMonoid.rel_alone
        apply braid_rels_m_inf_one_symm.separated
        apply or_dist_iff.mpr
        left; exact h
    | refl x => exact PresentedMonoid.refl
    | symm _ ih => exact swap ih
    | trans _ _ ih1 ih2 => exact PresentedMonoid.trans ih1 ih2
    | mul _ _ ih1 ih2 => exact mul ih1 ih2
  intro h
  apply PresentedMonoid.exact at h
  apply PresentedMonoid.sound
  induction h with
  | of x y h =>
    cases h with
    | adjacent i j h =>
      apply or_dist_iff_eq.mp at h
      rcases h with h | h
      · rw [← h]
        exact rel_alone <| braid_rels_m_inf.adjacent i
      apply swap
      apply rel_alone
      rw [← h]
      exact braid_rels_m_inf.adjacent j
    | separated i j h =>
      apply or_dist_iff.mp at h
      rcases h with h | h
      · exact rel_alone <| braid_rels_m_inf.separated _ _ h
      exact swap <| rel_alone <| braid_rels_m_inf.separated _ _ h
    | basic i => exact BraidMonoidInf.exact rfl
  | refl x => exact BraidMonoidInf.exact rfl
  | symm _ ih => exact swap ih
  | trans _ _ ih1 ih2 => exact PresentedMonoid.trans ih1 ih2
  | mul _ _ ih1 ih2 => exact mul ih1 ih2

variable {rels : FreeMonoid ℕ → FreeMonoid ℕ → Prop} {h : IsRightCancelMul (PresentedMonoid rels)} {h1 : IsCommonLeftMultipleMul (PresentedMonoid rels)}

theorem pml_to_presented_group_apply_mk (a : FreeMonoid ℕ) : pml_to_presented_group
    (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ rels h1 h)
    (PresentedMonoid.mk rels a)) =
    (PresentedGroup.mk (pm_rels_to_pg_rels rels) (FreeGroup.mk (to_over_plain a)) :
    PresentedGroup (pm_rels_to_pg_rels rels)) := by
  induction a using FreeMonoid.inductionOn'
  · rfl
  rename_i head tail ih
  simp [ih, to_over_plain_mul, ← FreeGroup.mul_mk]
  rfl

variable {h : IsRightCancelMul (PresentedMonoid braid_rels_m_inf)} {h1 : IsCommonLeftMultipleMul (PresentedMonoid braid_rels_m_inf)}

theorem  pml_to_presented_group_injective {α : Type} {rels : FreeMonoid α → FreeMonoid α → Prop}
  {h : IsRightCancelMul (PresentedMonoid rels)} {h1 : IsCommonLeftMultipleMul (PresentedMonoid rels)} :
  Function.Injective (pml_to_presented_group : pml h1 h →*
    PresentedGroup (pm_rels_to_pg_rels rels)) := by
  apply Function.HasLeftInverse.injective
  use presented_group_to_pml
  exact Function.leftInverse_iff_comp.mpr <| comp_eq_of_hom_comp_eq comp_pg_pml_pml_pg_eq_id

-- theorem OreLocalization.numeratorHom_inj : Function.Injective (OreLocalization.numeratorHom) := by
--   apply?

theorem right_cancel_extends [h2 : IsRightCancelMul (PresentedMonoid braid_rels_m_inf)] :
  IsRightCancelMul (PresentedMonoid braid_rels_m_inf_one_symm) where
  mul_right_cancel := by
    intro a b c h
    rcases Quotient.exists_rep a with ⟨a1, ha1⟩
    rcases Quotient.exists_rep b with ⟨b1, hb1⟩
    rcases Quotient.exists_rep c with ⟨c1, hc1⟩
    rw [← ha1, ← hb1, ← hc1] at h
    change ⟦a1 * b1⟧ = ⟦c1 * b1⟧ at h
    apply one_symm_is_really_the_same.mpr at h
    rw [PresentedMonoid.mul_mk, PresentedMonoid.mul_mk, mul_left_inj] at h
    rw [← ha1, ← hc1]
    exact one_symm_is_really_the_same.mp h

theorem left_cancel_extends [h2 : IsLeftCancelMul (PresentedMonoid braid_rels_m_inf)] :
  IsLeftCancelMul (PresentedMonoid braid_rels_m_inf_one_symm) where
  mul_left_cancel := by
    intro a b c h
    rcases Quotient.exists_rep a with ⟨a1, ha1⟩
    rcases Quotient.exists_rep b with ⟨b1, hb1⟩
    rcases Quotient.exists_rep c with ⟨c1, hc1⟩
    rw [← ha1, ← hb1, ← hc1] at h
    change ⟦a1 * b1⟧ = ⟦a1 * c1⟧ at h
    apply one_symm_is_really_the_same.mpr at h
    rw [PresentedMonoid.mul_mk, PresentedMonoid.mul_mk, mul_right_inj] at h
    rw [← hb1, ← hc1]
    exact one_symm_is_really_the_same.mp h

theorem fm_lift_pm_of_eq_pm_mk : (FreeMonoid.lift (PresentedMonoid.of rels)) a =
    PresentedMonoid.mk rels a := by
  induction a using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of b a ih =>
    simp [ih]
    rfl

noncomputable def map_to_one_symm : (PresentedMonoid braid_rels_m_inf) →*
  PresentedMonoid braid_rels_m_inf_one_symm := by
  apply PresentedMonoid.lift_hom (PresentedMonoid.of braid_rels_m_inf_one_symm)
  intro a b cg
  apply PresentedMonoid.sound at cg
  apply one_symm_is_really_the_same.mp at cg
  rw [fm_lift_pm_of_eq_pm_mk, fm_lift_pm_of_eq_pm_mk]
  exact cg

noncomputable def map_from_one_symm : (PresentedMonoid braid_rels_m_inf_one_symm) →*
  PresentedMonoid braid_rels_m_inf := by
  apply PresentedMonoid.lift_hom (PresentedMonoid.of braid_rels_m_inf)
  intro a b cg
  apply PresentedMonoid.sound at cg
  apply one_symm_is_really_the_same.mpr at cg
  rw [fm_lift_pm_of_eq_pm_mk, fm_lift_pm_of_eq_pm_mk]
  exact cg

noncomputable def one_symm_type_iso_me : (PresentedMonoid braid_rels_m_inf_one_symm) ≃*
  PresentedMonoid braid_rels_m_inf := by
  refine MonoidHom.toMulEquiv map_from_one_symm map_to_one_symm ?_ ?_
  exact PresentedMonoid.ext_iff.mpr (congrFun rfl)
  exact PresentedMonoid.ext_iff.mpr (congrFun rfl)

noncomputable def left_multiple_iso [Mul A] [Mul B] [h2 : IsCommonLeftMultipleMul A] (e : A ≃* B) :
  IsCommonLeftMultipleMul B where
  common_left_multiple := by
    intro a b
    have := (h2.common_left_multiple (e.symm a) (e.symm b))
    rcases this with ⟨c, d, hcd⟩
    apply congr_arg e at hcd
    simp at hcd
    use e c, e d

theorem pg_to_pm_fg_mk {h2 : IsRightCancelMul (PresentedMonoid braid_rels_m_inf)}
  {h3 : IsCommonLeftMultipleMul (PresentedMonoid braid_rels_m_inf)}
  (h : PresentedGroup.mk Braid.braid_rels_coexeter (FreeGroup.mk e) =
  (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk d)) (he : is_true e) (hd : is_true d) :
  PresentedMonoid.mk braid_rels_m_inf (List.map (fun x ↦ x.1) e) =
  PresentedMonoid.mk braid_rels_m_inf (List.map (fun x ↦ x.1) d) := by
  have he1 : e = to_over_plain (List.map (fun x ↦ x.1) e) := by
    exact (recover_from_is_true he).symm
  have hd1 : d = to_over_plain (List.map (fun x ↦ x.1) d) := by
    exact (recover_from_is_true hd).symm
  rw [he1, hd1, ← connect_monoid_group_braid_rels] at h
  --rw [← pml_to_presented_group_apply_mk] at h
  --insane errors when i try this twice
  have h5 : IsCommonLeftMultipleMul (PresentedMonoid braid_rels_m_inf_one_symm) :=
    left_multiple_iso one_symm_type_iso_me.symm
  have h4 : IsRightCancelMul (PresentedMonoid braid_rels_m_inf_one_symm) := right_cancel_extends
  have Hd2 : pml_to_presented_group
    (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ braid_rels_m_inf_one_symm h5 (right_cancel_extends))
    (PresentedMonoid.mk braid_rels_m_inf_one_symm (List.map (fun x ↦ x.1) d))) =
    (PresentedGroup.mk (pm_rels_to_pg_rels braid_rels_m_inf_one_symm)
    (FreeGroup.mk (to_over_plain (List.map (fun x ↦ x.1) d)))) := pml_to_presented_group_apply_mk (List.map (fun x ↦ x.1) d)
  have he1 : pml_to_presented_group
    (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ braid_rels_m_inf_one_symm h5 (right_cancel_extends))
    (PresentedMonoid.mk braid_rels_m_inf_one_symm (List.map (fun x ↦ x.1) e))) =
    (PresentedGroup.mk (pm_rels_to_pg_rels braid_rels_m_inf_one_symm)
    (FreeGroup.mk (to_over_plain (List.map (fun x ↦ x.1) e)))) := pml_to_presented_group_apply_mk (List.map (fun x ↦ x.1) e)
  have HTHREE : pml_to_presented_group
    (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ braid_rels_m_inf_one_symm h5 (right_cancel_extends))
    (PresentedMonoid.mk braid_rels_m_inf_one_symm (List.map (fun x ↦ x.1) d))) = pml_to_presented_group
    (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ braid_rels_m_inf_one_symm h5 h4)
    (PresentedMonoid.mk braid_rels_m_inf_one_symm (List.map (fun x ↦ x.1) e))) := by
    rw [Hd2, he1]
    exact h.symm
  have H := pml_to_presented_group_injective HTHREE
  have H5 : Function.Injective (@OreLocalization.numeratorHom
    (PresentedMonoid braid_rels_m_inf_one_symm)
    (PresentedMonoid.instMonoid braid_rels_m_inf_one_symm) ⊤
    oreSetSelf' : PresentedMonoid braid_rels_m_inf_one_symm →*
    @OreLocalization _ _ ⊤ (@oreSetSelf' _ braid_rels_m_inf_one_symm h5 h4)
    (PresentedMonoid braid_rels_m_inf_one_symm) _) := by
    intro x y hxy
    unfold OreLocalization.numeratorHom at hxy
    change @OreLocalization.oreDiv _ _ _ (@oreSetSelf' _ braid_rels_m_inf_one_symm h5 h4) _ _ x 1 =
      @OreLocalization.oreDiv _ _ _ (@oreSetSelf' _ braid_rels_m_inf_one_symm h5 h4) _ _ y 1 at hxy
    unfold OreLocalization.oreDiv at hxy
    unfold Quotient.mk' at hxy
    have H := Quotient.exact hxy
    rcases H with ⟨a, b, hab⟩
    simp at hab
    have another := hab.1
    rw [← hab.2] at another
    apply mul_left_cancel at another
    exact another.symm
    --this is strange, somehow something feels backwards. in my case it's fine, but check into this
    have H : IsLeftCancelMul (PresentedMonoid braid_rels_m_inf) := by
      have H1 : IsCancelMul (PresentedMonoid braid_rels_m_inf) :=
        CancelMonoid.toIsCancelMul (PresentedMonoid braid_rels_m_inf)
      exact IsCancelMul.toIsLeftCancelMul
    apply left_cancel_extends
  exact one_symm_is_really_the_same.mpr (H5 H.symm)

theorem invRev_remove_eq_reverse {e : List (α × Bool)} :
  (List.map (fun x ↦ x.1) e).reverse =
  (List.map ((fun x ↦ x.1) ∘ fun g ↦ (g.1, !g.2)) e).reverse := by simp

theorem solver_g_correct_other_direction :
    (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk a) =
    (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk b) →
    solver_g a b = true := by
  intro h
  unfold solver_g
  apply correct_other_dir
  rcases dede : (reverse_complex (a ++ (FreeGroup.invRev b))).2.1 with ⟨d, e, hde⟩
  have d_is : (reverse_complex (a ++ FreeGroup.invRev b)).snd.1.fst = d := by aesop
  have e_is : (reverse_complex (a ++ FreeGroup.invRev b)).2.1.2.1 = e := by
    rw [dede]
  rw [d_is, e_is]
  have H2 := SemiThue_reversing_to_braid_group_equiv ((reverse_complex (a ++ (FreeGroup.invRev b))).2.2)
  rw [hde.2.2.1, ← FreeGroup.mul_mk, PresentedGroup.mk_mul, h, ← FreeGroup.inv_mk,
    ← PresentedGroup.mk_inv, mul_inv_cancel, ← FreeGroup.mul_mk, PresentedGroup.mk_mul] at H2
  apply (mul_left_inj ((PresentedGroup.mk Braid.braid_rels_coexeter)
    (FreeGroup.mk e))⁻¹).mpr at H2
  rw [one_mul, mul_inv_cancel_right, PresentedGroup.mk_inv, FreeGroup.inv_mk] at H2
  apply pg_to_pm_fg_mk at H2
  specialize H2 (invRev_true_of_is_false hde.2.1) hde.1
  rw [← H2]
  congr 1
  simp [FreeGroup.invRev, invRev_remove_eq_reverse]
  exact RightCancelSemigroup.toIsRightCancelMul (PresentedMonoid braid_rels_m_inf)
  exact ⟨common_left_mul_inf⟩

theorem solver_g_correct : solver_g a b ↔
  PresentedGroup.mk Braid.braid_rels_coexeter (FreeGroup.mk a) =
  PresentedGroup.mk Braid.braid_rels_coexeter (FreeGroup.mk b) := by
  constructor
  · exact solver_g_correct_one_direction
  exact solver_g_correct_other_direction

-- theorem solver_g_correct_cons {a b : (PresentedGroup Braid.braid_rels_coexeter) } :
--   solver_g (Classical.choose (Quot.exists_rep (Classical.choose (Quotient.exists_rep a))))
--     (Classical.choose (Quot.exists_rep (Classical.choose (Quotient.exists_rep b)))) ↔
--   a = b := by
--   have Ha' := (Classical.choose_spec (Quot.exists_rep (Classical.choose (Quotient.exists_rep a))))
--   have Hb' := (Classical.choose_spec (Quot.exists_rep (Classical.choose (Quotient.exists_rep b))))
--   have Ha'' := (Classical.choose_spec (Quotient.exists_rep a))
--   have Hb'' := (Classical.choose_spec (Quotient.exists_rep b))
--   constructor
--   · intro it
--     rw [← Ha'', ← Hb'']
--     rw [← Ha', ← Hb']
--     exact solver_g_correct_one_direction it
--   intro it
--   rw [← Ha'', ← Hb''] at it
--   rw [← Ha', ← Hb'] at it
--   exact solver_g_correct_other_direction it --sorry --exact solver_g_correct_other_direction

--start with elements of the free group
def solver_fg (a b : FreeGroup ℕ) : Bool := by
  apply @Quot.lift₂ _ _ _ FreeGroup.Red.Step FreeGroup.Red.Step solver_g _ _ a b
  · intro a1 b1 c1 relsy
    have HAC := Quot.sound relsy
    change FreeGroup.mk _ = FreeGroup.mk _ at HAC
    cases hi : solver_g a1 b1
    · symm
      apply eq_false_of_ne_true
      intro h1
      apply solver_g_correct_one_direction at h1
      rw [← HAC] at h1
      apply solver_g_correct_other_direction at h1
      aesop
    apply solver_g_correct.1 at hi
    symm
    apply solver_g_correct_other_direction
    rw [← HAC, hi]
  intro a1 b1 c1 relsy
  have HBC := Quot.sound relsy
  change FreeGroup.mk _ = FreeGroup.mk _ at HBC
  cases hi : solver_g a1 c1
  · symm
    apply eq_false_of_ne_true
    intro h1
    apply solver_g_correct_one_direction at h1
    rw [← HBC] at h1
    apply solver_g_correct_other_direction at h1
    aesop
  apply solver_g_correct.1 at hi
  symm
  apply solver_g_correct_other_direction
  rw [← HBC, hi]

theorem solver_fg_correct : solver_fg a b ↔
    PresentedGroup.mk Braid.braid_rels_coexeter a =
    PresentedGroup.mk Braid.braid_rels_coexeter b := by
  rcases Quot.exists_rep a with ⟨a, rfl⟩
  rcases Quot.exists_rep b with ⟨b, rfl⟩
  exact solver_g_correct

def braid_solver (a b : PresentedGroup Braid.braid_rels_coexeter) : Bool := by
  apply Quotient.lift₂ solver_fg _ a b
  intro a b c d hac hbd
  have HAC := Quotient.sound hac
  change (PresentedGroup.mk Braid.braid_rels_coexeter) a = (PresentedGroup.mk Braid.braid_rels_coexeter) c at HAC
  have HBD := Quotient.sound hbd
  change (PresentedGroup.mk Braid.braid_rels_coexeter) b = (PresentedGroup.mk Braid.braid_rels_coexeter) d at HBD
  cases hi : solver_fg a b
  · symm
    apply eq_false_of_ne_true
    intro h1
    apply solver_fg_correct.1 at h1
    rw [← HAC, ← HBD] at h1
    apply solver_fg_correct.2 at h1
    aesop
  apply solver_fg_correct.1 at hi
  symm
  apply solver_fg_correct.2
  aesop

theorem braid_solver_correct {a b : PresentedGroup Braid.braid_rels_coexeter} : braid_solver a b ↔ a = b := by
  rcases Quotient.exists_rep a with ⟨a, rfl⟩
  rcases Quotient.exists_rep b with ⟨b, rfl⟩
  exact solver_fg_correct


instance braid_decidable_helper :
    DecidableEq (PresentedGroup Braid.braid_rels_coexeter) := by
  intro a b
  by_cases h : braid_solver a b = true
  · exact isTrue (braid_solver_correct.mp h)
  · exact isFalse (by
      intro hEq
      apply braid_solver_correct.mpr at hEq
      aesop)

def solver_nonsense (a b : PresentedGroup Braid.braid_rels_coexeter) : Bool := a = b


open Braid in
#eval braid_solver ((σi 1 * σi 2 * σi 1)) ((σi 2 * σi 1 * σi 2))

open Braid in
#eval solver_nonsense ((σi 1 * σi 2 * σi 1)) ((σi 2 * σi 3 * σi 2))

#eval solver_g [(1, true), (2, true), (4, true), (1, true)]
  [(2, true), (1, true), (2, true), (4, true)]

#show_braid_word_help ([[(3, true), (2, true), (0, false), (3, true)],
  [(3, true), (2, true), (3, true), (0, false)],
  [(2, true), (3, true), (2, true), (0, false)]] : List (List ((ℕ × Bool))))

def foo1 := (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true)]).1

#show_braid_word_help ([foo1,
  [(3, true), (2, true), (3, true), (0, false)],
  [(2, true), (3, true), (2, true), (0, false)]] : List (List ((ℕ × Bool))))

#eval (reverse_complex [(3, false), (1, true), (2, true), (1, true)]).1
#show_braid_word_help ([(reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1, []] : List (List (ℕ × Bool)))
#eval (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1
#eval (reverse_complex [(3, false), (2, true), (2, true), (1, true)]).1.length
#eval (reverse_complex [(2, false), (2, false), (1, false), (1, false), (2, true), (2, true), (1, true), (1, true)]).1.length
#eval (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (4, true), (4, true)]).1.length
#eval (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1.length

#eval (reverse_complex [(0, false), (0, false), (1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1

#eval (reverse_complex [(1, false), (2, false), (2, false), (3, true), (4, true)]).1.length

-- set_option pp.proofs true in
-- def Quotient.exists_rep_C (a : Quotient new_rels) :
--   Σ b, PLift (Quotient.mk new_rels b = a) := by
--   --apply @Quotient.ind _ _ (fun x => Σ b, PLift (Quotient.mk new_rels b = x))
--   apply @Quot.hrecOn _ _ (fun x => Σ b, PLift (Quotient.mk new_rels b = x))
--      a (fun c => by use c; constructor; rfl)
--   intro a b hab
--   have H := Quotient.sound hab

--   -- unfold HEq
--   -- simp [H]
--   sorry



-- #check Quot.rec
-- noncomputable def braid_solver (a b : Braid.braid_group_inf) : Bool := by
--   rcases Quotient.exists_rep_C a with ⟨a1, ⟨ha1⟩⟩
--   rcases Quotient.exists_rep_C b with ⟨b1, ⟨hb1⟩⟩
--   sorry



  -- have hb := Classical.choose (Quotient.exists_rep b)
  -- have ha1 := Classical.choose (Quot.exists_rep ha)
  -- have hb1 := Classical.choose (Quot.exists_rep hb)
  -- exact solver_g ha1 hb1


#check Classical.choose
