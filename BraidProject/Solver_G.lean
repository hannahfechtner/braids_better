import BraidProject.Solver_C
import BraidProject.BraidGroup

-- def solver_long (a b) (ha : List.length a > 0) (hb : List.length b > 0) :=
--   solver_helper' ⟨a, ⟨b, ⟨to_up_plain a ++ to_over_plain b, by simp [to_up_plain, to_over_plain]; exact ⟨⟨ha, hb⟩, by apply SemiThue.refl _ ⟩⟩⟩⟩


-- def solver_equiv (ha : List.length a > 0) (hb : List.length b > 0)  : SemiThue reversing
--     (to_up_plain a ++ to_over_plain b) (solver_long a b ha hb).1.2.2.1 := by
--   have H := (solver_long a b ha hb).1.2.2.2.2
--   simp at H
--   convert H
--   exact (solver_long a b ha hb).2.1.symm
--   exact (solver_long a b ha hb).2.2.symm

def separate_maximal_true_prefix (c : List (ℕ × Bool)) : List (ℕ × Bool) × List (ℕ × Bool) :=
  match c with
  | [] => ([], [])
  | (c2, false) :: c1 => ([], (c2, false) :: c1)
  | (d, true) :: e => ([(d, true)] ++ (separate_maximal_true_prefix e).1, (separate_maximal_true_prefix e).2)

-- theorem separate_maximal_true_prefix_nil : separate_maximal_true_prefix [] = ([], []) := by
--   unfold separate_maximal_true_prefix
--   simp
-- theorem separate_maximal_true_prefix_cons_false (d : Option ℕ) (e : List (Option ℕ × Bool)) :
--   separate_maximal_true_prefix ((d, false) :: e) = ([], (d, false) :: e) := by
--   unfold separate_maximal_true_prefix
--   simp

theorem separate_maximal_true_prefix_correct :
    (separate_maximal_true_prefix L).1 ++ (separate_maximal_true_prefix L).2 = L := by
  induction L with
  | nil => simp [separate_maximal_true_prefix]
  | cons d e ih =>
    match d with
    | (d1, false) =>
      simp [separate_maximal_true_prefix, ih]
    | (d2, true) =>
      simp [separate_maximal_true_prefix, ih]

def separate_maximal_true_prefix_is_true : is_true (separate_maximal_true_prefix L).1 := by
  induction L with
  | nil =>
    simp [separate_maximal_true_prefix]
    exact is_true_nil
  | cons d e =>
    match d with
    | (d1, false) =>
      simp [separate_maximal_true_prefix]
      exact is_true_nil
    | (d2, true) =>
      simp [separate_maximal_true_prefix]
      apply is_true_cons
      assumption

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
  rcases (reverse_complex (L1 ++ (bool_swap L2.reverse))).2.1 with ⟨d, e, hde⟩
  exact final_solver (List.map (fun x => x.1) e) (List.map (fun x => x.1) d)


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
      rename_i n
      change (PresentedGroup.mk Braid.braid_rels_coexeter)
        (FreeGroup.mk ([(n, false)] ++ [(n, true)])) = _
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

theorem solver_g_correct_one_direction :
  solver_g a b = true →
  (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk a) =
    (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk b) := by
  intro h
  unfold solver_g at h
  rcases dede : (reverse_complex (a ++ (bool_swap b.reverse))).2.1 with ⟨d, e, hde⟩
  have H := correct_one_dir h
  have H2 := SemiThue_reversing_to_braid_group_equiv ((reverse_complex (a ++ (bool_swap b.reverse))).2.2)
  rw [hde.2.2.1] at H2
  rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
    PresentedGroup.mk_mul, PresentedGroup.mk_mul] at H2
  have d_is : (reverse_complex (a ++ bool_swap b.reverse)).snd.1.fst = d := by aesop
  rw [d_is] at H
  have e_is : (reverse_complex (a ++ bool_swap b.reverse)).2.1.2.1 = e := by
    rw [dede]
  rw [e_is] at H
  



  sorry
#check PresentedGroup.mk
theorem solver_g_correct_other_direction :
    (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk a) =
    (PresentedGroup.mk Braid.braid_rels_coexeter) (FreeGroup.mk b) →
    solver_g a b = true := by
  intro h
  unfold solver_g
  apply correct_other_dir



  sorry

theorem solver_g_correct : solver_g a b ↔
  PresentedGroup.mk Braid.braid_rels_coexeter (FreeGroup.mk a) =
  PresentedGroup.mk Braid.braid_rels_coexeter (FreeGroup.mk b) := by
  constructor
  · exact solver_g_correct_one_direction
  exact solver_g_correct_other_direction

--#eval! (reverse_complex [(1, true), (2, false), (3, true), (4, false)]).1
-- def reverse_complex_comp (L : List (ℕ × Bool)) : (L1 : List (ℕ × Bool)) × in_order L1 :=
--   match L with
--   | [] => by
--     use []
--     exact in_order_nil
--   | l1 :: l2 =>
--   match hs : separate_first_pair (l1 :: l2) with
--   | ([], (b, c)) => by
--     have hc : c.length < (l1 :: l2).length := by
--       have H := separate_first_pair_correct (l1 :: l2)
--       have c_is : c = (separate_first_pair (l1 :: l2)).2.2 := by simp [hs]
--       rw [c_is]
--       apply congr_arg List.length at H
--       simp only [List.append_assoc, List.length_append, List.length_cons] at H
--       rw [List.length_cons, ← H, ← add_assoc]
--       refine Nat.lt_add_of_pos_left ?_
--       apply separate_first_pair_length ?_
--       simp
--     use (b++ (reverse_complex_comp c).1)
--     have H : is_true b := by
--       have H : b = (separate_first_pair (l1 :: l2)).2.1 := by simp [hs]
--       rw [H]
--       apply separate_first_pair_second_true
--     rcases (reverse_complex_comp c).2 with ⟨d, e, hde⟩
--     use b++d, e
--     constructor
--     · apply is_true_of_true_true H hde.1
--     constructor
--     · exact hde.2.1
--     constructor
--     rw [hde.2.2.1]
--     simp
--   | (a1::a2, ([], c)) => by
--     use a1 :: a2
--     have af : is_false (a1 :: a2) := by
--       have H : a1 :: a2 = (separate_first_pair (l1 :: l2)).1 := by simp [hs]
--       rw [H]
--       apply separate_first_pair_first_false
--     exact in_order_of_false af
--   | (a1::a2, (b1::b2, c)) => by
--     have H := solver_long (List.map (fun x => x.1) (a1 :: a2).reverse)
--       (List.map (fun x => x.1) (b1 :: b2)) (by simp) (by simp)
--     have H1 : in_order _ := solver_long_in_order (List.map (fun x => x.1) (a1 :: a2).reverse)
--       (List.map (fun x => x.1) (b1 :: b2)) (by simp) (by simp)
--     rcases H1 with ⟨d, e, hde⟩
--     have hc : c.length < (l1 :: l2).length := by
--       have H := separate_first_pair_correct (l1 :: l2)
--       have c_is : c = (separate_first_pair (l1 :: l2)).2.2 := by simp [hs]
--       rw [c_is]
--       apply congr_arg List.length at H
--       simp only [List.append_assoc, List.length_append, List.length_cons] at H
--       rw [List.length_cons, ← H, ← add_assoc]
--       refine Nat.lt_add_of_pos_left ?_
--       apply separate_first_pair_length ?_
--       simp
--     have H2 := reverse_complex_comp c
--     rcases H2.2 with ⟨f, g, hfg⟩
--     match e with
--     | [] =>
--       use d++f++g
--       use (d ++ f), g
--       constructor
--       · apply is_true_of_true_true hde.1 hfg.1
--       constructor
--       · exact hfg.2.1
--       constructor
--       rfl
--     | e1 :: e2 =>
--       match f with
--       | [] =>
--         use d ++ (e1 :: e2) ++ g
--         use d, (e1::e2) ++ g
--         constructor
--         · exact hde.1
--         constructor
--         · apply is_false_of_false_false hde.2.1 hfg.2.1
--         constructor
--         simp
--       | f1 :: f2 =>
--         have H3 := solver_long (List.map (fun x => x.1) (e1 :: e2).reverse)
--           (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)
--         have H4 : in_order _ := solver_long_in_order (List.map (fun x => x.1) (e1 :: e2).reverse)
--           (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)
--         rcases H4 with ⟨i, j, hij⟩
--         use d ++ i ++ j ++ g
--         use (d ++ i), j ++ g
--         constructor
--         · apply is_true_of_true_true hde.1 hij.1
--         constructor
--         · apply is_false_of_false_false hij.2.1 hfg.2.1
--         constructor
--         simp
--   termination_by L.length

-- theorem reverse_complex_comp_equiv_reg : (reverse_complex L).1 = (reverse_complex_comp L).1 := by
--   induction hl : L.length
--   · have H : L = [] := List.eq_nil_iff_length_eq_zero.mpr hl
--     rw [H]
--     simp [reverse_complex, reverse_complex_comp]
--   unfold reverse_complex reverse_complex_comp
--   split
--   · simp
--   split
--   · simp
--     sorry
--   · simp
--   simp only [List.map_cons, List.length_cons, eq_mpr_eq_cast, List.cons_append, cast_eq, cast_cast,
--     List.nil_append]

--   sorry

-- theorem reverse_complex_comp_equiv_reg' : (reverse_complex L).1 = (reverse_complex_comp L).1 := by
--   induction hl : L.length using Nat.strongRecOn generalizing L
--   unfold reverse_complex reverse_complex_comp
--   split
--   · simp
--   split
--   · rename_i b c se
--     simp
--     rename_i n ih l1 l2 L'
--     match b with
--     | [] =>
--       have H : c = [] := by apply separate_first_pair_nil_nil se
--       rw [H]
--       simp [reverse_complex, reverse_complex_comp]
--     | b1 :: b2 =>
--       have H := separate_first_pair_correct (l2 :: L')
--       have H : l2 :: L' = b1 :: b2 ++ c := by simp_all
--       apply congr_arg List.length at H
--       simp at H
--       simp at hl
--       have H : c.length < n := by omega
--       exact ih c.length H rfl
--   · simp
--   simp
--   sorry

-- noncomputable def reverse_complex_equiv : SemiThue reversing L (reverse_complex L).1 := by
--   exact (reverse_complex L).2.2


-- def get_maximal_false_suffix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) := by
--   cases c using List.reverseRecOn with
--   | nil => exact []
--   | append_singleton l a _ =>
--     match a with
--     | (_, true) => exact []
--     | (d, false) => exact get_maximal_false_suffix l ++ [(d, false)]
--   termination_by c.length

-- def remove_maximal_true_prefix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
--   match c with
--   | [] => []
--   | (d, false) :: e => (d, false) :: e
--   | (_, true) :: e => remove_maximal_true_prefix e

-- def remove_maximal_false_suffix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) := by
--   cases c using List.reverseRecOn with
--   | nil => exact []
--   | append_singleton l a _ =>
--     match a with
--     | (d, true) => exact l ++ [(d, true)]
--     | (d, false) => exact remove_maximal_false_suffix l
--   termination_by c.length

-- theorem remove_maximal_false_suffix_nil : remove_maximal_false_suffix [] = [] := by
--   unfold remove_maximal_false_suffix
--   simp

-- theorem remove_maximal_false_suffix_append_false :
--   remove_maximal_false_suffix (a ++ [(b, false)]) = remove_maximal_false_suffix a := by
--   unfold remove_maximal_false_suffix
--   simp
--   exact remove_maximal_false_suffix.eq_def a

-- theorem get_maximal_false_suffix_append_false : get_maximal_false_suffix (a ++ [(b, false)]) =
--   get_maximal_false_suffix a ++ [(b, false)] := by
--   unfold get_maximal_false_suffix
--   simp
--   exact get_maximal_false_suffix.eq_def a


-- def pgf_get_bottom (h : pgf a b c) := get_maximal_true_prefix c

-- def pgf_get_right (h : pgf a b c) := get_maximal_false_suffix c

-- def pgf_get_middle (h : pgf a b c) :=
--   remove_maximal_true_prefix (remove_maximal_false_suffix c)

-- theorem get_prefix_append_remove_prefix : get_maximal_true_prefix a ++ remove_maximal_true_prefix a = a := by
--   induction a with
--   | nil => simp [get_maximal_true_prefix, remove_maximal_true_prefix]
--   | cons d e ih =>
--     match d with
--     | (d1, false) =>
--       simp [get_maximal_true_prefix, remove_maximal_true_prefix, ih]
--     | (d2, true) =>
--       simp [get_maximal_true_prefix, remove_maximal_true_prefix, ih]

-- theorem remove_suffix_append_get_suffix : remove_maximal_false_suffix a ++ get_maximal_false_suffix a = a := by
--   induction a using List.reverseRecOn with
--   | nil => unfold remove_maximal_false_suffix get_maximal_false_suffix; simp
--   | append_singleton l d ih =>
--     match d with
--     | (d1, true) =>
--       unfold remove_maximal_false_suffix get_maximal_false_suffix; simp [ih]
--     | (d2, false) =>
--       rw [remove_maximal_false_suffix_append_false, get_maximal_false_suffix_append_false, ← List.append_assoc, ih]

-- theorem pgf_split_bottom_middle_right (h : pgf a b c) :
--   pgf_get_bottom h ++ pgf_get_middle h ++ pgf_get_right h = c := by
--   unfold pgf_get_bottom pgf_get_middle pgf_get_right
--   sorry
