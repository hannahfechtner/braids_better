import BraidProject.StepTwo_C_basic_eq
import BraidProject.SemiThue_C
import BraidProject.Cancellability
import BraidProject.GridsTwo_C
import BraidProject.PartialGrid_bounded
import BraidProject.PartialGrid_rw
import BraidProject.pgf_def

def find_it (L : List (ℕ × Bool)) :
    Option (List (ℕ × Bool) × ((ℕ) × (ℕ)) × List (ℕ × Bool)) :=
  match L with
  | [] => none
  | _ :: [] => none
  | (a, false) :: (b, true) :: tail =>
    some ([], (a, b), tail)
  | head :: tail =>
    match find_it tail with
    | none => none
    | some (c, e, f) =>
      some (head :: c, e, f)

@[simp]
theorem find_it_nil : find_it [] = none := by simp [find_it]

@[simp]
theorem find_it_singleton : find_it [a] = none := by
  unfold find_it; simp


theorem find_it_cons_none (h : find_it (a :: b) = none) : find_it b = none := by
  induction b with
  | nil => simp
  | cons head tail ih =>
    unfold find_it at h
    rcases a with ⟨a1, a2⟩
    rcases head with ⟨h3, h4⟩
    cases a2 with
    | false =>
      cases h4 with
      | true => simp at h
      | false =>
        simp at h
        cases ha : find_it ((h3, false) :: tail) with
        | none => rfl
        | some a => simp [ha] at h
    | true =>
      simp at h
      cases ha : find_it ((h3, h4) :: tail) with
      | none => rfl
      | some a => simp [ha] at h

theorem find_it_none_cons_true_iff : find_it tail = none ↔ find_it ((a, true) :: tail) = none := by
  constructor
  · intro h
    cases tail with
    | nil => simp [find_it]
    | cons head tail => simp [h, find_it]
  intro h
  exact find_it_cons_none h

@[simp]
theorem find_it_some_cons_true (h : find_it tail = some ⟨a, b, c⟩) :
    find_it ((d, true) :: tail) = some ⟨(d, true):: a, b, c⟩ := by
  conv => lhs; unfold find_it
  cases tail with
  | nil => simp at h
  | cons headt tailt => simp [h]

theorem find_it_first_empty (h : find_it a = some ([], d, e)) : ∃ a1 a2, a = (a1, false) :: a2 := by
  induction a with
  | nil => simp [find_it] at h
  | cons head tail ih =>
    rcases head with ⟨h1, t1⟩
    cases t1 with
    | false => use h1, tail
    | true =>
      cases tail with
      | nil => simp [find_it] at h
      | cons head1 tail1 =>
        rcases head1 with ⟨h2, t2⟩
        simp [find_it] at h
        cases hf : find_it ((h2, t2) :: tail1) with
        | none => simp [hf] at h
        | some idk =>
          simp [hf] at h


theorem find_it_true_cons (h : find_it ((a, true)::b) = some (c1 :: c, d, e)) :
    find_it b = (c, d, e) ∧ c1 = (a, true) := by
  induction b with
  | nil =>
    simp [find_it] at h
  | cons hb tb ih =>
    rcases hb with ⟨fb, sb⟩
    cases sb with
    | false =>
      simp [find_it] at h
      cases h1 : find_it ((fb, false) :: tb) with
      | none => simp [h1] at h
      | some val =>
        simp [h1] at h
        constructor
        · rw [← h.2, ← h.1.2]
        exact h.1.1.symm
    | true =>
      simp [find_it] at h
      cases h1 : find_it ((fb, true) :: tb) with
      | none => simp [h1] at h
      | some val =>
        simp [h1] at h
        constructor
        · rw [← h.2, ← h.1.2]
        exact h.1.1.symm

theorem fitc_iff (h : find_it tail1 = some (v1, v2, v3)) :
    find_it ((a, true) :: tail1) = some ((a, true) :: v1, v2, v3) :=
  find_it_some_cons_true h

theorem find_it_spec {L : List ((ℕ × Bool))} (h : find_it L = some (c, d, e)) :
    L = c ++ ([(d.1, false)] ++ [(d.2, true)]) ++ e := by
  induction L generalizing c d e with
  | nil => simp [find_it] at h
  | cons head tail ih =>
  cases tail with
  | nil => simp [find_it] at h
  | cons head1 tail1 =>
    rcases head with ⟨fst1, snd1⟩
    cases snd1 with
    | false =>
      rcases head1 with ⟨fst2, snd2⟩
      cases snd2 with
      | false =>
        unfold find_it at h
        cases hcases : find_it ((fst2, false) :: tail1) with
        | none => simp [hcases] at h
        | some thing =>
          rcases thing with ⟨v1, v2, v3⟩
          simp only [hcases, Option.some.injEq, Prod.mk.injEq] at h
          rw [h.2.1, h.2.2] at hcases
          rw [← h.1, ih hcases]
          simp
      | true =>
        simp only [find_it, Option.some.injEq, Prod.mk.injEq, List.nil_eq] at h
        rw [h.1, h.2.2]
        have H := Prod.mk.inj h.2.1
        rw [← H.1, ← H.2]
        simp
    | true =>
      cases c with
      | nil =>
        rcases find_it_first_empty h with ⟨a1, a2, ha⟩
        simp at ha
      | cons head3 tail3 =>
        apply find_it_true_cons at h
        rw [ih h.1, ← h.2]
        simp

theorem find_it_pair {a b : ℕ × Bool} (h : find_it [a,b] = some (c, d, e)) :
    d = (a.1, b.1) := by
  have H := find_it_spec h
  rcases d with ⟨d1, d2⟩
  have h_len := congr_arg List.length H
  simp only [List.length, zero_add, Nat.reduceAdd, List.cons_append, List.nil_append,
    List.append_assoc, List.length_append] at h_len
  simp only [List.cons_append, List.nil_append, List.append_assoc] at H
  have hc : c = [] := List.length_eq_zero_iff.mp (by omega)
  have he : e = [] := List.length_eq_zero_iff.mp (by omega)
  rw [hc, he, List.nil_append, List.cons.injEq, List.cons.injEq] at H
  simp [H]

abbrev triangle : Type := Σ a b : List (ℕ), Σ c : List (ℕ × Bool), PLift (a.length > 0 ∧ b.length > 0) ×
    (SemiThue reversing (to_up_plain a ++ to_over_plain b) c)

noncomputable def get_pg (a : triangle) : Σ bot mid top, PartialGrid (to_up a.1)
    (to_over a.2.1) bot mid top × PLift (remove_ones (bot ++ mid ++ top) = a.2.2.1) := by
  have H := @stepOne_mid (to_up_plain a.1 ++ to_over_plain a.2.1) a.2.2.1 a.2.2.2.2
  have H1 : skeleton_order (to_up_plain a.1 ++ to_over_plain a.snd.fst) := by
    unfold skeleton_order
    use to_up_plain a.1
    use to_over_plain a.snd.fst
    constructor
    · intro x hx
      have H := hx.1
      simp [to_up_plain] at H
      constructor
      rcases H with ⟨a1, ha1⟩
      aesop
    constructor
    · simp [is_true, to_over_plain]
      intro x ⟨hx⟩
      constructor
      simp at hx
      rcases hx with ⟨w, hw⟩
      rw [← hw.2]
    exact ⟨rfl⟩
  specialize H H1
  rcases H with ⟨c, Hc⟩
  have H4 : (to_option (List.map (fun y ↦ (y, false)) a.fst.reverse)).length > 0 := by
    rw [to_option_length]
    simp
    exact a.2.2.2.1.1.1
  have H5 : (to_option (List.map (fun y ↦ (y, true)) a.snd.fst)).length > 0 := by
    simp [to_option_length]
    exact a.2.2.2.1.1.2
  have H6 : to_option (to_up_plain a.1 ++ to_over_plain a.snd.fst) =
    to_option (to_up_plain a.1) ++ to_option (to_over_plain a.snd.fst) := by
      simp [to_option, to_over_plain, to_up_plain]
  rw [H6] at Hc
  have H3 := @step_two (to_option (List.map (fun y ↦ (y, false)) a.fst.reverse))
    (to_option (List.map (fun y ↦ (y, true)) a.snd.fst)) c
    (by apply is_false_to_option; simp [is_true]; intro x ⟨hx⟩; simp at hx; constructor;
        rcases hx with ⟨a, ha⟩; aesop) H4
    (by apply is_true_to_option ; simp [is_true]; intro x ⟨hx⟩; simp at hx; constructor;
         rcases hx with ⟨a, ha⟩; rw [← ha.2]) H5 Hc.1
  rcases H3 with ⟨bot, mid, up, pg, c_is⟩
  use bot, mid, up
  constructor
  · have H : a.1.length ≠ 0 := by
        intro h
        rw [List.eq_nil_iff_length_eq_zero.mpr h] at H4
        simp  [to_option] at H4
    have H1 : a.2.1.length ≠ 0 := by
      intro h
      rw [List.eq_nil_iff_length_eq_zero.mpr h] at H5
      simp [to_option] at H5
    have H2 : a.1 ≠ [] := by aesop
    have H3 : a.2.1≠ [] := by aesop
    simp [to_up, H2, to_over, H3]
    unfold to_option at pg
    change PartialGrid ((List.map (fun (x : ℕ × Bool) ↦ (some x.1, x.2)) ∘ (List.map (fun y ↦ (y, false)))) a.fst.reverse)
      ((List.map (fun (x : ℕ × Bool) ↦ (some x.1, x.2)) ∘ (List.map (fun y ↦ (y, true)))) a.snd.fst) bot mid up at pg
    have H : ∀ b, List.map (fun (x : ℕ × Bool) ↦ (some x.1, x.2)) ∘ (List.map (fun y ↦ (y, b))) = List.map (fun x => (some x, b)) := by
      intro b
      ext
      simp
    rw [H, H] at pg
    simp at pg
    exact pg
  rw [c_is.1]
  exact Hc.2.2

noncomputable def get_n' (a : triangle) : ℕ := ab_len a.1 a.2.1 - (rw_length_rev a.2.2.2.2)

set_option pp.notation true

theorem straight_pg_sm_g (h : PartialGrid a b c d e) (h1 : gridt a1 b1 f g)
    : a = to_up a1 → b = to_over b1 → h.length ≤ h1.length := by
  intro ha hb
  apply pg_sm_g_eq1 h h1
  · rw [ha]
    exact remove_up_is_plain
  rw [hb]
  exact remove_over_is_plain


-- theorem rw_length_zero_of_eq (h : SemiThue reversing a1 a2) (ha : a1 = a2) : rw_length_rev h = 0 := by
--   induction h with
--   | refl a => simp [rw_length_rev]
--   | reduction h =>
--     simp at ha
--     exfalso
--     cases h
--     all_goals simp at ha
--   | trans a b c _ _ _ _ => sorry

-- theorem rw_length_zero_of_eq_one_step (h : SemiThue_one_step reversing a1 a2) (ha : a1 = a2) : rw_length_one_step_rev h = 0 := by
--   induction h with
--   | refl a => simp [rw_length_one_step_rev]
--   | one_step h1 h2 ih =>
--     simp [rw_length_one_step_rev]


--make a more general version of this which takes in any relations
noncomputable def one_step_trans_rev
  (h1 : SemiThue_one_step reversing a b) (h2 : SemiThue_one_step reversing b c) :
    (h3 : SemiThue_one_step reversing a c) ×
    PLift (rw_length_one_step_rev h3 = rw_length_one_step_rev h1 + rw_length_one_step_rev h2) := by
  induction h2
  · use h1
    constructor
    simp [rw_length_one_step_rev]
  rename_i d e f g h i j k
  specialize k h1
  rcases k with ⟨h4, len4⟩
  cases j with
  | basic n =>
    use h4.one_step (reversing.basic n)
    constructor
    rw [rw_length_one_step_rev, rw_length_one_step_rev, len4.1, add_assoc]
  | apart h =>
    use h4.one_step (reversing.apart h)
    constructor
    rw [rw_length_one_step_rev, rw_length_one_step_rev, len4.1, add_assoc]
  | close h =>
    use h4.one_step (reversing.close h)
    constructor
    rw [rw_length_one_step_rev, rw_length_one_step_rev, len4.1, add_assoc]

noncomputable def one_step_of_reg_rev_w_len {a b} :
    ((h1 : SemiThue reversing a b )→ (Σ h2 : SemiThue_one_step reversing a b,
    PLift (rw_length_rev h1 = rw_length_one_step_rev h2) )) := by
  intro h
  induction h
  · use SemiThue_one_step.refl _
    constructor
    simp [rw_length_rev, rw_length_one_step_rev]
  · rename_i c d e f h
    use SemiThue_one_step.one_step (SemiThue_one_step.refl _) h
    constructor
    cases h
    all_goals rw [rw_length_rev, rw_length_one_step_rev, rw_length_one_step_rev]
  rename_i ih1 ih2
  use (one_step_trans_rev ih1.1 ih2.1).1
  constructor
  rw [rw_length_rev, (one_step_trans_rev ih1.1 ih2.1).2.1]
  exact Mathlib.Tactic.Ring.add_congr ih1.2.1 ih2.2.1 rfl

theorem semithue_cons_length : rw_length (@SemiThue_cons _ _ _ _ c h) = rw_length h := by
  unfold SemiThue_cons
  induction h with
  | refl a => simp [rw_length]
  | reduction h => simp [rw_length]
  | trans a b c ha hb ih1 ih2 =>
    simp [rw_length, ← ih2, ← ih1]

-- set_option pp.proofs true in
-- def SemiThue_rel_w_len (h : grid_style a b) : {h1 : SemiThue grid_style a b // rw_length h1 = rw_length (@SemiThue.reduction _ _ _ _ [] [] h)} := by
--   simp only [← List.nil_append a, ← List.nil_append b, ← List.append_nil ([] ++ a), ← List.append_nil ([] ++ b)]
--   use SemiThue.reduction h
--   simp [rw_length]

noncomputable def equiv_insert_w_len : {h1 : SemiThue grid_style (a :: L) (insert_one a L) // rw_length h1 = 0} := by
  have H : ∀ t L a, L.length ≤ t → {h1 : SemiThue grid_style (a :: L) (insert_one a L) // rw_length h1 = 0} := by
    intro t
    induction t
    · intro L a len
      simp at len
      rw [len]
      use SemiThue.refl [a]
      simp [rw_length]
    rename_i n ih
    intro L a len
    match a with
    | (none, true) =>
      have H : (insert_one (none, true) L) = (none, true) :: L := by
        simp [insert_one]
      rw [H]
      use SemiThue.refl ((none, true) :: L)
      simp [rw_length]
    | (none, false) =>
      match L with
      | [] => use SemiThue.refl [(none, false)]; simp [rw_length]
      | (none, true) :: tail =>
        simp at len
        use SemiThue.trans _ _ _ (SemiThue_append_right_w_len _ (@SemiThue.reduction _ _ _ _ [] [] grid_style.empty)).1 (SemiThue_cons (ih tail _ len).1)
        rw [rw_length, (SemiThue_append_right_w_len _ _).2, semithue_cons_length, (ih tail _ len).2, rw_length]
      | (none, false) :: tail =>
        use SemiThue.refl ((none, false) :: (none, false) :: tail)
        simp [rw_length]
      | (some c, true) :: tail1 =>
        simp at len
        specialize ih tail1 (none, false) len
        use SemiThue.trans _ _ _ (SemiThue_append_right_w_len _ (@SemiThue.reduction _ _ _ _ [] [] (grid_style.up c))).1 (SemiThue_cons ih.1)
        simp [rw_length, (SemiThue_append_right_w_len _ _).2, semithue_cons_length, ih.2]
      | (some c, false) :: tail1 =>
        use SemiThue.refl ((none, false) :: (some c, false) :: tail1)
        simp [rw_length]
    | (some b, true) =>
      match L with
      | [] => use SemiThue.refl _; simp [rw_length]
      | (none, true) :: tail => use SemiThue.refl _ ; simp [rw_length]
      | (none, false) :: tail => use SemiThue.refl _ ; simp [rw_length]
      | (some c, true) :: tail1 => use SemiThue.refl _ ; simp [rw_length]
      | (some c, false) :: tail1 => use SemiThue.refl _ ; simp [rw_length]
    | (some b, false) =>
      match L with
      | [] => use SemiThue.refl _ ; simp [rw_length]
      | (none, true) :: tail =>
        simp at len
        specialize ih tail (some b, false) len
        use SemiThue.trans _ _ _ (SemiThue_append_right_w_len _ (@SemiThue.reduction _ _ _ _ [] [] (grid_style.over b))).1 (SemiThue_cons ih.1)
        simp [rw_length, (SemiThue_append_right_w_len _ _).2, semithue_cons_length, ih.2]
      | (none, false) :: tail => use SemiThue.refl _ ; simp [rw_length]
      | (some c, true) :: tail1 => use SemiThue.refl _ ;  simp [rw_length]
      | (some c, false) :: tail1 => use SemiThue.refl _ ; simp [rw_length]
  exact H L.length _ _ (by simp)


noncomputable def equiv_move_ones_for_len : SemiThue grid_style L (move_ones L) := by
  induction L
  · exact SemiThue.refl []
  rename_i head tail ih
  exact SemiThue.trans _ _ _ (SemiThue_cons ih) (equiv_insert_w_len).1

theorem equiv_insert_no_length {b c} : rw_length (@equiv_insert_w_len b c).1 = 0 := by
  exact (@equiv_insert_w_len b c).2

theorem move_ones_no_length {b} : rw_length (@equiv_move_ones_for_len b) = 0 := by
  induction b with
  | nil => simp [equiv_move_ones_for_len, rw_length]
  | cons head tail ih =>
    unfold equiv_move_ones_for_len
    simp only [rw_length, equiv_insert_no_length, semithue_cons_length]
    unfold equiv_move_ones_for_len at ih
    rw [ih]

noncomputable def rg_of_rev_rel_w_len (d1) (gr : SemiThue grid_style (to_option a) b') (b'_is : remove_ones b' =
      e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b') (rel_holds : grid_style_real
      [(some c1, false), (some c2, true)] d1) : Σ b', (gr' : SemiThue grid_style (to_option a) b') ×
      PLift (remove_ones b' = e ++ (remove_ones d1) ++ f) × irreducible b' × PLift (rw_length gr + 1 = rw_length gr'):= by
  have H1 : [(c1, false), (c2, true)].Infix' (remove_ones b') := by
    rw [b'_is]
    use e, f
    exact {down := rfl}
  rcases (pts_of_irr pt_b) b' (List.infix_refl_C b') c1 c2 H1 with ⟨w, t, hwt⟩
  rw [← hwt.1] at b'_is
  rw [remove_ones_append, remove_ones_append] at b'_is
  simp only [remove_ones] at b'_is
  have ptw : pts w := by
    rw [← hwt.1] at pt_b
    exact pts_chop_right (pts_chop_right (pts_of_irr pt_b))
  have ptt : pts t := by
    rw [← hwt.1, List.append_assoc] at pt_b
    exact pts_chop_left (pts_chop_left (pts_of_irr pt_b))
  rw [← hwt.1] at pt_b
  have := giant_list_split b'_is (irreducible_append (irreducible_append pt_b).1).1
    (irreducible_append pt_b).2
  rcases this with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
  · use move_ones (w ++ d1 ++ t)
    have hi := hwt.1.symm
    subst hi
    use (by apply SemiThue.trans _ _ _ gr; exact SemiThue.trans _ _ _ (SemiThue.reduction (by cases rel_holds with
        | basic n => exact grid_style.basic c1
        | apart h => exact grid_style.apart h
        | close h => exact grid_style.close h)) equiv_move_ones_for_len)
    constructor
    · exact {down := by rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, h2.1.1,
        h2.1.2]}
    constructor
    · exact irreducible_move_ones
    constructor
    rw [rw_length, rw_length, add_right_inj, move_ones_no_length, add_zero]
    cases rel_holds with
    | basic n =>
      simp [rw_length]
    | apart h =>
      simp [rw_length]
    | close h =>
      simp [rw_length]
  · use move_ones (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
    have hi := hwt.1.symm
    subst hi
    have hi2 := hw.1.1
    subst hi2
    -- have H : SemiThue grid_style ((w1 ++ [(some c1, false), (some c2, true)] ++ w2) ++ [(some c1, false), (some c2, true)] ++ t)
    --       (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t) := by
    --     apply SemiThue_append_right
    --     apply SemiThue_append_right
    --     apply SemiThue.reduction
    --     cases rel_holds with
    --     | basic n => exact grid_style.basic c1
    --     | apart h => exact grid_style.apart h
    --     | close h => exact grid_style.close h
    use
      (by apply SemiThue.trans _ _ _ gr; apply (SemiThue_append_right_w_len _ <|
      (SemiThue_append_right_w_len _ (SemiThue.reduction (by
        cases rel_holds with
        | basic n => exact grid_style.basic c1
        | apart h => exact grid_style.apart h
        | close h => exact grid_style.close h))).1).1.trans _ _ _ equiv_move_ones_for_len)
    constructor
    · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, hw.1.2.1, hw.1.2.2]
      exact {down := by simp [remove_ones, remove_ones_append]}
    constructor
    · exact irreducible_move_ones
    constructor
    rw [rw_length, rw_length, add_right_inj, move_ones_no_length, add_zero,
      (SemiThue_append_right_w_len _ _).2, (SemiThue_append_right_w_len _ _).2]
    cases rel_holds with
    | basic n =>
      simp [rw_length]
    | apart h =>
      simp [rw_length]
    | close h =>
      simp [rw_length]
  use move_ones (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
  have hi := hwt.1.symm
  rw [List.append_assoc] at hi
  subst hi
  have another := ht.1.1
  subst another
  rw [List.append_assoc, List.append_assoc, List.append_assoc, ← List.append_assoc t1]
  use (by apply SemiThue.trans _ _ _ gr ((SemiThue_append_left_w_len _
            ((SemiThue_append_left_w_len _ (SemiThue.reduction (by
                cases rel_holds with
                | basic n => exact grid_style.basic c1
                | apart h => exact grid_style.apart h
                | close h => exact grid_style.close h))).1)).1.trans _ _ _ equiv_move_ones_for_len))
  constructor
  · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, ht.1.2.1, ht.1.2.2]
    exact {down := by simp [remove_ones, remove_ones_append]}
  constructor
  · exact irreducible_move_ones
  constructor
  rw [rw_length, rw_length, add_right_inj, move_ones_no_length, add_zero]
  rw [(SemiThue_append_left_w_len _ _).2, (SemiThue_append_left_w_len _ _).2]
  cases rel_holds with
    | basic n =>
      simp [rw_length]
    | apart h =>
      simp [rw_length]
    | close h =>
      simp [rw_length]

noncomputable def one_step_rev_to_grid_w_len (h : SemiThue_one_step reversing a b) :
   Σ b', (h1 : SemiThue grid_style (to_option a) b') × PLift
  (remove_ones b' = b) × irreducible b' × PLift (rw_length_one_step_rev h = rw_length h1) := by
  induction h with
  | refl a =>
    use to_option a, SemiThue.refl (to_option a)
    constructor
    · exact { down := remove_map_helper }
    constructor
    · exact irr_to_option
    constructor
    simp [rw_length, rw_length_rev, rw_length_one_step_rev]
  | one_step h1 h2 ih =>
    rename_i c d e f g
    rcases ih with ⟨b', gr, b'_is, pt_b⟩
    cases h2 with
    | basic h_dist =>
      apply Nat.eq_of_dist_eq_zero at h_dist
      have H := rg_of_rev_rel_w_len ([(none, true), (none, false)]) gr  b'_is.1 pt_b.1 --(.basic h_dist)
      rw [h_dist] at H
      specialize H (.basic _)
      rcases H with ⟨b'', gr', b'_is', pt_b', hlen⟩
      use b'', gr'
      constructor
      · constructor
        rw [b'_is'.1]
        simp [remove_ones]
      constructor
      · exact pt_b'
      constructor
      rw [rw_length_one_step_rev]
      rw [pt_b.2.1]
      exact hlen.1
    | apart h_dist =>
      rename_i i j
      have H := rg_of_rev_rel_w_len ([(some j, true), (some i, false)]) gr b'_is.1 pt_b.1 (.apart h_dist)
      rcases H with ⟨b'', gr', b'_is', pt_b', hlen⟩
      use b'', gr'
      constructor
      · constructor
        rw [b'_is'.1]
        simp [remove_ones]
      constructor
      · exact pt_b'
      constructor
      rw [rw_length_one_step_rev]
      rw [pt_b.2.1]
      exact hlen.1
    | close h_dist =>
      rename_i i j
      have H := rg_of_rev_rel_w_len ([(some j, true), (some i, true), (some j, false), (some i, false)]) gr b'_is.1 pt_b.1 (.close h_dist)
      rcases H with ⟨b'', gr', b'_is', pt_b', hlen⟩
      use b'', gr'
      constructor
      · constructor
        rw [b'_is'.1]
        simp [remove_ones]
      constructor
      · exact pt_b'
      constructor
      rw [rw_length_one_step_rev]
      rw [pt_b.2.1]
      exact hlen.1

noncomputable def rev_to_grid_w_len (h : SemiThue reversing a b) :
   Σ b', (h1 : SemiThue grid_style (to_option a) b') × PLift
  (remove_ones b' = b) × irreducible b' × PLift (rw_length_rev h = rw_length h1) := by
  have H := (one_step_of_reg_rev_w_len h)
  have H2 := one_step_rev_to_grid_w_len H.1
  rcases H2 with ⟨b', h1, h2, irr, hl⟩
  use b'
  use h1, h2, irr
  rw [← hl.1]
  exact H.2

  -- induction H with
  -- | refl a =>
  --   use to_option a, SemiThue.refl (to_option a)
  --   constructor
  --   · exact { down := remove_map_helper }
  --   constructor
  --   · exact irr_to_option
  --   constructor
  --   simp [rw_length, rw_length_rev]
  --   have H := (one_step_of_reg_rev_w_len h).2

  --   rw [H.1]
  --   sorry -- need a version of H with length

  -- | one_step h1 h2 ih =>
  --   rename_i c d e f g
  --   rcases ih (one_step_equiv_reg.2 h1) with ⟨b', gr, b'_is, pt_b⟩
  --   cases h2 with
  --   | basic h_dist =>
  --     apply Nat.eq_of_dist_eq_zero at h_dist
  --     have H := rg_of_rev_rel ([(none, true), (none, false)]) gr  b'_is.1 pt_b.1 --(.basic h_dist)
  --     rw [h_dist] at H
  --     specialize H (.basic _)
  --     rcases H with ⟨b'', gr', b'_is', pt_b'⟩
  --     use b'', gr'
  --     constructor
  --     · constructor
  --       rw [b'_is'.1]
  --       simp [remove_ones]
  --     constructor
  --     · exact pt_b'
  --     constructor
  --     have H := (one_step_of_reg_rev_w_len h).2

  --     sorry


  --   | apart h_dist =>
  --     rename_i i j
  --     have H := rg_of_rev_rel ([(some j, true), (some i, false)]) gr b'_is.1 pt_b.1 (.apart h_dist)
  --     rcases H with ⟨b'', gr', b'_is', pt_b'⟩
  --     use b'', gr'
  --     constructor
  --     · constructor
  --       rw [b'_is'.1]
  --       simp [remove_ones]
  --     constructor
  --     · exact pt_b'
  --     sorry
  --   | close h_dist =>
  --     rename_i i j
  --     have H := rg_of_rev_rel ([(some j, true), (some i, true), (some j, false), (some i, false)]) gr b'_is.1 pt_b.1 (.close h_dist)
  --     rcases H with ⟨b'', gr', b'_is', pt_b'⟩
  --     use b'', gr'
  --     constructor
  --     · constructor
  --       rw [b'_is'.1]
  --       simp [remove_ones]
  --     constructor
  --     · exact pt_b'
  --     sorry


noncomputable def rev_to_gs_w_len_general (h : SemiThue reversing a c) :
  Σ c1, Σ (h1 : SemiThue grid_style (to_option a) c1), PLift (rw_length_rev h = rw_length h1) := by
  -- probably the statement needs to be tweaked based on step one
  have H := rev_to_grid_w_len h
  rcases H with ⟨c1, h1, h2, h3, hl⟩
  use c1
  use h1
  exact hl

theorem to_option_append : to_option (a ++ b) = to_option a ++ to_option b := by simp [to_option]

noncomputable def rev_to_gs_w_len (h : SemiThue reversing (to_up_plain a ++ to_over_plain b) c) (ha : a.length > 0) (hb : b.length > 0) :
  Σ c1, Σ (h1 : SemiThue grid_style ((to_up a) ++ (to_over b)) c1), PLift (rw_length_rev h = rw_length h1) := by
  -- probably the statement needs to be tweaked based on step one
  rcases rev_to_gs_w_len_general h with ⟨c1, h1, hl⟩
  use c1
  have ha : to_up a = to_option (to_up_plain a) := by exact Eq.symm (to_option_up_plain_eq_up ha)
  rw [ha]
  have hb : to_over b = to_option (to_over_plain b) := by exact Eq.symm (to_option_over_plain_eq_over hb)
  rw [hb, ← to_option_append]
  use h1
  exact hl

#check pgf_of_st_w_len

noncomputable def st_pgf_len (h : SemiThue reversing (to_up_plain a ++ to_over_plain b) c)
  (ha : a.length > 0) (hb : b.length > 0) :
  Σ c , Σ h1 : pgf (to_up a) (to_over b) c, PLift (rw_length_rev h = h1.length) := by
  have H := rev_to_gs_w_len h ha hb
  rcases H with ⟨c1, h2, hl⟩
  rw [hl.1]
  use c1
  have H3 := one_step_of_reg_w_len h2
  rcases H3 with ⟨h4, hl4⟩
  rw [hl4.1]
  have H2 := @pgf_of_st_w_len _ _ (to_up a) (to_over b) h4 rfl (is_false_up) (to_up_len_pos)
    (is_true_over) (to_over_len_pos)
  exact H2

noncomputable def get_frontier_style_converse (h1 : pgf a b mid) :
  Σ c d e, (h : PartialGrid a b c d e) ×
  PLift (mid = c ++ d ++ e ∧ h.length = h1.length) := by
  induction h1 with
  | skeleton ha ha1 hb hb1 =>
    use [], (a ++ b), []
    use PartialGrid.empty a b ha ha1 hb hb1
    constructor
    constructor
    · simp
    simp [PartialGrid.length, pgf.length]
  | empty h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := add_empty_cell_w_len s (empty_fill.empty) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [pgf.length, ← t.1.2, hl.1]
  | top_bottom i h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := add_empty_cell_w_len s (empty_fill.up _) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [pgf.length, ← t.1.2, hl.1]
  | sides i h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := add_empty_cell_w_len s (empty_fill.over _) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [pgf.length, ← t.1.2, hl.1]
  | top_left i h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := add_cell_w_len s (grid_style_real.basic _) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [pgf.length, ← t.1.2]
    exact hl.1.symm
  | adjacent i j hd h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := add_cell_w_len s (grid_style_real.close hd) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [pgf.length, ← t.1.2]
    exact hl.1.symm
  | separated i k hd h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H1 : p ++ q ++ r = n ++ [(some i, false), (some k, true)] ++ o := by
      rw [← t.1.1, hc]
    have H2 : grid_style_real [(some i, false), (some k, true)] [(some k, true), (some i, false)] :=
      grid_style_real.apart hd
    have H := add_cell_w_len s (grid_style_real.apart hd) H1
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [pgf.length, ← t.1.2]
    exact hl.1.symm

noncomputable def st_pg_len (h : SemiThue reversing (to_up_plain a ++ to_over_plain b) c)
  (ha : a.length > 0) (hb : b.length > 0) :
  Σ c d e, Σ h1 : PartialGrid (to_up a) (to_over b) c d e, PLift (rw_length_rev h = h1.length) := by
  have H := st_pgf_len h ha hb
  rcases H with ⟨c, h3, h4⟩
  rw [h4.1]
  have H := get_frontier_style_converse h3
  rcases H with ⟨d, e, f, h1, h2⟩
  use d, e, f, h1
  exact ⟨h2.1.2.symm⟩

theorem st_smaller_than_g (h : SemiThue reversing (to_up_plain a ++ to_over_plain b) c)
  (ha : a.length > 0) (hb : b.length > 0):
    ab_len a b ≥ rw_length_rev h := by
  rcases st_pg_len h ha hb with ⟨c, d, e, h1, hl⟩
  rw [hl.1]
  apply straight_pg_sm_g
  rfl
  rfl

def solver_helper (a : triangle) : List (ℕ × Bool) :=
  match hb': find_it a.2.2.1 with
  | none => a.2.2.1
  | some (c, d, e) =>
    match hd : d.1.dist d.2 with
    | 0 => solver_helper ⟨a.1, ⟨a.2.1, ⟨c ++ [] ++ e,
        ⟨a.2.2.2.1,
        by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.basic hd)⟩⟩⟩⟩
    | 1 => solver_helper ⟨a.1, ⟨a.2.1, ⟨(c ++ [(d.2, true), (d.1, true), (d.2, false), (d.1, false)] ++ e),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.close hd)⟩ ⟩⟩⟩
    | Nat.succ (Nat.succ n) => solver_helper ⟨a.1, ⟨a.2.1, ⟨(c ++ [(d.2, true), (d.1, false)] ++ e),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.apart (by omega))⟩⟩⟩⟩
    termination_by get_n' a
    decreasing_by
    · rcases a with ⟨a1, a2, a3, a4⟩
      simp only
      rcases find_it_spec hb' with ⟨b1, b2, b3⟩
      rcases d with ⟨x, y⟩
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · simp [rw_length_rev]
      · apply st_smaller_than_g
        simp only [gt_iff_lt, a4.1.1.1]
        simp [a4.1.1.2]
      apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    · rcases a with ⟨a1, a2, a3, a4⟩
      rcases find_it_spec hb' with ⟨b1, b2, b3⟩
      rcases d with ⟨x, y⟩
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · simp [rw_length_rev]
      · apply st_smaller_than_g
        simp [a4.1.1.1]
        simp [a4.1.1.2]
      apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec hb' with ⟨b1, b2, b3⟩
    rcases d with ⟨x, y⟩
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [rw_length_rev]
    · apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    apply st_smaller_than_g
    simp [a4.1.1.1]
    simp [a4.1.1.2]

def solver_helper' (a : triangle) : {h : triangle // h.1 = a.1 ∧ h.2.1 = a.2.1} :=
  match hb' : find_it a.2.2.1 with
  | none => ⟨a, ⟨rfl, rfl⟩⟩
  | some (c, d, e) =>
    match hd : d.1.dist d.2 with
    | 0 => solver_helper' ⟨a.1, ⟨a.2.1, ⟨c ++ [] ++ e,
        ⟨a.2.2.2.1,
        by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.basic hd)⟩⟩⟩⟩
    | 1 => solver_helper' ⟨a.1, ⟨a.2.1, ⟨(c ++ [(d.2, true), (d.1, true), (d.2, false), (d.1, false)] ++ e),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.close hd)⟩ ⟩⟩⟩
    | Nat.succ (Nat.succ n) => solver_helper' ⟨a.1, ⟨a.2.1, ⟨(c ++ [(d.2, true), (d.1, false)] ++ e),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.apart (by omega))⟩⟩⟩⟩
    termination_by get_n' a
    decreasing_by
    · rcases a with ⟨a1, a2, a3, a4⟩
      simp only
      rcases find_it_spec hb' with ⟨b1, b2, b3⟩
      rcases d with ⟨x, y⟩
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · simp [rw_length_rev]
      · apply st_smaller_than_g
        simp [a4.1.1.1]
        simp [a4.1.1.2]
      apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    · rcases a with ⟨a1, a2, a3, a4⟩
      rcases find_it_spec hb' with ⟨b1, b2, b3⟩
      rcases d with ⟨x, y⟩
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · simp [rw_length_rev]
      · apply st_smaller_than_g
        simp [a4.1.1.1]
        simp [a4.1.1.2]
      apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec hb' with ⟨b1, b2, b3⟩
    rcases d with ⟨x, y⟩
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [rw_length_rev]
    · apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    apply st_smaller_than_g
    simp [a4.1.1.1]
    simp [a4.1.1.2]

theorem solver_helper_find_it_none' : find_it (solver_helper a)= none := by
  induction ha : get_n' a using Nat.strongRecOn generalizing a
  rw [solver_helper]
  split
  · assumption
  split
  · rename_i ih l m o p hd
    apply @ih
      (get_n' ⟨a.fst, ⟨a.snd.fst, ⟨l ++ [] ++ o, ⟨a.2.2.2.1,
          by
          apply a.2.2.2.2.trans
          rw [find_it_spec p]
          exact SemiThue.reduction (reversing.basic hd)⟩⟩⟩⟩)
    rw [← ha]
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec p with ⟨b1, b2, b3⟩
    have H : m.1 = m.2 := by exact Nat.eq_of_dist_eq_zero hd
    rcases m with ⟨x, y⟩
    simp only at H
    subst H
    unfold get_n'
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [rw_length_rev]
    · apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    apply st_smaller_than_g
    simp [a4.1.1.1]
    simp [a4.1.1.2]
    rfl
  · rename_i ih m n o p hd
    apply @ih (get_n' ⟨a.1, ⟨a.2.1, ⟨(m ++ [(n.2, true), (n.1, true), (n.2, false), (n.1, false)] ++ o),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec p]
          exact SemiThue.reduction (reversing.close hd)⟩ ⟩⟩⟩)
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec p with ⟨b1, b2, b3⟩
    rcases n with ⟨x, y⟩
    rw [← ha]
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [rw_length_rev]
    · apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    apply st_smaller_than_g
    simp [a4.1.1.1]
    simp [a4.1.1.2]
    rfl
  rename_i ih l m n o p hd
  apply @ih (get_n' ⟨a.1, ⟨a.2.1, ⟨(l ++ [(m.2, true), (m.1, false)] ++ n),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec o]
          exact SemiThue.reduction (reversing.apart (by omega))⟩⟩⟩⟩)
  rcases a with ⟨a1, a2, a3, a4⟩
  rcases find_it_spec o with ⟨b1, b2, b3⟩
  rcases m with ⟨x, y⟩
  rw [← ha]
  apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
  · simp [rw_length_rev]
  · apply st_smaller_than_g
    simp [a4.1.1.1]
    simp [a4.1.1.2]
  apply st_smaller_than_g
  simp [a4.1.1.1]
  simp [a4.1.1.2]
  rfl

theorem solver_helper_find_it_none (a) : find_it (solver_helper' a).1.2.2.1 = none := by
  induction ha : get_n' a using Nat.strongRecOn generalizing a
  rw [solver_helper']
  split
  · assumption
  split
  · rename_i ih l m o p hd
    simp at hd
  rename_i ih l m n o p q r samesies
  rw [samesies] at o
  simp only [List.cons_append, List.nil_append, eq_mpr_eq_cast, Nat.succ_eq_add_one]
  split
  · rename_i hd
    simp only
    apply @ih
      (get_n' ⟨a.fst, ⟨a.snd.fst, ⟨p ++ [] ++ r, ⟨a.2.2.2.1,
          by
          apply a.2.2.2.2.trans
          rw [find_it_spec o]
          exact SemiThue.reduction (reversing.basic hd)⟩⟩⟩⟩)
    rw [← ha]
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec o with ⟨b1, b2, b3⟩
    have H : q.1 = q.2 := by exact Nat.eq_of_dist_eq_zero hd
    rcases q with ⟨x, y⟩
    simp only at H
    subst H
    unfold get_n'
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [rw_length_rev]
    · apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    apply st_smaller_than_g
    simp [a4.1.1.1]
    simp [a4.1.1.2]
    rfl
  · rename_i hd
    simp only
    apply @ih (get_n' ⟨a.1, ⟨a.2.1, ⟨(p ++ [(q.2, true), (q.1, true), (q.2, false), (q.1, false)] ++ r),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec o]
          exact SemiThue.reduction (reversing.close hd)⟩ ⟩⟩⟩)
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec o with ⟨b1, b2, b3⟩
    rcases q with ⟨x, y⟩
    rw [← ha]
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [rw_length_rev]
    · apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    apply st_smaller_than_g
    simp [a4.1.1.1]
    simp [a4.1.1.2]
    rfl
  rename_i hd
  simp only
  apply @ih (get_n' ⟨a.1, ⟨a.2.1, ⟨(p ++ [(q.2, true), (q.1, false)] ++ r),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec o]
          exact SemiThue.reduction (reversing.apart (by omega))⟩⟩⟩⟩)
  rcases a with ⟨a1, a2, a3, a4⟩
  rcases find_it_spec o with ⟨b1, b2, b3⟩
  rcases q with ⟨x, y⟩
  rw [← ha]
  apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
  · simp [rw_length_rev]
  · apply st_smaller_than_g
    simp [a4.1.1.1]
    simp [a4.1.1.2]
  apply st_smaller_than_g
  simp [a4.1.1.1]
  simp [a4.1.1.2]
  rfl

def in_order_of_find_it_none (h : find_it a = none) : in_order a := by
  induction a with
  | nil =>
    use [], []
    constructor
    · exact is_true_nil
    constructor
    · exact is_false_nil
    constructor
    simp [in_order]
  | cons head tail ih =>
    have h2 := find_it_cons_none h
    specialize ih h2
    rcases ih with ⟨c, d, h1, h2, ⟨h3⟩⟩
    match head with
    | (a, true) =>
      use (a, true)::c, d
      constructor
      · exact is_true_cons c h1
      constructor
      · exact h2
      constructor
      simp [h3]
    | (a, false) =>
      match c with
      | [] =>
        use [], (a, false)::d
        constructor
        · exact h1
        constructor
        · exact is_false_cons d h2
        constructor
        simp [h3]
      | (c1, true) :: c2 =>
        rw [h3] at h
        simp [find_it] at h
      | (c1, false) :: c2 =>
        specialize h1 (c1, false) ⟨by simp⟩
        simp at h1
        exact h1.1.elim

def solver_helper_in_order (a) : in_order (solver_helper' a).1.2.2.1 := by
  have H := solver_helper_find_it_none a
  exact in_order_of_find_it_none H


def solver_long (a b) (ha : List.length a > 0) (hb : List.length b > 0) :=
  solver_helper' ⟨a, ⟨b, ⟨to_up_plain a ++ to_over_plain b, by simp [to_up_plain, to_over_plain]; exact ⟨⟨ha, hb⟩, by apply SemiThue.refl _ ⟩⟩⟩⟩

def solver_long_in_order (a b) (ha : List.length a > 0) (hb : List.length b > 0) :
  in_order (solver_long a b ha hb).1.2.2.1 := by
  have H := solver_helper_find_it_none ⟨a, ⟨b, ⟨to_up_plain a ++ to_over_plain b, by simp [to_up_plain, to_over_plain]; exact ⟨⟨ha, hb⟩, by apply SemiThue.refl _ ⟩⟩⟩⟩
  exact in_order_of_find_it_none H



def solver_equiv (ha : List.length a > 0) (hb : List.length b > 0)  : SemiThue reversing
    (to_up_plain a ++ to_over_plain b) (solver_long a b ha hb).1.2.2.1 := by
  have H := (solver_long a b ha hb).1.2.2.2.2
  simp at H
  convert H
  exact (solver_long a b ha hb).2.1.symm
  exact (solver_long a b ha hb).2.2.symm

def final_solver (a b : List ℕ) : Bool :=
  match a with
  | [] =>
    match b with
    | [] => true
    | b1 :: b2 => false
  | a1 :: a2 =>
    match b with
    | [] => false
    | b1 :: b2 => (solver_long (a1 :: a2) (b1 :: b2) (by simp) (by simp)).1.2.2.1 = []

def in_order_over_plain_up_plain : in_order (to_over_plain c ++ to_up_plain d) := by
  use to_over_plain c
  use to_up_plain d
  constructor
  · exact to_over_plain_true
  constructor
  · exact to_up_plain_false
  exact ⟨rfl⟩

def includes_false (L : List (Option ℕ × Bool)) := ∃ a ∈ L, a.2 = false

theorem includes_false_not_nil (h : includes_false L) : L.length > 0 := by
  match L with
  | [] => simp [includes_false] at h
  | a :: b => simp

theorem includes_false_append_singleton (h : includes_false (L ++ [(a, true)])) : includes_false L := by
  rcases h with ⟨x, hx, h2⟩
  use x
  simp at hx
  cases hx
  · exact ⟨by assumption, h2⟩
  simp_all

theorem remove_to_option_to_over : (remover (to_option (to_over_plain b))) = b := by
  induction b with
  | nil => simp [remover, to_option, to_over_plain]
  | cons b1 b2 ih =>
    simp [remover, to_option, to_over_plain]
    simp [remover, to_option, to_over_plain] at ih
    exact ih

theorem remove_to_option_to_up_plain : (remover (to_option (to_up_plain a)).reverse) = a := by
  induction a with
  | nil => simp [remover, to_option, to_up_plain]
  | cons a1 a2 ih =>
    simp [remover, to_option, to_up_plain]
    simp [remover, to_option, to_up_plain] at ih
    exact ih

theorem remover_nil_of_remove_ones_nil (h : remove_ones bot = []) : remover bot = [] := by
  induction bot with
  | nil => simp [remover]
  | cons head tail ih =>
    match head with
    | (none, b) =>
      simp [remover]
      simp [remove_ones] at h
      exact ih h
    | (some a, b) =>
      simp [remove_ones] at h

theorem remover_rev_nil (h : remover a = []) : remover a.reverse = [] := by
  induction a using List.reverseRecOn with
  | nil => simp [remover]
  | append_singleton front caboose ih =>
    match caboose with
    | (none, b) =>
      simp [remover_append] at h
      simp_all [remover, h]
    | (some a, b) =>
      simp [remover, remover_append] at h

theorem remover_singleton_of_remove_ones (h : remove_ones a = [(c, b)]) : remover a = [c] := by
  induction a with
  | nil => unfold remove_ones at h; simp_all
  | cons head tail ih =>
    unfold remove_ones at h
    unfold remover
    match head with
    | (none, b) => simp_all
    | (some a, b) =>
      simp_all [remover_nil_of_remove_ones_nil]

theorem remove_eq_of_remove_ones_eq_to_over_plain (h : to_over_plain c = remove_ones bot) : remover bot = c := by
  induction c generalizing bot with
  | nil => simp_all [to_over_plain, remover_nil_of_remove_ones_nil]
  | cons c1 c2 ih =>
    simp [to_over_plain] at h
    match hr : remove_ones bot with
    | [] => simp_all
    | r1 :: r2 =>
      simp [hr] at h
      change _ = [r1] ++ r2 at hr
      apply remove_ones_eq_append at hr
      rcases hr with ⟨a1, a2, bot_is, h3, h4⟩
      rw [← h.2] at h4
      specialize ih h4.symm
      simp [bot_is, remover_append, ih, remover_singleton_of_remove_ones h3, ← h.1]

theorem remove_ones_rev : (remove_ones a).reverse = remove_ones a.reverse := by
  induction a
  · simp
  rename_i head tail ih
  match head with
  | (none, b) => simp [remove_ones, ih]
  | (some a, b) => simp [remove_ones, ih]

theorem remover_of_remove_ones_singleton (h : remove_ones a2 = [(b, false)]) :
  remover a2.reverse  = [b] := by
  induction a2 using List.reverseRecOn with
  | nil => simp at h
  | append_singleton front caboose ih =>
    simp_all
    match caboose with
    | (none, b) =>
      simp [remove_ones] at h
      simp [remover]
      exact ih h
    | (some a, b) =>
      simp [remove_ones] at h
      change _ = [] ++ _ at h
      apply List.append_singleton_eq_append_singleton at h
      simp [remover]
      constructor
      · aesop
      apply remover_rev_nil
      apply remover_nil_of_remove_ones_nil h.1

theorem remove_rev_eq_remove_ones_eq_to_up_plain
    (h : remove_ones up = to_up_plain d) : remover up.reverse = d := by
  induction d generalizing up with
  | nil =>
    apply remover_rev_nil
    exact remove_eq_of_remove_ones_eq_to_over_plain h.symm
  | cons head tail ih =>
    simp [to_up_plain] at h
    cases hr : remove_ones up using List.reverseRecOn with
    | nil => simp_all
    | append_singleton front caboose =>
      simp [hr] at h
      apply remove_ones_eq_append at hr
      rcases hr with ⟨a1, a2, bot_is, h3, h4⟩
      apply List.append_singleton_eq_append_singleton at h
      rw [h.1] at h3
      rw [← List.map_reverse] at h3
      specialize ih h3
      rw [bot_is, List.reverse_append, remover_append, ih]
      rw [h.2] at h4
      rw [remover_of_remove_ones_singleton h4]
      simp

theorem not_true_and_false_of_len_gt_zero (h1 : is_true m) (h2 : is_false m) (hl : m.length > 0) : False := by
  induction m with
  | nil => simp at hl
  | cons m1 m2 ih =>
    apply is_true_split at h1
    apply is_false_split at h2
    have H1 := (h1.1 m1 ⟨by simp⟩).1
    have H2 := (h2.1 m1 ⟨by simp⟩).1
    aesop

theorem helper_for_bottom (h : remove_ones b' = to_over_plain c ++ to_up_plain d)
  (h1 : bot ++ up = move_ones b') (hbot : is_true bot) (hup : is_false up): (remover up.reverse) = d ∧ remover bot = c := by
  have one := congr_arg remover h1
  have two := congr_arg remove_ones h1
  simp [remover_append] at one
  simp [remove_ones_append, remove_ones_move_ones] at two
  rw [← two] at h
  rcases List.append_eq_append_iff.mp h with ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
  · match mid with
    | [] =>
      simp_all
      have H := remove_eq_of_remove_ones_eq_to_over_plain spec1
      have H2 := remove_rev_eq_remove_ones_eq_to_up_plain spec2
      simp [H, H2]
    | m1 :: m2 =>
      exfalso
      have H : is_true (to_over_plain c) := to_over_plain_true
      rw [spec1] at H
      apply is_true_append at H
      have H2 : is_false (remove_ones up) := is_false_remove_ones hup
      rw [spec2] at H2
      apply is_false_append at H2
      apply not_true_and_false_of_len_gt_zero (is_true_split H.2).1 (is_false_split H2.1).1
      simp
  match mid with
  | [] =>
    simp_all
    have H := remove_eq_of_remove_ones_eq_to_over_plain spec1.symm
    have H2 := remove_rev_eq_remove_ones_eq_to_up_plain spec2.symm
    simp [H, H2]
  | m1 :: m2 =>
    exfalso
    have H : is_true (remove_ones bot) := is_true_remove_ones hbot
    rw [spec1] at H
    apply is_true_append at H
    have H2 : is_false (to_up_plain d) := to_up_plain_false
    rw [spec2] at H2
    apply is_false_append at H2
    apply not_true_and_false_of_len_gt_zero (is_true_split H.2).1 (is_false_split H2.1).1
    simp

def in_order_singleton : in_order [a] := by
  match a with
  | (a1, true) =>
    use [(a1, true)], []
    constructor
    · exact is_true_cons [] is_true_nil
    constructor
    · exact is_false_nil
    constructor
    simp
  | (a1, false) =>
    use [], [(a1, false)]
    constructor
    · exact is_true_nil
    constructor
    · exact is_false_cons [] is_false_nil
    constructor
    simp

theorem remove_ones_cons : remove_ones (a :: b) = remove_ones [a] ++ remove_ones b := by
  change remove_ones ([a] ++ b) = _
  exact remove_ones_append

noncomputable def in_order_insert_one (h : in_order b) (hr : in_order (remove_ones (a :: b))) :
     in_order (insert_one a b) := by
  induction hb : b.length generalizing a b with
  | zero =>
    rw [List.eq_nil_iff_length_eq_zero.mpr hb]
    simp [insert_one]; exact in_order_singleton
  | succ n ih =>
    match b with
    | [] => simp at hb
    | (none, false) :: tail =>
      simp [insert_one]
      rcases h with ⟨c, d, c_true, d_false, ⟨cd_is⟩⟩
      have H : c = [] := by
        match c with
        | [] => rfl
        | c1 :: c2 =>
          simp at cd_is
          rw [← cd_is.1] at c_true
          specialize c_true (none, false) ⟨by simp⟩
          simp at c_true
          exact c_true.1.elim
      rw [H, List.nil_append] at cd_is
      match a with
      | (a1, false) =>
        use [], (a1, false) :: d
        constructor
        · exact is_true_nil
        constructor
        · exact is_false_cons d d_false
        constructor
        rw [cd_is, List.nil_append]
      | (a1, true) =>
        use [(a1, true)], d
        constructor
        · exact is_true_cons [] is_true_nil
        constructor
        · exact d_false
        constructor
        rw [cd_is]
        rfl
    | (some a1, false) :: tail =>
      simp [insert_one]
      rcases h with ⟨c, d, c_true, d_false, ⟨cd_is⟩⟩
      have H : c = [] := by
        match c with
        | [] => rfl
        | c1 :: c2 =>
          simp at cd_is
          rw [← cd_is.1] at c_true
          specialize c_true (some a1, false) ⟨by simp⟩
          simp at c_true
          exact c_true.1.elim
      rw [H, List.nil_append] at cd_is
      match a with
      | (a1, false) =>
        use [], (a1, false) :: d
        constructor
        · exact is_true_nil
        constructor
        · exact is_false_cons d d_false
        constructor
        rw [cd_is, List.nil_append]
      | (a1, true) =>
        use [(a1, true)], d
        constructor
        · exact is_true_cons [] is_true_nil
        constructor
        · exact d_false
        constructor
        rw [cd_is]
        rfl
    | (none, true) :: tail =>
      match a with
      | (a1, true) =>
        simp [insert_one]
        rcases h with ⟨c, d, c_true, d_false, ⟨cd_is⟩⟩
        use (a1, true) :: c, d
        constructor
        · exact is_true_cons c c_true
        constructor
        · exact d_false
        constructor
        rw [cd_is]
        rfl
      | (a1, false) =>
        simp [insert_one]
        simp at hb
        rw [remove_ones_cons, remove_ones, ← remove_ones_append] at hr
        specialize @ih tail (a1, false) (in_order_rest h) hr hb
        rcases ih with ⟨c, d, c_true, d_false, ⟨cd_is⟩⟩
        use (none, true)::c, d
        constructor
        · exact is_true_cons c c_true
        constructor
        · exact d_false
        constructor
        rw [cd_is]
        rfl
    | (some a1, true) :: tail =>
      match a with
      | (none, true) =>
        simp [insert_one]
        rcases h with ⟨c, d, c_true, d_false, ⟨hcd⟩⟩
        use (none, true) :: c, d
        constructor
        · exact is_true_cons c c_true
        constructor
        · exact d_false
        constructor
        rw [hcd]
        rfl
      | (some a2, true) =>
        simp [insert_one]
        rcases h with ⟨c, d, c_true, d_false, ⟨cd_is⟩⟩
        use (a2, true) :: c, d
        constructor
        · exact is_true_cons c c_true
        constructor
        · exact d_false
        constructor
        rw [cd_is]
        rfl
      | (none, false) =>
        simp [insert_one]
        simp at hb
        rw [remove_ones_cons, remove_ones, remove_ones, remove_ones_nil, List.nil_append] at hr
        specialize @ih tail (none, false) (in_order_rest h)
          (by rw [remove_ones_cons, remove_ones, remove_ones_nil,
          List.nil_append]; exact in_order_rest hr) hb
        rcases ih with ⟨c, d, c_true, d_false, ⟨hcd⟩⟩
        use (some a1, true) :: c, d
        constructor
        · exact is_true_cons c c_true
        constructor
        · exact d_false
        constructor
        rw [hcd]
        rfl
      | (some a2, false) =>
        simp [remove_ones] at hr
        rcases hr with ⟨c, d, c_true, d_false, ⟨hcd⟩⟩
        have H : c = [] := by
          match c with
          | [] => rfl
          | c1 :: c2 =>
            simp at hcd
            rw [← hcd.1] at c_true
            specialize c_true (a2, false) ⟨by simp⟩
            simp at c_true
            exact c_true.1.elim
        rw [H, List.nil_append] at hcd
        rw [← hcd] at d_false
        specialize d_false (a1, true) ⟨by simp⟩
        simp at d_false
        exact d_false.1.elim

noncomputable def in_order_move_ones_of_in_order_remove_ones (h : in_order (remove_ones b)) :
  in_order (move_ones b) := by
  induction b with
  | nil => simp; exact in_order_nil
  | cons head tail ih =>
    simp [move_ones]
    have H : in_order (remove_ones tail) := by
      match head with
      | (none, b) =>
        simp [remove_ones] at h
        exact h
      | (some a, b) =>
        apply in_order_rest
        simp [remove_ones] at h
        exact h
    specialize ih H
    apply in_order_insert_one ih
    rcases ih with ⟨c, d, c_true, d_false, ⟨hcd⟩⟩
    match head with
    | (none, b) =>
      use remove_ones c, remove_ones d
      constructor
      · exact is_true_remove_ones c_true
      constructor
      · exact is_false_remove_ones d_false
      constructor
      simp [remove_ones, hcd]
    | (some a1, true) =>
      use (a1, true) :: remove_ones c, remove_ones d
      constructor
      · apply is_true_cons
        exact is_true_remove_ones c_true
      constructor
      · exact is_false_remove_ones d_false
      constructor
      simp [remove_ones, hcd]
    | (some a1, false) =>
      simp [remove_ones, remove_ones_move_ones]
      simp [remove_ones] at h
      exact h

theorem bm_equiv_of_reversing (ha : List.length a > 0) (hb : List.length b > 0)
  (h : SemiThue reversing (to_up_plain a ++ to_over_plain b) (to_over_plain c ++ to_up_plain d)) :
  PresentedMonoid.mk braid_rels_m_inf (a ++ c) = PresentedMonoid.mk braid_rels_m_inf (b ++ d) := by
  have H0 := stepOne h skeleton_up_plain_over_plain in_order_over_plain_up_plain
  rcases H0 with ⟨b', st, so, io, ⟨rm⟩⟩
  have silly : to_option (to_up_plain a ++ to_over_plain b) =
    to_option (to_up_plain a) ++ to_option (to_over_plain b) := by
    unfold to_option
    simp
  rw [silly] at st
  have H2 : SemiThue grid_style b' (move_ones b') := equiv_move_ones
  have H3 := SemiThue.trans _ _ _ st H2
  have H := step_two (is_false_to_option to_up_plain_false)
    (by simp [ha, to_option, to_up_plain]) (is_true_to_option to_over_plain_true)
    (by simp [hb, to_option, to_over_plain]) H3
  rcases H with ⟨bot, mid, up, pg, ⟨b'_is⟩⟩
  rcases PartialGrid.middle_frontier_nil_or_caps pg with ⟨⟨mid_nil⟩⟩ | ⟨fm, mm, cm, ⟨problem⟩⟩
  · rw [mid_nil] at pg
    have grid1 := gridt_of_PartialGrid pg
    unfold gridt_option at grid1
    rw [mid_nil, List.append_nil] at b'_is
    have hbot := helper_for_bottom rm b'_is pg.bottom_frontier_is_true
      pg.right_frontier_is_false
    rw [remove_to_option_to_over, remove_to_option_to_up_plain, hbot.1, hbot.2] at grid1
    have H := braid_eq_of_grid (grid_of_gridt grid1)
    convert H
  rw [problem] at b'_is
  exfalso
  have H : in_order (remove_ones b') := by
    rw [rm]
    exact in_order_over_plain_up_plain
  have H1 : in_order (move_ones b') := in_order_move_ones_of_in_order_remove_ones H
  rcases H1 with ⟨a1, a2, a1_true, a2_false, ⟨ha12⟩⟩
  rw [ha12] at b'_is
  rw [← List.append_assoc, List.append_assoc (bot ++ ([(fm, false)] ++ mm))] at b'_is
  rcases List.append_eq_append_iff.mp b'_is with
    ⟨middle, spec1, spec2⟩ | ⟨middle, spec1, spec2⟩
  · rw [spec1] at a1_true
    specialize a1_true (fm, false) ⟨by simp⟩
    simp at a1_true
    exact a1_true.1.elim
  rw [spec2] at a2_false
  specialize a2_false (cm, true) ⟨by simp⟩
  simp at a2_false
  exact a2_false.1.elim

theorem correct_one_dir (h : final_solver a b) : PresentedMonoid.mk braid_rels_m_inf a =
  PresentedMonoid.mk braid_rels_m_inf b := by
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
      rw [← List.append_nil (a1 :: a2), ← List.append_nil (b1 :: b2)]
      apply bm_equiv_of_reversing (by simp) (by simp)
      conv =>
        enter [3]
        rw [to_over_plain, to_up_plain]
        simp
      have H := @solver_equiv (a1 :: a2) (b1 :: b2) (by simp) (by simp)
      rw [h] at H
      exact H

def skeleton_order_to_up_plain_to_over_plain : skeleton_order
  (to_up_plain a ++ to_over_plain b) := by
  use to_up_plain a
  use to_over_plain b
  constructor
  · exact to_up_plain_false
  constructor
  · exact to_over_plain_true
  exact ⟨rfl⟩

-- theorem to_option_append : to_option (a ++ b) = to_option a ++ to_option b := by
--   unfold to_option; simp

theorem eq_of_SemiThue_false (h : SemiThue reversing a b) (ha : is_false a) : a = b := by
  induction h with
  | refl a => rfl
  | reduction h =>
    rcases h
    · rename_i i j hij
      specialize ha (j, true) ⟨by simp⟩
      simp at ha
      exact ha.1.elim
    · rename_i i j hij
      specialize ha (j, true) ⟨by simp⟩
      simp at ha
      exact ha.1.elim
    rename_i i j hij
    specialize ha (j, true) ⟨by simp⟩
    simp at ha
    exact ha.1.elim
  | trans a b c _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

theorem eq_of_SemiThue_true (h : SemiThue reversing a b) (ha : is_true a) : a = b := by
  induction h with
  | refl a => rfl
  | reduction h =>
    rcases h
    · rename_i i j hij
      specialize ha (i, false) ⟨by simp⟩
      simp at ha
      exact ha.1.elim
    · rename_i i j hij
      specialize ha (i, false) ⟨by simp⟩
      simp at ha
      exact ha.1.elim
    rename_i i j hij
    specialize ha (i, false) ⟨by simp⟩
    simp at ha
    exact ha.1.elim
  | trans a b c _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

theorem eq_of_SemiThue_in_order (h : SemiThue reversing a b) (ha : in_order a) : a = b := by
  induction h with
  | refl a => rfl
  | reduction h =>
    rcases ha with ⟨one, two, one_true, two_false, ⟨spec⟩⟩
    rcases h
    · rename_i c d i j hij
      apply Nat.eq_of_dist_eq_zero at hij
      rw [hij]
      rw [hij] at spec
      have spec_rw : c ++ [(j, false), (j, true)] ++ d =
        (c ++ [(j, false)]) ++ ((j, true):: d) := by simp
      rw [spec_rw] at spec
      rcases List.append_eq_append_iff.mp spec with
        ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
      · rw [spec1] at one_true
        specialize one_true (j, false) ⟨by simp⟩
        simp at one_true
        exact one_true.1.elim
      rw [spec2] at two_false
      specialize two_false (j, true) ⟨by simp⟩
      simp at two_false
      exact two_false.1.elim
    · rename_i c d i j hij
      have spec_rw : c ++ [(i, false), (j, true)] ++ d =
        (c ++ [(i, false)]) ++ ((j, true):: d) := by simp
      rw [spec_rw] at spec
      rcases List.append_eq_append_iff.mp spec with
        ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
      · rw [spec1] at one_true
        specialize one_true (i, false) ⟨by simp⟩
        simp at one_true
        exact one_true.1.elim
      rw [spec2] at two_false
      specialize two_false (j, true) ⟨by simp⟩
      simp at two_false
      exact two_false.1.elim
    rename_i c d i j hij
    have spec_rw : c ++ [(i, false), (j, true)] ++ d =
      (c ++ [(i, false)]) ++ ((j, true):: d) := by simp
    rw [spec_rw] at spec
    rcases List.append_eq_append_iff.mp spec with
      ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
    · rw [spec1] at one_true
      specialize one_true (i, false) ⟨by simp⟩
      simp at one_true
      exact one_true.1.elim
    rw [spec2] at two_false
    specialize two_false (j, true) ⟨by simp⟩
    simp at two_false
    exact two_false.1.elim
  | trans a b c _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

noncomputable def step_three (h : SemiThue reversing (to_up_plain a ++ to_over_plain b) cde) :
  Σ c1 d1 e1, PartialGrid (to_up a) (to_over b) c1 d1 e1 × PLift (remove_ones (c1 ++ d1 ++ e1) = cde) := by
  match a with
  | [] =>
    have hb1 : to_over_plain b = cde := by
      simp [to_up_plain] at h
      apply eq_of_SemiThue_true h
      exact to_over_plain_true
    use [], (none, false):: to_over b, []
    constructor
    · simp [to_up]
      apply PartialGrid.empty
      . simp
      · intro a ⟨ha⟩
        simp at ha
        rw [ha]
        exact ⟨rfl⟩
      · exact to_over_len_pos
      exact is_true_over
    constructor
    simp_all [remove_ones, ← hb1]
    exact remove_over_is_plain
  | a1 :: a2 =>
  match b with
  | [] =>
    have ha1 : to_up_plain (a1 :: a2) = cde := by
      simp [to_over_plain] at h
      apply eq_of_SemiThue_false h
      exact to_up_plain_false
    use [], to_up (a1 :: a2) ++ [(none, true)], []
    constructor
    · apply PartialGrid.empty
      . exact to_up_len_pos
      · exact is_false_up
      · exact to_over_len_pos
      exact is_true_over
    constructor
    simp_all [remove_ones, ← ha1]
    exact remove_up_is_plain
  | b1 :: b2 =>
  have H1 := stepOne_mid h skeleton_order_to_up_plain_to_over_plain
  rcases H1 with ⟨b', st, so, ⟨rm⟩⟩
  rw [to_option_append] at st
  have H2 := step_two (is_false_to_option to_up_plain_false) (by simp [to_option, to_up_plain])
    (is_true_to_option to_over_plain_true) (by simp [to_option_length, to_over_plain]) st
  rw [← rm]
  rw [← (to_option_up_plain_eq_up (by simp)), ← to_option_over_plain_eq_over (by simp)]
  rcases H2 with ⟨bot, mid, up, pg, ⟨b'_is⟩⟩
  use bot, mid, up
  use pg
  constructor
  rw [b'_is]

theorem to_up_plain_mul {a b : FreeMonoid ℕ} :
  to_up_plain (a * b) = to_up_plain b ++ to_up_plain a := by
  rw [← to_up_plain_append]
  rfl

theorem to_over_plain_mul {a b : FreeMonoid α} :
  to_over_plain (a * b) = to_over_plain a ++ to_over_plain b := by
  rw [← to_over_plain_append]
  rfl

theorem to_up_append (h : a.length > 0) (hb : b.length > 0) : to_up (a ++ b) = to_up b ++ to_up a := by
  unfold to_up
  aesop

noncomputable def grid_to_rev (h : gridt a b c d) : SemiThue reversing
  (to_up_plain a ++ to_over_plain b) (to_over_plain d ++ to_up_plain c) := by
  induction h with
  | empty => exact SemiThue.refl _
  | top_bottom i => exact SemiThue.refl _
  | sides i => exact SemiThue.refl _
  | top_left i => exact SemiThue_rel (reversing.basic (Nat.dist_eq_zero rfl))
  | adjacent i k h => exact SemiThue_rel (reversing.close h)
  | separated i j h => exact SemiThue_rel (reversing.apart h)
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [to_up_plain_mul, to_up_plain_mul, List.append_assoc]
    apply (SemiThue_append_left h1_ih).trans
    rw [← List.append_assoc, ← List.append_assoc]
    exact SemiThue_append_right h2_ih
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [to_over_plain_mul, to_over_plain_mul, ← List.append_assoc]
    apply (SemiThue_append_right h1_ih).trans
    rw [List.append_assoc, List.append_assoc]
    exact SemiThue_append_left h2_ih

def pg_mid_frontier_reverses_to_grid_extend_both (h : PartialGrid a1 b1 c1 d1 e1) :=
  ∀ {a b f g a2 b2}, (remove_ones a2 ++ remove_ones a1 = to_up_plain a) →
  remove_ones b1 ++ remove_ones b2 = to_over_plain b → a2.length > 0 → is_false a2 →
  b2.length > 0 → is_true b2 → gridt a b f g →
  SemiThue reversing (remove_ones (a2 ++ c1 ++ d1 ++ e1 ++ b2)) (to_over_plain g ++ to_up_plain f)

def pg_mid_frontier_reverses_to_grid_extend_left (h : PartialGrid a1 b1 c1 d1 e1)
  := ∀ {a b f g a2 e2}, (e2 ++ remove_ones e1 = to_up_plain f) →
  (remove_ones a2 ++ remove_ones a1 = to_up_plain a) →
  remove_ones b1 = to_over_plain b → a2.length > 0 → is_false a2 → (h2 : gridt a b f g) →
  SemiThue reversing (remove_ones (a2 ++ c1 ++ d1)) (to_over_plain g ++ e2)

def pg_mid_frontier_reverses_to_grid_extend_top (h : PartialGrid a1 b1 c1 d1 e1) :=
  ∀ {a b f g b2 c2}, remove_ones c1 ++ c2 = to_over_plain g → remove_ones a1 = to_up_plain a →
  remove_ones (b1 ++ b2) = to_over_plain b → b2.length > 0 → is_true b2 → gridt a b f g →
  SemiThue reversing (remove_ones (d1 ++ e1 ++ b2)) (c2 ++ to_up_plain f)

def pg_mid_frontier_reverses_to_grid_extend_neither (h : PartialGrid a1 b1 c1 d1 e1) :=
  ∀ {a b f g c2 e2}, remove_ones c1 ++ c2 = to_over_plain g → e2 ++ remove_ones e1 = to_up_plain f →
  remove_ones a1 = to_up_plain a → remove_ones b1 = to_over_plain b → gridt a b f g →
  SemiThue reversing (remove_ones d1) (c2 ++ e2)

theorem to_over_plain_eq_append_remove_ones (h : to_over_plain a = remove_ones b ++ remove_ones c) :
  a = remover b ++ remover c :=by
    rw [← remover_append]
    symm
    apply remove_eq_of_remove_ones_eq_to_over_plain
    rw [h]
    rw [remove_ones_append]

theorem to_up_plain_eq_append_remove_ones (h : to_up_plain a = remove_ones b ++ remove_ones c) :
  a = remover c.reverse ++ remover b.reverse := by
    rw [← remover_append, ← List.reverse_append]
    symm
    apply remove_rev_eq_remove_ones_eq_to_up_plain
    rw [h]
    rw [remove_ones_append]

theorem to_option_cons : to_option (a :: b) = (some a.1, a.2) :: to_option b := by
  unfold to_option
  simp [to_up_plain, to_over_plain]

theorem remove_ones_to_option : remove_ones (to_option L) = L := by
  induction L with
  | nil => simp [remove_ones, to_option]
  | cons head tail ih =>
    rw [to_option_cons, remove_ones, ih]

noncomputable def all_options_horizontal_append_one (g1 : PartialGrid a b bot [] up)
    (g2 : PartialGrid up b2 bot2 mid2 up2)
    (g1_ih : pg_mid_frontier_reverses_to_grid_extend_both g1 ×
      pg_mid_frontier_reverses_to_grid_extend_left g1 ×
      pg_mid_frontier_reverses_to_grid_extend_top g1 ×
      pg_mid_frontier_reverses_to_grid_extend_neither g1)
    (g2_ih : pg_mid_frontier_reverses_to_grid_extend_both g2 ×
      pg_mid_frontier_reverses_to_grid_extend_left g2 ×
      pg_mid_frontier_reverses_to_grid_extend_top g2 ×
      pg_mid_frontier_reverses_to_grid_extend_neither g2) :
    pg_mid_frontier_reverses_to_grid_extend_both (g1.horizontal_append_one g2) ×
    pg_mid_frontier_reverses_to_grid_extend_left (g1.horizontal_append_one g2) ×
    pg_mid_frontier_reverses_to_grid_extend_top (g1.horizontal_append_one g2) ×
    pg_mid_frontier_reverses_to_grid_extend_neither (g1.horizontal_append_one g2) := by
  repeat any_goals constructor
  · intro e f g i j k l m n no o op p
    have H0 : pg_mid_frontier_reverses_to_grid_extend_left g1 := g1_ih.2.1
    have H0' : pg_mid_frontier_reverses_to_grid_extend_both g2 := g2_ih.1
    have e_is : e = remover (a.reverse) ++ remover (j.reverse) :=
      to_up_plain_eq_append_remove_ones l.symm
    have f_is : f = remover b ++ remover b2 ++ remover k:= by
      rw [← remover_append, ← remover_append]
      rw [← remove_ones_append] at m
      exact eq_remover_of_remove_ones_eq_to_over_plain m
    rw [e_is, f_is, List.append_assoc] at p
    rcases splittable_vertically_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    rcases splittable_horizontally_of_gridt i1 _ _ rfl with
      ⟨c2, d2, e2, i3, i4, ⟨rm1⟩⟩
    have H2 := gridt_of_PartialGrid g1
    have H := unicity_c H2 i3 rfl rfl
    rw [H.1.1] at rm1
    rw [rm1] at i2
    specialize @H0 (remover a.reverse ++ remover j.reverse) (remover b) c1 d1 j (to_up_plain e2)
    rw [rm1, to_up_plain_mul, to_up_plain_remover_rev_eq_remove_ones
      g2.left_frontier_is_false, to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones no, to_up_plain_remover_rev_eq_remove_ones
        g1.left_frontier_is_false, to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true] at H0
    rw [rm1] at i1
    specialize H0 rfl rfl rfl n no i1
    rw [List.append_nil] at H0
    have H01 : SemiThue reversing (remove_ones (j ++ bot)++ remove_ones (bot2 ++ mid2 ++ up2 ++ k))
      (to_over_plain d1 ++ to_up_plain e2 ++ remove_ones (bot2 ++ mid2 ++ up2 ++ k)) :=
      SemiThue_append_right H0
    have : remove_ones (j ++ bot)++ remove_ones (bot2 ++ mid2 ++ up2 ++ k) =
      (remove_ones (j ++ (bot ++ bot2) ++ mid2 ++ up2 ++ k)) := by simp
    rw [this] at H01
    apply H01.trans
    rw [rm, to_over_plain_mul, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
    apply SemiThue_append_left
    have helper1 : remove_ones (to_up e2) ++ remove_ones up = to_up_plain (remover up.reverse ++ FreeMonoid.toList e2) := by
      rw [to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones, List.append_left_inj, remove_up_is_plain]
      rfl
      exact g2.left_frontier_is_false
    have helper2 : remove_ones b2 ++ remove_ones k = to_over_plain ((remover b2) ++ (remover k)) := by
      rw [to_over_plain_append, to_over_plain_remover_eq_remove_ones, List.append_right_inj, to_over_plain_remover_eq_remove_ones op]
      exact g2.top_frontier_is_true
    specialize @H0' (remover up.reverse ++ FreeMonoid.toList e2)
      (Append.append (remover b2) (remover k)) g e1 (to_up e2) k helper1 helper2
        to_up_len_pos is_false_up o op i2
    rw [List.append_assoc, List.append_assoc, List.append_assoc, remove_ones_append, remove_up_is_plain] at H0'
    exact H0'
  · intro e f g i j k l m n o op p
    have H0 : pg_mid_frontier_reverses_to_grid_extend_left g1 := g1_ih.2.1
    have H0' : pg_mid_frontier_reverses_to_grid_extend_left g2 := g2_ih.2.1
    have e_is : e = remover (a.reverse) ++ remover (j.reverse) := by
      rw [← remover_append, ← List.reverse_append]
      symm
      apply remove_rev_eq_remove_ones_eq_to_up_plain
      rw [← m]
      rw [remove_ones_append]
    have f_is : f = remover b ++ remover b2 := by
      rw [← remover_append]
      exact eq_remover_of_remove_ones_eq_to_over_plain n
    rw [e_is, f_is] at p
    rcases splittable_vertically_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    rcases splittable_horizontally_of_gridt i1 _ _ rfl with
      ⟨c2, d2, e2, i3, i4, ⟨rm1⟩⟩
    have H2 := gridt_of_PartialGrid g1
    have H := unicity_c H2 i3 rfl rfl
    rw [H.2.1] at i3 i4
    rw [H.1.1] at i3 rm1
    specialize @H0 (remover a.reverse ++ remover j.reverse) (remover b) c1 d1 j (to_up_plain e2)
    rw [rm1, to_up_plain_mul, to_up_plain_remover_rev_eq_remove_ones
      g2.left_frontier_is_false] at H0
    specialize H0 rfl
    rw [to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones op, to_up_plain_remover_rev_eq_remove_ones
      g1.left_frontier_is_false, to_over_plain_remover_eq_remove_ones
        g1.top_frontier_is_true] at H0
    specialize H0 rfl rfl o op
    rw [rm1] at i1
    specialize H0 i1
    rw [List.append_nil] at H0
    have H01 : SemiThue reversing (remove_ones (j ++ bot)++ remove_ones (bot2++mid2))
      (to_over_plain d1 ++ to_up_plain e2 ++ remove_ones (bot2++mid2)) :=
      SemiThue_append_right H0
    rw [← remove_ones_append, ← List.append_assoc, List.append_assoc j bot bot2] at H01
    apply H01.trans
    rw [rm, to_over_plain_mul, List.append_assoc, List.append_assoc]
    apply SemiThue_append_left
    unfold pg_mid_frontier_reverses_to_grid_extend_left at H0'
    specialize @H0' c1 (remover b2) g e1 (to_up e2) k l
    rw [rm1, to_up_plain_mul, to_up_plain_remover_rev_eq_remove_ones
      g2.left_frontier_is_false, List.append_left_inj, remove_up_is_plain,
      List.append_assoc] at H0'
    have h1 : remove_ones b2 = to_over_plain (remover b2) := by
      rw [to_over_plain_remover_eq_remove_ones]
      exact g2.top_frontier_is_true
    rw [rm1] at i2
    specialize @H0' rfl h1 to_up_len_pos is_false_up i2
    convert H0'
    conv =>
      enter [2]
      rw [remove_ones_append]
    rw [List.append_left_inj]
    exact remove_up_is_plain.symm
  · intro e f g i j k l m n o op p
    have H0 : pg_mid_frontier_reverses_to_grid_extend_top g2 := g2_ih.2.2.1
    unfold pg_mid_frontier_reverses_to_grid_extend_top at H0
    have H2 := gridt_of_PartialGrid g1
    unfold gridt_option at H2
    have he : e = remover (a.reverse) := by
      exact Eq.symm (remove_rev_eq_remove_ones_eq_to_up_plain m)
    rw [he] at p
    have hf : f = remover b ++ (remover b2 ++ remover j) := by
      rw [← remover_append, ← remover_append, ← List.append_assoc]
      exact eq_remover_of_remove_ones_eq_to_over_plain n
    rw [hf] at p
    rcases splittable_vertically_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H := unicity_c H2 i1 rfl rfl
    rw [H.1.1] at i2
    rw [H.2.1] at rm
    rw [rm, remove_ones_append, to_over_plain_mul,
      to_over_plain_remover_eq_remove_ones g1.bottom_frontier_is_true, List.append_assoc,
      List.append_right_inj] at l
    specialize @H0 (remover up.reverse) ((Append.append (remover b2) (remover j))) g e1 j k l
    apply H0 _ _ o op i2
    · rw [to_up_plain_remover_rev_eq_remove_ones]
      exact g2.left_frontier_is_false
    change _ = to_over_plain (_ ++ _)
    rw [to_over_plain_append, remove_ones_append,
      to_over_plain_remover_eq_remove_ones op, to_over_plain_remover_eq_remove_ones g2.top_frontier_is_true]
  · intro e f g i j k l m n o p
    have H0 : pg_mid_frontier_reverses_to_grid_extend_neither g2 := g2_ih.2.2.2
    unfold pg_mid_frontier_reverses_to_grid_extend_neither at H0
    have H2 := gridt_of_PartialGrid g1
    unfold gridt_option at H2
    have he : e = remover (a.reverse) := by
      exact Eq.symm (remove_rev_eq_remove_ones_eq_to_up_plain n)
    rw [he] at p
    have hf : f = remover b ++ remover b2  := by
      rw [← remover_append]
      exact eq_remover_of_remove_ones_eq_to_over_plain o
    rw [hf] at p
    rcases splittable_vertically_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H := unicity_c H2 i1 rfl rfl
    rw [H.1.1] at i2
    rw [H.2.1] at rm
    rw [rm, remove_ones_append, to_over_plain_mul,
      to_over_plain_remover_eq_remove_ones g1.bottom_frontier_is_true, List.append_assoc,
      List.append_right_inj] at l
    specialize @H0 (remover up.reverse) (remover b2) g e1 j k
    apply H0 l m _ _ i2
    · rw [to_up_plain_remover_rev_eq_remove_ones]
      exact g2.left_frontier_is_false
    rw [to_over_plain_remover_eq_remove_ones]
    exact g2.top_frontier_is_true

noncomputable def all_options_vertical_append_one (g1 : PartialGrid a b bot [] up)
    (g2 : PartialGrid a1 bot bot2 mid2 up2)
    (g1_ih : pg_mid_frontier_reverses_to_grid_extend_both g1 ×
      pg_mid_frontier_reverses_to_grid_extend_left g1 ×
      pg_mid_frontier_reverses_to_grid_extend_top g1 ×
      pg_mid_frontier_reverses_to_grid_extend_neither g1)
    (g2_ih : pg_mid_frontier_reverses_to_grid_extend_both g2 ×
      pg_mid_frontier_reverses_to_grid_extend_left g2 ×
      pg_mid_frontier_reverses_to_grid_extend_top g2 ×
      pg_mid_frontier_reverses_to_grid_extend_neither g2) :
    pg_mid_frontier_reverses_to_grid_extend_both (g1.vertical_append_one g2) ×
    pg_mid_frontier_reverses_to_grid_extend_left (g1.vertical_append_one g2) ×
    pg_mid_frontier_reverses_to_grid_extend_top (g1.vertical_append_one g2) ×
    pg_mid_frontier_reverses_to_grid_extend_neither (g1.vertical_append_one g2) := by
  repeat any_goals constructor
  · intro e f g i j k l m n no o op p
    have H0 : pg_mid_frontier_reverses_to_grid_extend_top g1 := g1_ih.2.2.1
    have e_is : e = remover (a.reverse) ++ remover (a1.reverse) ++ remover j.reverse := by
      rw [← remover_append, ← remover_append, ← List.reverse_append, ← List.reverse_append]
      symm
      apply remove_rev_eq_remove_ones_eq_to_up_plain
      rw [← l, remove_ones_append]
    have f_is : f = remover b ++ remover k := by
      rw [← remover_append]
      rw [← remove_ones_append] at m
      exact eq_remover_of_remove_ones_eq_to_over_plain m
    rw [e_is, f_is, List.append_assoc] at p
    rcases splittable_horizontally_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    rcases splittable_vertically_of_gridt i1 _ _ rfl with
      ⟨c2, d2, e2, i3, i4, ⟨rm1⟩⟩
    have H2 := gridt_of_PartialGrid g1
    have H := unicity_c H2 i3 rfl rfl
    rw [H.1.1] at i3 i4
    rw [H.2.1] at i3 rm1
    rw [rm1] at i1
    have helper1 : remove_ones bot ++ to_over_plain e2 = to_over_plain (remover bot ++ FreeMonoid.toList e2) := by
      rw [to_over_plain_append, to_over_plain_remover_eq_remove_ones, List.append_right_inj]
      rfl
      exact g2.top_frontier_is_true
    have helper2 : remove_ones a = to_up_plain (remover a.reverse) := by
      rw [to_up_plain_remover_rev_eq_remove_ones]
      exact g1.left_frontier_is_false
    have helper3 : remove_ones (b ++ k) = to_over_plain (remover b ++ remover k) := by
      rw [to_over_plain_append, to_over_plain_remover_eq_remove_ones,
        to_over_plain_remover_eq_remove_ones op, remove_ones_append]
      exact g1.top_frontier_is_true
    specialize @H0 (remover a.reverse) (remover b ++ remover k) d1
      (remover bot ++ FreeMonoid.toList e2) k (to_over_plain e2) helper1 helper2 helper3 o op i1
    rw [List.nil_append] at H0
    apply @SemiThue_append_left _ _ _ _  (remove_ones (j ++ bot2 ++ mid2 ++ up2)) at H0
    rw [← remove_ones_append, List.append_assoc, List.append_assoc, List.append_assoc] at H0
    rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
    apply H0.trans
    rw [rm, to_up_plain_mul, ← List.append_assoc, ← List.append_assoc]
    apply SemiThue_append_right
    have H0' : pg_mid_frontier_reverses_to_grid_extend_both g2 := g2_ih.1
    rw [rm1] at i2
    specialize @H0' (Append.append (remover a1.reverse) (remover j.reverse))
      (remover bot ++ FreeMonoid.toList e2) e1 i j (to_over e2)
    have : (remove_ones (j ++ bot2 ++ mid2 ++ up2 ++ to_over e2)) = (remove_ones (j ++ bot2 ++ mid2 ++ up2) ++ to_over_plain e2) := by
      rw [remove_ones_append, List.append_right_inj]
      exact remove_over_is_plain
    rw [this] at H0'
    apply H0' _ _ n no to_over_len_pos is_true_over i2
    · change _ = to_up_plain (_ ++ _)
      rw [to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones no,
        to_up_plain_remover_rev_eq_remove_ones g2.left_frontier_is_false]
    rw [to_over_plain_append, to_over_plain_remover_eq_remove_ones g2.top_frontier_is_true,
      List.append_right_inj, remove_over_is_plain]
    rfl
  · intro e f g i j k l m n o op p
    have H0 : pg_mid_frontier_reverses_to_grid_extend_left g2 := g2_ih.2.1
    have e_is : e = remover (a.reverse) ++ remover (a1.reverse) ++ remover (j.reverse) := by
      rw [← remover_append, ← remover_append, ← List.reverse_append, ← List.reverse_append]
      symm
      apply remove_rev_eq_remove_ones_eq_to_up_plain
      rw [← m]
      rw [remove_ones_append]
    have f_is : f = remover b := by
      exact eq_remover_of_remove_ones_eq_to_over_plain n
    rw [e_is, f_is, List.append_assoc] at p
    rcases splittable_horizontally_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H2 := gridt_of_PartialGrid g1
    have H := unicity_c H2 i1 rfl rfl
    rw [H.1.1] at rm
    rw [H.2.1] at i2
    apply @H0 (Append.append (remover a1.reverse) (remover j.reverse)) (remover bot) e1 i j k _ _ _ o op i2
    · rw [rm, to_up_plain_mul, to_up_plain_remover_rev_eq_remove_ones g1.right_frontier_is_false,
        remove_ones_append, ← List.append_assoc, List.append_left_inj] at l
      exact l
    · change _ = to_up_plain (_ ++ _)
      rw [to_up_plain_append,
        to_up_plain_remover_rev_eq_remove_ones op, to_up_plain_remover_rev_eq_remove_ones g2.left_frontier_is_false]
    rw [to_over_plain_remover_eq_remove_ones]
    exact g2.top_frontier_is_true
  · intro e f g i j k l m n o op p
    have H0 : pg_mid_frontier_reverses_to_grid_extend_top g1 := g1_ih.2.2.1
    have e_is : e = remover (a.reverse) ++ remover (a1.reverse) := by
      rw [← remover_append, ← List.reverse_append]
      symm
      apply remove_rev_eq_remove_ones_eq_to_up_plain
      rw [← m]
    have f_is : f = remover b ++ remover j := by
      rw [← remover_append]
      exact eq_remover_of_remove_ones_eq_to_over_plain n
    rw [e_is, f_is] at p
    rcases splittable_horizontally_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    rcases splittable_vertically_of_gridt i1 _ _ rfl with
      ⟨c2, d2, e2, i3, i4, ⟨rm1⟩⟩
    have H2 := gridt_of_PartialGrid g1
    have H := unicity_c H2 i3 rfl rfl
    rw [H.1.1] at i3 i4
    rw [H.2.1] at i3 rm1
    rw [rm1] at i1
    have helper1 : remove_ones bot ++ to_over_plain e2 = to_over_plain (remover bot ++ FreeMonoid.toList e2) := by
      rw [to_over_plain_append, to_over_plain_remover_eq_remove_ones, List.append_right_inj]
      rfl
      exact g2.top_frontier_is_true
    have helper2 : remove_ones a = to_up_plain (remover a.reverse) := by
      rw [to_up_plain_remover_rev_eq_remove_ones]
      exact g1.left_frontier_is_false
    have helper3 : remove_ones (b ++ j) = to_over_plain (remover b ++ remover j) := by
      rw [to_over_plain_append, to_over_plain_remover_eq_remove_ones,
        to_over_plain_remover_eq_remove_ones op, remove_ones_append]
      exact g1.top_frontier_is_true
    specialize @H0 (remover a.reverse) (remover b ++ remover j) d1
      (remover bot ++ FreeMonoid.toList e2) j (to_over_plain e2) helper1 helper2 helper3 o op i1
    rw [List.nil_append] at H0
    apply @SemiThue_append_left _ _ _ _  (remove_ones (mid2 ++ up2)) at H0
    rw [← remove_ones_append, List.append_assoc] at H0
    rw [List.append_assoc, List.append_assoc]
    apply H0.trans
    rw [rm, to_up_plain_mul, ← List.append_assoc, ← List.append_assoc]
    apply SemiThue_append_right
    have H0' : pg_mid_frontier_reverses_to_grid_extend_top g2 := g2_ih.2.2.1
    rw [rm1] at i2
    specialize @H0' (remover a1.reverse) (remover bot ++ FreeMonoid.toList e2) e1 i (to_over e2) k
    have : (remove_ones (mid2 ++ up2 ++ to_over e2)) = (remove_ones (mid2 ++ up2) ++ to_over_plain e2) := by
      rw [remove_ones_append, List.append_right_inj]
      exact remove_over_is_plain
    rw [this] at H0'
    apply H0' l (to_up_plain_remover_rev_eq_remove_ones g2.left_frontier_is_false).symm _ to_over_len_pos is_true_over i2
    rw [remove_ones_append, to_over_plain_append, to_over_plain_remover_eq_remove_ones
        g2.top_frontier_is_true, List.append_right_inj, remove_over_is_plain]
    rfl
  · intro e f g i j k l m n o p
    have H0 : pg_mid_frontier_reverses_to_grid_extend_neither g2 := g2_ih.2.2.2
    unfold pg_mid_frontier_reverses_to_grid_extend_neither at H0
    have H2 := gridt_of_PartialGrid g1
    unfold gridt_option at H2
    have he : f = remover (b) := eq_remover_of_remove_ones_eq_to_over_plain o
    rw [he] at p
    have hf : e = remover (List.reverse a) ++ remover (List.reverse a1)  := by
      apply to_up_plain_eq_append_remove_ones
      rw [remove_ones_append] at n
      exact n.symm
    rw [hf] at p
    rcases splittable_horizontally_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H := unicity_c H2 i1 rfl rfl
    rw [H.2.1] at i2
    rw [H.1.1] at rm
    rw [rm, remove_ones_append, to_up_plain_mul,
      to_up_plain_remover_rev_eq_remove_ones g1.right_frontier_is_false, ← List.append_assoc,
      List.append_left_inj] at m
    specialize @H0 (remover a1.reverse) (remover bot) e1 i j k
    apply H0 l m _ _ i2
    · rw [to_up_plain_remover_rev_eq_remove_ones]
      exact g2.left_frontier_is_false
    rw [to_over_plain_remover_eq_remove_ones]
    exact g2.top_frontier_is_true

noncomputable def all_options_horizontal_append (h : mid.length > 0)
    (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid up b2 bot2 mid2 up2)
    (g1_ih : pg_mid_frontier_reverses_to_grid_extend_both g1 ×
      pg_mid_frontier_reverses_to_grid_extend_left g1 ×
      pg_mid_frontier_reverses_to_grid_extend_top g1 ×
      pg_mid_frontier_reverses_to_grid_extend_neither g1)
    (g2_ih : pg_mid_frontier_reverses_to_grid_extend_both g2 ×
      pg_mid_frontier_reverses_to_grid_extend_left g2 ×
      pg_mid_frontier_reverses_to_grid_extend_top g2 ×
      pg_mid_frontier_reverses_to_grid_extend_neither g2) :
    pg_mid_frontier_reverses_to_grid_extend_both (PartialGrid.horizontal_append h g1 g2) ×
    pg_mid_frontier_reverses_to_grid_extend_left (PartialGrid.horizontal_append h g1 g2) ×
    pg_mid_frontier_reverses_to_grid_extend_top (PartialGrid.horizontal_append h g1 g2) ×
    pg_mid_frontier_reverses_to_grid_extend_neither (PartialGrid.horizontal_append h g1 g2) := by
  repeat any_goals constructor
  · intro e f g i j k l m n no o op p
    have e_is : e = remover (a.reverse) ++ remover (j.reverse) := by
      rw [← remover_append, ← List.reverse_append]
      symm
      apply remove_rev_eq_remove_ones_eq_to_up_plain
      rw [← l, remove_ones_append]
    have f_is : f = remover b ++ (remover b2 ++ remover k):= by
      rw [← remover_append, ← remover_append]
      rw [← remove_ones_append, List.append_assoc] at m
      exact eq_remover_of_remove_ones_eq_to_over_plain m
    rw [e_is, f_is] at p
    rcases splittable_vertically_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H0 : pg_mid_frontier_reverses_to_grid_extend_left g1 := g1_ih.2.1
    have long := PartialGrid.extend_bottom g1 j no (fun h => by simp [h] at n)
    have H := (same_time_c i1 long).2
      (to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true).symm
      (by rw [remove_ones_append, to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones no,
        to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false]; exact
        List.suffix_refl_C)
    have H1 := (same_time_c i1 long).1
      (by rw [remove_ones_append, to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones no,
        List.append_right_inj, to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false])
      (by rw [to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true]; exact
        List.prefix_refl_C)
    rcases H with ⟨d2, ⟨hd2⟩⟩
    rcases H1 with ⟨d3, ⟨hd3⟩⟩
    specialize @H0 (remover a.reverse ++ remover j.reverse) (remover b) c1 d1 j d2
      hd2 (by rw [to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones no,
        to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false]) (to_over_plain_remover_eq_remove_ones
          g1.top_frontier_is_true).symm n no i1
    apply @SemiThue_append_right _ _ _ _ (remove_ones (bot2 ++ mid2 ++ up2 ++ k)) at H0
    simp [remove_ones_append] at H0
    simp [remove_ones_append]
    apply H0.trans
    rw [rm, to_over_plain_mul, List.append_assoc]
    apply SemiThue_append_left
    have H0' : pg_mid_frontier_reverses_to_grid_extend_both g2 := g2_ih.1
    have helper1 : remove_ones (to_option d2 ++ [(none, false)]) ++ remove_ones up = to_up_plain c1 := by
      rw [remove_ones_append, remove_ones_to_option, remove_ones, remove_ones_nil, List.append_nil, hd2]
    have helper2 : is_false (to_option d2 ++ [(none, false)]) := by
      apply is_false_of_false_false
      · apply is_false_to_option
        have H : is_false (to_up_plain c1) := to_up_plain_false
        rw [← hd2] at H
        apply is_false_append at H
        exact H.1
      · exact is_false_cons [] is_false_nil
    have helper3 : is_true (k ++ [(none, true)]) := is_true_of_true_true op (is_true_cons [] is_true_nil)
    specialize @H0' c1 (remover b2 ++ remover k) g e1  (to_option d2 ++ [(none, false)]) (k ++ [(none, true)]) helper1
      (by rw [to_over_plain_append, remove_ones_append, remove_ones, remove_ones_nil, List.append_nil,
        to_over_plain_remover_eq_remove_ones g2.top_frontier_is_true,
        to_over_plain_remover_eq_remove_ones op])
      (by simp) helper2 (by simp) helper3 i2
    have : (remove_ones (to_option d2 ++ [(none, false)] ++ bot2 ++ mid2 ++ up2 ++ (k ++ [(none, true)]))) =
      (d2 ++ (remove_ones bot2 ++ (remove_ones mid2 ++ (remove_ones up2 ++ remove_ones k)))) := by
      simp [remove_ones_append, remove_ones_to_option, remove_ones]
    rw [this] at H0'
    exact H0'
  · intro e f g i j k l m n o op p
    have e_is : e = remover (a.reverse) ++ remover (j.reverse) := by
      rw [← remover_append, ← List.reverse_append]
      symm
      apply remove_rev_eq_remove_ones_eq_to_up_plain
      rw [← m, remove_ones_append]
    have f_is : f = remover b ++ remover b2 := by
      rw [← remover_append]
      exact eq_remover_of_remove_ones_eq_to_over_plain n
    rw [e_is, f_is] at p
    rcases splittable_vertically_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H0 : pg_mid_frontier_reverses_to_grid_extend_left g1 := g1_ih.2.1
    have long := PartialGrid.extend_bottom g1 j op (fun h => by simp [h] at o)
    have H := (same_time_c i1 long).2
      (to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true).symm
      (by rw [to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones op, remove_ones_append,
      to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false]; exact
        List.suffix_refl_C)
    have H1 := (same_time_c i1 long).1
      (by rw [remove_ones_append, to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false,
        to_up_plain_remover_rev_eq_remove_ones op])
      (by rw [to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true]; exact
        List.prefix_refl_C)
    rcases H with ⟨d2, ⟨hd2⟩⟩
    rcases H1 with ⟨d3, ⟨hd3⟩⟩
    specialize @H0 (remover a.reverse ++ remover j.reverse) (remover b) c1 d1 j d2
      hd2 (by rw [to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones op,
        to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false]) (to_over_plain_remover_eq_remove_ones
          g1.top_frontier_is_true).symm o op i1
    apply @SemiThue_append_right _ _ _ _ (remove_ones (bot2 ++ mid2)) at H0
    simp [remove_ones_append] at H0
    simp [remove_ones_append]
    apply H0.trans
    rw [rm, to_over_plain_mul, List.append_assoc]
    apply SemiThue_append_left
    have H0' : pg_mid_frontier_reverses_to_grid_extend_left g2 := g2_ih.2.1
    have helper1 : remove_ones (to_option d2 ++ [(none, false)]) ++ remove_ones up = to_up_plain c1 := by
      rw [remove_ones_append, remove_ones_to_option, remove_ones, remove_ones_nil, List.append_nil, hd2]
    have helper2 : is_false (to_option d2 ++ [(none, false)]) := by
      apply is_false_of_false_false
      · apply is_false_to_option
        have H : is_false (to_up_plain c1) := to_up_plain_false
        rw [← hd2] at H
        apply is_false_append at H
        exact H.1
      · exact is_false_cons [] is_false_nil
    specialize @H0' c1 (remover b2) g e1 (to_option d2 ++ [(none, false)]) k l helper1
      (to_over_plain_remover_eq_remove_ones g2.top_frontier_is_true).symm (by simp) helper2 i2
    have : (remove_ones (to_option d2 ++ [(none, false)] ++ bot2 ++ mid2))  = (d2 ++ (remove_ones bot2 ++ remove_ones mid2)) := by
      simp [remove_ones_append, remove_ones_to_option, remove_ones]
    rw [this] at H0'
    exact H0'
  · intro e f g i j k l m n o op p
    have e_is : e = remover a.reverse := (remove_rev_eq_remove_ones_eq_to_up_plain m).symm
    have f_is : f = remover b ++ (remover b2 ++ remover j) := by
      rw [← List.append_assoc, ← remover_append, ← remover_append]
      exact eq_remover_of_remove_ones_eq_to_over_plain n
    rw [e_is, f_is] at p
    rcases splittable_vertically_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H := (same_time_c i1 g1).1 (to_up_plain_remover_rev_eq_remove_ones
      g1.left_frontier_is_false).symm (by rw [to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true]; exact
        List.prefix_refl_C)
    have H2 := (same_time_c i1 g1).2 (to_over_plain_remover_eq_remove_ones (by exact
      g1.top_frontier_is_true)).symm
        (by rw [to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false]; exact List.suffix_refl_C)
    rcases H with ⟨d2, ⟨hd2⟩⟩
    rcases H2 with ⟨d3, ⟨hd3⟩⟩
    have H0 : pg_mid_frontier_reverses_to_grid_extend_neither g1 := g1_ih.2.2.2
    specialize @H0 (remover a.reverse) (remover b) c1 d1 d2 d3 hd2 hd3
      (to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false).symm
      (to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true).symm i1
    apply @SemiThue_append_right _ _ _ _ (remove_ones (bot2 ++ mid2 ++ up2 ++ j)) at H0
    rw [← remove_ones_append, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at H0
    apply H0.trans
    have k_is : k = d2 ++ to_over_plain e1 := by
      rw [rm, to_over_plain_mul, ← hd2, List.append_assoc, List.append_right_inj] at l
      exact l
    rw [k_is, List.append_assoc, List.append_assoc d2]
    apply SemiThue_append_left
    have H0' : pg_mid_frontier_reverses_to_grid_extend_both g2 := g2_ih.1
    specialize @H0' c1 (Append.append (remover b2) (remover j)) g e1 (to_option d3 ++ [(none, false)]) j
    simp [remove_ones_append, remove_ones, ← hd3, remove_ones_to_option] at H0'
    simp [remove_ones_append]
    apply H0' trivial _ trivial _ o op i2
    · change _ = to_over_plain (_ ++ _)
      rw [to_over_plain_append, to_over_plain_remover_eq_remove_ones g2.top_frontier_is_true,
        List.append_right_inj, to_over_plain_remover_eq_remove_ones op]
    apply is_false_of_false_false
    · apply is_false_to_option
      have H : is_false (to_up_plain c1) := to_up_plain_false
      rw [← hd3] at H
      apply is_false_append at H
      exact H.1
    · exact is_false_cons [] is_false_nil
  intro e f g i j k l m n o p
  have e_is : e = remover a.reverse := (remove_rev_eq_remove_ones_eq_to_up_plain n).symm
  have f_is : f = remover b ++ remover b2 := by
    rw [remove_ones_append] at o
    apply to_over_plain_eq_append_remove_ones o.symm
  rw [e_is, f_is] at p
  rcases splittable_vertically_of_gridt p _ _ rfl
    with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
  have H := (same_time_c i1 g1).1 (to_up_plain_remover_rev_eq_remove_ones
    g1.left_frontier_is_false).symm (by rw [to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true]; exact
      List.prefix_refl_C)
  have H2 := (same_time_c i1 g1).2 (to_over_plain_remover_eq_remove_ones (by exact
    g1.top_frontier_is_true)).symm
    (by rw [to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false]; exact List.suffix_refl_C)
  rcases H with ⟨d2, ⟨hd2⟩⟩
  rcases H2 with ⟨d3, ⟨hd3⟩⟩
  have H0 : pg_mid_frontier_reverses_to_grid_extend_neither g1 := g1_ih.2.2.2
  specialize @H0 (remover a.reverse) (remover b) c1 d1 d2 d3 hd2 hd3
    (to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false).symm
    (to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true).symm i1
  apply @SemiThue_append_right _ _ _ _ (remove_ones (bot2 ++ mid2)) at H0
  rw [← remove_ones_append, ← List.append_assoc] at H0
  apply H0.trans
  rw [rm, to_over_plain_mul, ← hd2, List.append_assoc, List.append_right_inj] at l
  rw [l, List.append_assoc, List.append_assoc]
  apply SemiThue_append_left
  have H0' : pg_mid_frontier_reverses_to_grid_extend_left g2 := g2_ih.2.1
  specialize @H0' c1 (remover b2) g e1 (to_option d3 ++ [(none, false)]) k m
  rw [remove_ones_append, remove_ones, remove_ones_nil, List.append_nil, remove_ones_to_option,
    to_over_plain_remover_eq_remove_ones g2.top_frontier_is_true] at H0'
  have d3_false : is_false d3 := by
    have H : is_false (to_up_plain c1) := to_up_plain_false
    rw [← hd3] at H
    apply is_false_append at H
    exact H.1
  specialize H0' hd3 rfl (by simp) (is_false_of_false_false (is_false_to_option d3_false)
    (is_false_cons [] is_false_nil)) i2
  simp only [List.append_assoc, List.cons_append, List.nil_append, remove_ones_append,
    remove_ones] at H0'
  simp only [remove_ones_append]
  rw [remove_ones_to_option] at H0'
  exact H0'

noncomputable def all_options_vertical_append (g1 : PartialGrid a b bot mid up)
    (g2 : PartialGrid a1 bot bot2 mid2 up2) (h : mid.length > 0)
    (g1_ih : pg_mid_frontier_reverses_to_grid_extend_both g1 ×
      pg_mid_frontier_reverses_to_grid_extend_left g1 ×
      pg_mid_frontier_reverses_to_grid_extend_top g1 ×
      pg_mid_frontier_reverses_to_grid_extend_neither g1)
    (g2_ih : pg_mid_frontier_reverses_to_grid_extend_both g2 ×
      pg_mid_frontier_reverses_to_grid_extend_left g2 ×
      pg_mid_frontier_reverses_to_grid_extend_top g2 ×
      pg_mid_frontier_reverses_to_grid_extend_neither g2) :
    pg_mid_frontier_reverses_to_grid_extend_both (g1.vertical_append g2 h) ×
    pg_mid_frontier_reverses_to_grid_extend_left (g1.vertical_append g2 h) ×
    pg_mid_frontier_reverses_to_grid_extend_top (g1.vertical_append g2 h) ×
    pg_mid_frontier_reverses_to_grid_extend_neither (g1.vertical_append g2 h) := by
  repeat any_goals constructor
  · intro e f g i j k l m n no o op p
    have e_is : e = remover a.reverse ++ (remover a1.reverse ++ remover j.reverse):= by
      rw [← List.append_assoc, ← remover_append, ← List.reverse_append, ← remover_append, ← List.reverse_append]
      symm
      apply remove_rev_eq_remove_ones_eq_to_up_plain
      rw [← l, remove_ones_append]
    have f_is : f = remover b ++ remover k := by
      rw [← remover_append]
      rw [← remove_ones_append] at m
      exact eq_remover_of_remove_ones_eq_to_over_plain m
    rw [e_is, f_is] at p
    rcases splittable_horizontally_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H := (same_time_c i1 g1).1 (to_up_plain_remover_rev_eq_remove_ones
      g1.left_frontier_is_false).symm (by rw [to_over_plain_append,
        to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true]; exact
          List.prefix_append_self_C)
    rcases H with ⟨d2, ⟨hd2⟩⟩
    have H0 : pg_mid_frontier_reverses_to_grid_extend_top g1 := g1_ih.2.2.1
    specialize @H0 (remover a.reverse) (remover b ++ remover k) d1 c1 k d2 hd2
      (to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false).symm
      (by rw [remove_ones_append, to_over_plain_append,
        to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true, to_over_plain_remover_eq_remove_ones op]) o op i1
    apply @SemiThue_append_left _ _ _ _ (remove_ones (j ++ bot2 ++ mid2 ++ up2)) at H0
    simp [remove_ones_append] at H0
    simp [remove_ones_append]
    apply H0.trans
    rw [rm, to_up_plain_mul, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    apply SemiThue_append_right
    have H0' : pg_mid_frontier_reverses_to_grid_extend_both g2 := g2_ih.1
    have is_true_d2 : is_true (to_option d2 ++ [(none, true)]) := by
      apply is_true_of_true_true
      · have H : is_true (to_over_plain c1) := to_over_plain_true
        rw [← hd2] at H
        apply is_true_append at H
        apply is_true_to_option
        exact H.2
      exact is_true_cons [] is_true_nil
    have helper1 : remove_ones (bot ++ (to_option d2 ++ [(none, true)])) = to_over_plain c1 := by
      simp [remove_ones, remove_ones_to_option, hd2]
    have helper2 : remove_ones j ++ remove_ones a1 = to_up_plain ((remover a1.reverse) ++ (remover j.reverse)) := by
      rw [to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones g2.left_frontier_is_false,
        to_up_plain_remover_rev_eq_remove_ones no]
    have dt : is_true (to_option d2 ++ [(none, true)]):= by
      apply is_true_of_true_true
      · have H : is_true (to_over_plain c1) := to_over_plain_true
        rw [← hd2] at H
        apply is_true_append at H
        apply is_true_to_option
        exact H.2
      exact is_true_cons [] is_true_nil
    specialize @H0' ((remover a1.reverse) ++ (remover j.reverse)) c1 e1 i j
        (to_option d2 ++ [(none, true)]) (by rw [to_up_plain_append,
        to_up_plain_remover_rev_eq_remove_ones g2.left_frontier_is_false,
        to_up_plain_remover_rev_eq_remove_ones no]) (by rw [remove_ones_append,
        remove_ones_to_option, remove_ones, remove_ones_nil, List.append_nil, hd2]) n no
        (by simp [to_option_length]) dt i2
    simp only [List.append_assoc, remove_ones_append, remove_ones_to_option, remove_ones,
      List.append_nil] at H0'
    simp only [List.append_assoc]
    exact H0'
  · intro e f g i j k l m n o op p
    have e_is : e = remover a.reverse ++ (remover a1.reverse ++ remover j.reverse):= by
      rw [← List.append_assoc, ← remover_append, ← List.reverse_append, ← remover_append, ← List.reverse_append]
      symm
      apply remove_rev_eq_remove_ones_eq_to_up_plain
      rw [← m, remove_ones_append]
    have f_is : f = remover b := eq_remover_of_remove_ones_eq_to_over_plain n
    rw [e_is, f_is] at p
    rcases splittable_horizontally_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H := (same_time_c i1 g1).1 (to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false).symm
      (by rw [to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true]; exact
        List.prefix_refl_C)
    have H2 := (same_time_c i1 g1).2 (to_over_plain_remover_eq_remove_ones (by exact
      g1.top_frontier_is_true)).symm
      (by rw [to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false]; exact List.suffix_refl_C)
    rcases H with ⟨d2, ⟨hd2⟩⟩
    rcases H2 with ⟨d3, ⟨hd3⟩⟩
    have H0 : pg_mid_frontier_reverses_to_grid_extend_neither g1 := g1_ih.2.2.2
    specialize @H0 (remover a.reverse) (remover b) d1 c1 d2 d3 hd2 hd3
      (to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false).symm
      (to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true).symm i1
    apply @SemiThue_append_left _ _ _ _ (remove_ones (j ++ bot2 ++ mid2++up2)) at H0
    rw [← remove_ones_append, ← List.append_assoc] at H0
    rw [← List.append_assoc, ← List.append_assoc]
    apply H0.trans
    rw [rm, to_up_plain_mul, ← hd3, ← List.append_assoc, List.append_left_inj] at l
    rw [l, ← List.append_assoc]
    apply SemiThue_append_right
    have H0' : pg_mid_frontier_reverses_to_grid_extend_both g2 := g2_ih.1
    specialize @H0' (Append.append (remover a1.reverse) (remover j.reverse)) c1 e1 i j (to_option d2 ++ [(none, true)])
    rw [remove_ones_append, remove_ones_append, remove_ones, remove_ones_nil, List.append_nil, remove_ones_to_option] at H0'
    have helper1 : is_true (to_option d2 ++ [(none, true)]) := by
      apply is_true_of_true_true
      · have H : is_true (to_over_plain c1) := to_over_plain_true
        rw [← hd2] at H
        apply is_true_append at H
        apply is_true_to_option
        exact H.2
      exact is_true_cons [] is_true_nil
    have helper2 : remove_ones j ++ remove_ones a1 = to_up_plain (Append.append (remover a1.reverse) (remover j.reverse)) := by
      change _ = to_up_plain (_++_)
      rw [to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones g2.left_frontier_is_false,
        to_up_plain_remover_rev_eq_remove_ones op]
    specialize H0' helper2 hd2 o op (by simp) helper1 i2
    simp only [List.append_assoc, List.cons_append, List.nil_append, remove_ones_append,
      remove_ones] at H0'
    simp only [remove_ones_append]
    rw [remove_ones_to_option, List.append_nil, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at H0'
    exact H0'
  · intro e f g i j k l m n o op p
    have e_is : e = remover a.reverse ++ remover a1.reverse := by
      rw [← remover_append, ← List.reverse_append]
      symm
      apply remove_rev_eq_remove_ones_eq_to_up_plain
      rw [← m, remove_ones_append]
    have f_is : f = remover b ++ remover j := by
      rw [← remover_append]
      exact eq_remover_of_remove_ones_eq_to_over_plain n
    rw [e_is, f_is] at p
    rcases splittable_horizontally_of_gridt p _ _ rfl
      with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
    have H := (same_time_c i1 g1).1 (to_up_plain_remover_rev_eq_remove_ones
      g1.left_frontier_is_false).symm (by rw [to_over_plain_append,
        to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true]; exact
          List.prefix_append_self_C)
    rcases H with ⟨d2, ⟨hd2⟩⟩
    have H0 : pg_mid_frontier_reverses_to_grid_extend_top g1 := g1_ih.2.2.1
    specialize @H0 (remover a.reverse) (remover b ++ remover j) d1 c1 j d2 hd2
      (to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false).symm
      (by rw [remove_ones_append, to_over_plain_append,
        to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true, to_over_plain_remover_eq_remove_ones op]) o op i1
    apply @SemiThue_append_left _ _ _ _ (remove_ones (mid2 ++ up2)) at H0
    simp [remove_ones_append] at H0
    simp [remove_ones_append]
    apply H0.trans
    rw [rm, to_up_plain_mul, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    apply SemiThue_append_right
    have H0' : pg_mid_frontier_reverses_to_grid_extend_top g2 := g2_ih.2.2.1
    have is_true_d2 : is_true (to_option d2 ++ [(none, true)]) := by
      apply is_true_of_true_true
      · have H : is_true (to_over_plain c1) := to_over_plain_true
        rw [← hd2] at H
        apply is_true_append at H
        apply is_true_to_option
        exact H.2
      exact is_true_cons [] is_true_nil
    have helper1 : remove_ones (bot ++ (to_option d2 ++ [(none, true)])) = to_over_plain c1 := by
      simp [remove_ones, remove_ones_to_option, hd2]
    specialize @H0' (remover a1.reverse) c1 e1 i (to_option d2 ++ [(none, true)]) k l
        (to_up_plain_remover_rev_eq_remove_ones g2.left_frontier_is_false).symm helper1 (by simp) is_true_d2 i2
    simp [remove_ones, remove_ones_to_option] at H0'
    rw [List.append_assoc]
    exact H0'
  intro e f g i j k l m n o p
  have e_is : e = remover a.reverse ++ remover a1.reverse := by
    rw [← remover_append, ← List.reverse_append]
    symm
    apply remove_rev_eq_remove_ones_eq_to_up_plain
    rw [← n, remove_ones_append]
  have f_is : f = remover b := eq_remover_of_remove_ones_eq_to_over_plain o
  rw [e_is, f_is] at p
  rcases splittable_horizontally_of_gridt p _ _ rfl
    with ⟨c1, d1, e1, i1, i2, ⟨rm⟩⟩
  have H := (same_time_c i1 g1).1 (to_up_plain_remover_rev_eq_remove_ones
    g1.left_frontier_is_false).symm (by rw [to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true]; exact
      List.prefix_refl_C)
  have H2 := (same_time_c i1 g1).2 (to_over_plain_remover_eq_remove_ones (by exact
    g1.top_frontier_is_true)).symm
    (by rw [to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false]; exact List.suffix_refl_C)
  rcases H with ⟨d2, ⟨hd2⟩⟩
  rcases H2 with ⟨d3, ⟨hd3⟩⟩
  have H0 : pg_mid_frontier_reverses_to_grid_extend_neither g1 := g1_ih.2.2.2
  specialize @H0 (remover a.reverse) (remover b) d1 c1 d2 d3 hd2 hd3
    (to_up_plain_remover_rev_eq_remove_ones g1.left_frontier_is_false).symm
    (to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true).symm i1
  apply @SemiThue_append_left _ _ _ _ (remove_ones (mid2++up2)) at H0
  rw [← remove_ones_append, ← List.append_assoc] at H0
  apply H0.trans
  rw [rm, to_up_plain_mul, ← hd3, ← List.append_assoc, List.append_left_inj] at m
  rw [m, ← List.append_assoc]
  apply SemiThue_append_right
  have H0' : pg_mid_frontier_reverses_to_grid_extend_top g2 := g2_ih.2.2.1
  specialize @H0' (remover a1.reverse) c1 e1 i (to_option d2 ++ [(none, true)]) j l
  rw [remove_ones_append, remove_ones_append, remove_ones, remove_ones_nil, List.append_nil, remove_ones_to_option,
    to_up_plain_remover_rev_eq_remove_ones g2.left_frontier_is_false] at H0'
  have helper1 : is_true (to_option d2 ++ [(none, true)]) := by
    apply is_true_of_true_true
    · have H : is_true (to_over_plain c1) := to_over_plain_true
      rw [← hd2] at H
      apply is_true_append at H
      apply is_true_to_option
      exact H.2
    exact is_true_cons [] is_true_nil
  specialize H0' rfl hd2 (by simp) helper1 i2
  simp only [List.append_assoc, List.cons_append, List.nil_append, remove_ones_append,
    remove_ones] at H0'
  simp only [remove_ones_append]
  rw [remove_ones_to_option, List.append_nil, ← List.append_assoc] at H0'
  exact H0'

noncomputable def extend_both_cell (h : cell a b c d) :
    pg_mid_frontier_reverses_to_grid_extend_both (PartialGrid.single_gridt h) := by
  intro e f g i j k l m n no o op p
  cases h with
  | empty =>
    simp_all [remove_ones]
    exact grid_to_rev p
  | top_bottom i =>
    simp_all [remove_ones]
    exact grid_to_rev p
  | sides i =>
    rw [to_up_singleton, remove_ones] at l
    rw [to_over_nil, remove_ones] at m
    simp only [to_over_nil, List.append_nil, to_up_singleton,
      List.nil_append, remove_ones_append, remove_ones, l, m]
    convert grid_to_rev p
  | top_left i =>
    have hl := to_up_plain_eq_append_remove_ones l.symm
    have hm := to_over_plain_eq_append_remove_ones m.symm
    simp only [to_up_singleton, List.reverse_cons, List.reverse_nil, List.nil_append,
      to_over_singleton] at hl hm
    rcases splittable_horizontally_of_gridt p ([i]) _ hl with ⟨u, c1, c2, g1, g2, ⟨spec⟩⟩
    rcases splittable_vertically_of_gridt g1 [i] _ hm with ⟨u1, c3, c4, g3, g4, ⟨spec1⟩⟩
    have H := i_top_left_t g3 i rfl rfl
    rw [H.1] at g4
    have H1 := word_side_side_t _ _ _ g4 rfl
    rw [H1.1, one_mul] at spec
    have hb := grid_to_rev g2
    simp_all [remove_ones]
    rw [spec1, to_up_plain_remover_rev_eq_remove_ones no, to_over_plain_remover_eq_remove_ones op] at hb
    exact hb
  | adjacent i k' hdist =>
    have hl := to_up_plain_eq_append_remove_ones l.symm
    have hm := to_over_plain_eq_append_remove_ones m.symm
    simp only [to_up_singleton, List.reverse_cons, List.reverse_nil, List.nil_append,
      to_over_singleton] at hl hm
    rcases splittable_horizontally_of_gridt p ([i]) _ hl with ⟨u, c1, c2, g1, g2, ⟨spec⟩⟩
    rcases splittable_vertically_of_gridt g1 [k'] _ hm with ⟨u1, c3, c4, g3, g4, ⟨spec1⟩⟩
    have H := i_adjacent_t g3 i k' rfl rfl hdist
    rw [H.1] at g4
    rw [spec1, H.2] at g2
    have hb := grid_to_rev g2
    have hd := grid_to_rev g4
    simp_all [remove_ones]
    have Hd := @SemiThue_append_left _ reversing _ _ (remove_ones j ++ [(k', true)] ++ [(i, true)]) hd
    simp only [List.append_assoc, List.cons_append, List.nil_append, to_up_plain_mul] at Hd
    have Hb := @SemiThue_append_right _ reversing _ _ (to_up_plain c1) hb
    rw [to_up_plain_mul]
    rw [to_over_plain_remover_eq_remove_ones op] at Hd
    rw [to_over_plain_mul, to_over_plain_mul, to_up_plain_remover_rev_eq_remove_ones no,
      List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at Hb
    exact Hd.trans _ _ _ Hb
  | separated i j' hdist =>
    have hl := to_up_plain_eq_append_remove_ones l.symm
    have hm := to_over_plain_eq_append_remove_ones m.symm
    simp at hl hm
    rcases splittable_horizontally_of_gridt p ([i]) _ hl with ⟨u, c1, c2, g1, g2, ⟨spec⟩⟩
    rcases splittable_vertically_of_gridt g1 [j'] _ hm with ⟨u1, c3, c4, g3, g4, ⟨spec1⟩⟩
    have H := helpier_ij_t g3 i j' hdist rfl rfl
    rw [H.1] at g4
    rw [spec1, H.2] at g2
    have hb := grid_to_rev g2
    have hd := grid_to_rev g4
    simp_all [remove_ones]
    have Hd := @SemiThue_append_left _ reversing _ _ (remove_ones j ++ [(j', true)]) hd
    simp [to_up_plain_mul] at Hd
    have Hb := @SemiThue_append_right _ reversing _ _ (to_up_plain c1) hb
    rw [to_up_plain_mul]
    rw [to_over_plain_remover_eq_remove_ones op] at Hd
    rw [to_over_plain_mul, to_up_plain_remover_rev_eq_remove_ones no] at Hb
    simp at Hb
    exact Hd.trans _ _ _ Hb

noncomputable def extend_left_cell (h : cell a b c d) :
    pg_mid_frontier_reverses_to_grid_extend_left (PartialGrid.single_gridt h) := by
  intro e f g i j k l m n o op p
  cases h with
  | empty =>
    simp_all [remove_ones]
    have H := word_top_bottom_t _ _ _ p (to_over_plain_inj n)
    rw [H.1, H.2]
    apply SemiThue.refl
  | top_bottom i =>
    simp_all [remove_ones]
    exact grid_to_rev p
  | sides i =>
    simp [remove_ones, to_over] at n
    have f_is : f = [] := by exact to_over_plain_inj n
    rw [f_is] at p
    have H := word_top_bottom_t _ _ _ p rfl
    simp_all [remove_ones]
    rw [← m] at l
    apply List.append_singleton_eq_append_singleton at l
    rw [← l.1]
    apply SemiThue.refl
  | top_left i' =>
    have hm := to_up_plain_eq_append_remove_ones m.symm
    simp_all [remove_ones]
    change to_over_plain [i'] = _ at n
    have hf := to_over_plain_inj n
    rcases splittable_horizontally_of_gridt p ([i']) _ hm with
      ⟨u, c1, c2, g1, g2, ⟨spec⟩⟩
    rw [← hf] at g1
    have H := i_top_left_t g1 i' rfl rfl
    have hr := grid_to_rev g2
    rw [H.2, to_up_plain_remover_rev_eq_remove_ones op] at hr
    rw [spec, H.1]
    convert hr
    simp
    rfl
  | adjacent i' k' hdist =>
    have hm := to_up_plain_eq_append_remove_ones m.symm
    simp_all [remove_ones]
    change to_over_plain [k'] = _ at n
    have hf := to_over_plain_inj n
    rcases splittable_horizontally_of_gridt p ([i']) _ hm with
      ⟨u, c1, c2, g1, g2, ⟨spec⟩⟩
    rw [← hf] at g1
    have H := i_adjacent_t g1 i' k' rfl rfl hdist
    have hr := grid_to_rev g2
    rw [H.2, to_up_plain_remover_rev_eq_remove_ones op] at hr
    have hn : (remove_ones j ++ to_over_plain (FreeMonoid.of k' * FreeMonoid.of i')) =
      (remove_ones j ++ [(k', true), (i', true)]) := by
      simp [to_over_plain_mul]
      rfl
    rw [hn] at hr
    apply hr.trans
    rw [spec, to_up_plain_mul, H.1, to_up_plain_mul] at l
    change k ++ [(k', false), (i', false)] = to_up_plain c2 ++ [(k', false), (i', false)] at l
    rw [List.append_left_inj] at l
    rw [l]
    exact SemiThue.refl _
  | separated i' j' hdist =>
    have hm := to_up_plain_eq_append_remove_ones m.symm
    simp_all [remove_ones]
    change to_over_plain [j'] = _ at n
    have hf := to_over_plain_inj n
    rcases splittable_horizontally_of_gridt p ([i']) _ hm with
      ⟨u, c1, c2, g1, g2, ⟨spec⟩⟩
    rw [← hf] at g1
    have H := helpier_ij_t g1 i' j' hdist rfl rfl
    have hr := grid_to_rev g2
    have k_is : k = to_up_plain c2 := by
      rw [spec, to_up_plain_mul, H.1] at l
      change k ++ [(i', false)] = to_up_plain c2 ++ [(i', false)] at l
      exact List.append_cancel_right l
    rw [H.2, to_up_plain_remover_rev_eq_remove_ones op, ← k_is] at hr
    rw [← n]
    exact hr

noncomputable def extend_top_cell (h : cell a b c d) :
    pg_mid_frontier_reverses_to_grid_extend_top (PartialGrid.single_gridt h) := by
  intro e f g i j k l m n o op p
  rw [List.append_assoc, remove_ones_append, remove_ones_nil, List.nil_append]
  cases h with
  | empty =>
    simp_all [remove_ones]
    have : e = [] := by exact to_up_plain_inj m
    rw [this] at p
    exact grid_to_rev p
  | top_bottom i =>
    simp_all [remove_ones]
    have : e = [] := by exact to_up_plain_inj m
    rw [this] at p
    have H := word_side_side_t _ _ _ p rfl
    rw [H.1]
    simp [← H.2, ← l] at n
    rw [n]
    change SemiThue reversing _ (_ ++ [])
    rw [List.append_nil]
    exact SemiThue.refl _
  | sides i =>
    simp_all [remove_ones]
    have H := grid_to_rev p
    rw [← m] at H
    exact H
  | top_left i =>
    rw [remove_ones_append] at n
    simp [to_over] at n
    have hf := to_over_plain_eq_append_remove_ones n.symm
    rcases splittable_vertically_of_gridt p (remover [(some i, true)]) _ hf with
      ⟨u, c1, c2, g1, g2, ⟨spec⟩⟩
    have e_is : e = [i] := by
      simp [remove_ones, to_up] at m
      exact to_up_plain_inj m.symm
    have H := i_top_left_t g1 i e_is rfl
    rw [H.1] at g2
    have H1 := word_side_side_t _ _ _ g2 rfl
    simp_all [remove_ones]
    change SemiThue reversing (remove_ones j) (to_over_plain (remover j) ++ [])
    rw [List.append_nil, to_over_plain_remover_eq_remove_ones op]
    exact SemiThue.refl _
  | adjacent i' k' hdist =>
    have e_is : e = [i'] := by
      simp [remove_ones, to_up] at m
      exact to_up_plain_inj m.symm
    rw [remove_ones_append] at n
    simp [to_over] at n
    have hf := to_over_plain_eq_append_remove_ones n.symm
    rcases splittable_vertically_of_gridt p (remover [(some k', true)]) _ hf with
      ⟨u, c1, c2, g1, g2, ⟨spec⟩⟩
    have H := i_adjacent_t g1 i' k' e_is rfl hdist
    rw [H.1] at g2
    have hr := grid_to_rev g2
    rw [remove_ones_append]
    change SemiThue reversing ([(k', false), (i', false)] ++ remove_ones j) _
    have k_is : k = to_over_plain c2 := by
      simp only [to_over_cons_cons, to_over_singleton, remove_ones, List.cons_append,
        List.nil_append, spec, H.2, to_over_plain_mul, List.append_assoc] at l
      change _ = (k', true) :: (i', true) :: (to_over_plain c2) at l
      simp only [List.cons.injEq, true_and] at l
      exact l
    rw [to_over_plain_remover_eq_remove_ones op, ← k_is] at hr
    exact hr
  | separated i' j' hdist =>
    have e_is : e = [i'] := by
      simp [remove_ones, to_up] at m
      exact to_up_plain_inj m.symm
    rw [remove_ones_append] at n
    simp [to_over] at n
    have hf := to_over_plain_eq_append_remove_ones n.symm
    rcases splittable_vertically_of_gridt p (remover [(some j', true)]) _ hf with
      ⟨u, c1, c2, g1, g2, ⟨spec⟩⟩
    have H := helpier_ij_t g1 i' j' hdist e_is rfl
    rw [H.1] at g2
    have hr := grid_to_rev g2
    rw [remove_ones_append]
    change SemiThue reversing ([(i', false)] ++ remove_ones j) _
    have k_is : k = to_over_plain c2 := by
      simp only [to_over_cons_cons, to_over_singleton, remove_ones, List.cons_append,
        List.nil_append, spec, H.2, to_over_plain_mul, List.append_assoc] at l
      change _ = (j', true) :: (to_over_plain c2) at l
      simp only [List.cons.injEq, true_and] at l
      exact l
    rw [to_over_plain_remover_eq_remove_ones op, ← k_is] at hr
    exact hr

noncomputable def extend_neither_cell  (h : cell a b c d) :
    pg_mid_frontier_reverses_to_grid_extend_neither (PartialGrid.single_gridt h) := by
  intro e f g i j k l m n o p
  cases h with
  | empty =>
    simp [to_up, remove_ones] at m
    simp [to_over, remove_ones] at l
    have e_is : e = [] := to_up_plain_inj n.symm
    have f_is : f = [] := to_over_plain_inj o.symm
    rw [e_is, f_is] at p
    have H := all_ones_better_t p
    simp_all [to_over_plain, to_up_plain]
    apply SemiThue.refl
  | top_bottom i =>
    simp [to_up, remove_ones] at m
    simp [to_over, remove_ones] at l
    have e_is : e = [] := to_up_plain_inj n.symm
    have f_is : f = [i] := to_over_plain_inj o.symm
    rw [e_is, f_is] at p
    have H := i_top_bottom_t p _ rfl rfl
    rw [H.2] at l
    change _ = [(i, true)] at l
    simp_all [to_over_plain, to_up_plain]
    apply SemiThue.refl
  | sides i =>
    simp [to_up, remove_ones] at m
    simp [to_over, remove_ones] at l
    have e_is : e = [i] := to_up_plain_inj n.symm
    have f_is : f = [] := to_over_plain_inj o.symm
    rw [e_is, f_is] at p
    have H := i_side_side_t p _ rfl rfl
    rw [H.1] at m
    change _ = [(i, false)] at m
    simp_all [to_over_plain, to_up_plain]
    apply SemiThue.refl
  | top_left i =>
    simp [to_up, remove_ones] at m
    simp [to_over, remove_ones] at l
    have e_is : e = [i] := to_up_plain_inj n.symm
    have f_is : f = [i] := to_over_plain_inj o.symm
    rw [e_is, f_is] at p
    have H := i_top_left_t p _ rfl rfl
    simp_all [to_over_plain, to_up_plain]
    apply SemiThue.refl
  | adjacent i k h =>
    simp [to_up, remove_ones] at m
    simp [to_over, remove_ones] at l
    have e_is : e = [i] := to_up_plain_inj n.symm
    have f_is : f = [k] := to_over_plain_inj o.symm
    rw [e_is, f_is] at p
    have H := i_adjacent_t p _ _ rfl rfl h
    rw [H.1] at m
    rw [H.2] at l
    change _ = [(k, false), (i, false)] at m
    change _ = [(k, true), (i, true)] at l
    simp_all [to_over_plain, to_up_plain]
    apply SemiThue.refl
  | separated i j h =>
    simp [to_up, remove_ones] at m
    simp [to_over, remove_ones] at l
    have e_is : e = [i] := to_up_plain_inj n.symm
    have f_is : f = [j] := to_over_plain_inj o.symm
    rw [e_is, f_is] at p
    have H := helpier_ij_t p _ _ h rfl rfl
    rw [H.1] at m
    rw [H.2] at l
    change _ = [(i, false)] at m
    change _ = [(j, true)] at l
    simp_all [to_over_plain, to_up_plain]
    apply SemiThue.refl

noncomputable def all_options_frontier_reverse (h : PartialGrid a1 b1 c1 d1 e1) :
  pg_mid_frontier_reverses_to_grid_extend_both h × pg_mid_frontier_reverses_to_grid_extend_left h
  × pg_mid_frontier_reverses_to_grid_extend_top h × pg_mid_frontier_reverses_to_grid_extend_neither h := by
  induction h with
  | single_gridt h =>
    repeat any_goals constructor
    · exact extend_both_cell h
    · exact extend_left_cell h
    · exact extend_top_cell h
    exact extend_neither_cell h
  | empty a b ha ha1 hb hb1 =>
    repeat any_goals constructor
    · intro e f g i j k l m n no o op p
      rw [List.append_nil, List.append_nil, ← List.append_assoc, List.append_assoc,
        remove_ones_append, remove_ones_append, remove_ones_append, l, m]
      exact grid_to_rev p
    · intro e f g i j k l m n o op p
      rw [remove_ones, List.append_nil] at l
      rw [List.append_nil, ← List.append_assoc, remove_ones_append, remove_ones_append]
      rw [l, m, n]
      exact grid_to_rev p
    · intro e f g i j k l m n o op p
      rw [remove_ones, List.nil_append] at l
      rw [List.append_nil, List.append_assoc, remove_ones_append, l, m, n]
      exact grid_to_rev p
    intro e f g i j k l m n o p
    simp only [remove_ones, List.nil_append, List.append_nil] at l m
    convert grid_to_rev p
    simp [n, o]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    exact all_options_horizontal_append_one g1 g2 g1_ih g2_ih
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    exact all_options_horizontal_append h g1 g2 g1_ih g2_ih
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    exact all_options_vertical_append_one g1 g2 g1_ih g2_ih
  | vertical_append g1 g2 h g1_ih g2_ih =>
    exact all_options_vertical_append g1 g2 h g1_ih g2_ih

noncomputable def pg_mid_frontier_reverses_to_grid (h : PartialGrid a1 b1 c1 d1 e1)
  (ha : a1 = to_up a) (hb : b1 = to_over b) (h2 : gridt a b f g) :
  SemiThue reversing (remove_ones (c1 ++ d1 ++ e1)) (to_over_plain g ++ to_up_plain f) := by
  have ⟨H2, H3⟩ := same_time_c h2 h
  rw [ha, hb] at H2 H3
  rw [remove_over_is_plain] at H2
  rw [remove_up_is_plain] at H3
  specialize H2 remove_up_is_plain List.prefix_refl_C
  specialize H3 remove_over_is_plain List.suffix_refl_C
  rcases H2 with ⟨c2, ⟨hc2⟩⟩
  rcases H3 with ⟨e2, ⟨he2⟩⟩
  have ha1 : remove_ones a1 = to_up_plain a := by
    rw [ha]
    exact remove_up_is_plain
  have hb1 : remove_ones b1 = to_over_plain b := by
    rw [hb]
    exact remove_over_is_plain
  have H := @(all_options_frontier_reverse h).2.2.2 a b f g c2 e2 hc2 he2 ha1 hb1
  rw [← he2, ← hc2]
  simp [remove_ones_append]
  apply SemiThue_append_left
  rw [← List.append_assoc]
  apply SemiThue_append_right
  exact H h2

noncomputable def restricted_confluence (h1 : SemiThue reversing (to_up_plain a ++ to_over_plain b) c)
  (h2 : SemiThue reversing (to_up_plain a ++ to_over_plain b) d) : Σ e, SemiThue reversing c e × SemiThue reversing d e := by
  have H1 := step_three h1
  have H2 := step_three h2
  rcases H1 with ⟨c1, d1, e1, pg, ⟨rm1⟩⟩
  rcases H2 with ⟨c2, d2, e2, pg2, ⟨rm2⟩⟩
  have H2 : Σ c3 d3, gridt a b c3 d3 := existence_s a b
  rcases H2 with ⟨c3, d3, gt⟩
  use (to_over_plain d3 ++ to_up_plain c3)
  rw [← rm1, ← rm2]
  constructor
  · exact pg_mid_frontier_reverses_to_grid pg rfl rfl gt
  exact pg_mid_frontier_reverses_to_grid pg2 rfl rfl gt

theorem correct_other_dir (h : PresentedMonoid.mk braid_rels_m_inf a =
    PresentedMonoid.mk braid_rels_m_inf b) : final_solver a b := by
  have H : grid (a*1) (b*1) 1 1 := by
    apply grid_of_eq
    rw [mul_one, mul_one]
    exact h
  rw [mul_one, mul_one] at H
  have Ht : gridt a b 1 1 := by
    exact (gridt_of_grid H).some
  have hr := grid_to_rev Ht
  change SemiThue reversing _ [] at hr
  have hpg := step_three (grid_to_rev Ht)
  match a with
  | [] =>
    match b with
    | [] =>
      simp [final_solver]
    | b1 :: b2 =>
      simp [final_solver]
      have H := eq_of_SemiThue_true hr to_over_plain_true
      simp [to_over_plain] at H
  | a1 :: a2 =>
    match b with
    | [] =>
      simp [final_solver]
      simp [to_over_plain] at hr
      have H := eq_of_SemiThue_false hr to_up_plain_false
      simp [to_up_plain] at H
    | b1 :: b2 =>
      simp [final_solver]
      have H := @solver_equiv (a1 :: a2) (b1 :: b2) (by simp) (by simp)
      rcases restricted_confluence hr H with ⟨e, h1, h2⟩
      have He : e = [] := (eq_of_SemiThue_true h1 is_true_nil).symm
      rw [← He]
      apply eq_of_SemiThue_in_order h2
      apply solver_helper_in_order
