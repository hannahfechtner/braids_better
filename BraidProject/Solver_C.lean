import BraidProject.StepTwo_C
import BraidProject.SemiThue_C
import BraidProject.Cancellability_C
import BraidProject.GridsTwo_C
import BraidProject.PartialGrid_bounded

-- import BraidProject.BraidGroup
-- def to_up_plain (a : List ℕ) : List (ℕ × Bool) := List.map (fun x => (x, false)) a.reverse

-- def to_over_plain (a : List ℕ) : List (ℕ × Bool) := List.map (fun x => (x, true)) a
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
theorem find_it_some_cons_true (h : find_it tail = some ⟨a, b, c⟩) : find_it ((d, true) :: tail) = some ⟨(d, true):: a, b, c⟩ := by
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

-- def gridt.length : gridt a b c d → ℕ := by
--   intro h
--   match h with
--   | gridt.empty => exact 0
--   | gridt.sides _ => exact  0
--   | gridt.top_bottom _ => exact 0
--   | gridt.top_left _ => exact 1
--   | gridt.adjacent _ _ _ => exact 1
--   | gridt.separated _ _ _ => exact 1
--   | gridt.horizontal h1 h2 => exact gridt.length h1 + gridt.length h2
--   | gridt.vertical h1 h2 => exact gridt.length h1 + gridt.length h2

-- noncomputable def ab_len (a b : List ℕ) : ℕ :=
--   match existence_s a b with
--   | ⟨_, _, h⟩ => gridt.length h

noncomputable def get_n' (a : triangle) : ℕ := ab_len a.1 a.2.1 - (get_pg a).2.2.2.1.length

set_option pp.notation true

theorem straight_pg_sm_g (h : PartialGrid a b c d e) (h1 : gridt a1 b1 f g)
    : a = to_up a1 → b = to_over b1 → h.length ≤ h1.length := by
  intro ha hb
  apply pg_sm_g_eq1 h h1
  · rw [ha]
    exact remove_up_is_plain
  rw [hb]
  exact remove_over_is_plain

theorem pg_smaller_than_g (a : triangle) : ab_len a.1 a.2.1 ≥ (get_pg a).2.2.2.1.length := by
  apply straight_pg_sm_g _ _ rfl rfl

-- noncomputable def get_n (a : triangle) : ℕ := by
--   have H := @stepOne_mid (List.map (fun y => (y, false)) a.1.reverse ++ List.map (fun y => (y, true)) a.2.1) a.2.2.1 a.2.2.2.2
--   have H1 : skeleton_order (List.map (fun y ↦ (y, false)) a.fst.reverse ++ List.map (fun y ↦ (y, true)) a.snd.fst) := by
--     unfold skeleton_order
--     use List.map (fun y ↦ (y, false)) a.fst.reverse
--     use List.map (fun y ↦ (y, true)) a.snd.fst
--     constructor
--     · simp [is_true]
--       intro x ⟨hx⟩
--       constructor
--       simp at hx
--       rcases hx with ⟨w, hw⟩
--       rw [← hw.2]
--     · simp [is_true]
--       constructor
--       · intro x ⟨hx⟩
--         constructor
--         simp at hx
--         rcases hx with ⟨w, hw⟩
--         rw [← hw.2]
--       exact ⟨trivial⟩
--   specialize H H1
--   rcases H with ⟨c, Hc⟩
--   have H4 : (to_option (List.map (fun y ↦ (y, false)) a.fst.reverse)).length > 0 := by
--     rw [to_option_length]
--     simp
--     exact a.2.2.2.1.1.1
--   have H5 : (to_option (List.map (fun y ↦ (y, true)) a.snd.fst)).length > 0 := by
--     simp [to_option_length]
--     exact a.2.2.2.1.1.2
--   have H6 : to_option (List.map (fun y ↦ (y, false)) a.fst.reverse ++ List.map (fun y ↦ (y, true)) a.snd.fst) =
--     (to_option (List.map (fun y ↦ (y, false)) a.fst.reverse) ++ to_option (List.map (fun y ↦ (y, true)) a.snd.fst)) := by
--       simp [to_option]
--   rw [H6] at Hc
--   have H3 := @step_two (to_option (List.map (fun y ↦ (y, false)) a.fst.reverse))
--     (to_option (List.map (fun y ↦ (y, true)) a.snd.fst)) c
--     (by apply is_false_to_option; simp [is_true]; intro x ⟨hx⟩; simp at hx; constructor;
--          rcases hx with ⟨a, ha⟩; aesop) H4
--     (by apply is_true_to_option ; simp [is_true]; intro x ⟨hx⟩; simp at hx; constructor;
--          rcases hx with ⟨a, ha⟩; rw [← ha.2]) H5 Hc.1
--   rcases H3 with ⟨bot, mid, up, pg, c_is⟩
--   exact PartialGrid.length pg

theorem get_n'_same''  (c0 c3 c₁ c₂) (hr : reversing c₁ c₂)
  (rev1 : SemiThue reversing (to_up_plain a ++ to_over_plain b) (c0 ++ c₁ ++ c3))
  (rev2 : SemiThue reversing (to_up_plain a ++ to_over_plain b) (c0 ++ c₂ ++ c3))
  (h1 : PartialGrid (to_up a) (to_over b) c5 d5 e5)
  (h6 : remove_ones (c5 ++ d5 ++ e5) = c0 ++ c₁ ++ c3)
  (h2 : PartialGrid (to_up a) (to_over b) c6 d6 e6)
  (h7 : remove_ones (c6 ++ d6 ++ e6) = c0 ++ c₂ ++ c3) :
  h1.length < h2.length := by
  sorry

theorem get_n'_same'  (c0 c3 c₁ c₂ c1 c2) (hc1 : c1 = c0 ++ c₁ ++ c3)  (hc2 : c2 = c0 ++ c₂ ++ c3) (hr : reversing c₁ c₂)
  (rev1 : SemiThue reversing (to_up_plain a ++ to_over_plain b) c1)
  (rev2 : SemiThue reversing (to_up_plain a ++ to_over_plain b) c2) (h1 : PartialGrid (to_up a) (to_over b) c5 d5 e5)
  (h6 : remove_ones (c5 ++ d5 ++ e5) = c0 ++ c₁ ++ c3) (h2 : PartialGrid (to_up a) (to_over b) c6 d6 e6)
  (h7 : remove_ones (c6 ++ d6 ++ e6) = c0 ++ c₂ ++ c3):
  h1.length < h2.length := by
  rw [hc1] at rev1
  rw [hc2] at rev2
  apply get_n'_same'' _ _ _ _ hr rev1 rev2 h1 h6 h2 h7

theorem get_n'_same  (c0 c3 c₁ c₂ c1 c2) (hc1 : c1 = c0 ++ c₁ ++ c3)  (hc2 : c2 = c0 ++ c₂ ++ c3) (hr : reversing c₁ c₂)
  (rev1 : SemiThue reversing (to_up_plain a ++ to_over_plain b) c1)
  (rev2 : SemiThue reversing (to_up_plain a ++ to_over_plain b) c2) :
  (get_pg ⟨a, ⟨b, ⟨c1, ⟨len, rev1⟩⟩⟩⟩).2.2.2.1.length <
  (get_pg ⟨a, ⟨b, ⟨c2, ⟨len, rev2⟩⟩⟩⟩).2.2.2.1.length := by
  simp
  apply get_n'_same' _ _ _ _ _ _ hc1 hc2 hr rev1 rev2
  · rw [← hc1]
    rcases (get_pg ⟨a, ⟨b, ⟨c1, ⟨len, rev1⟩⟩⟩⟩) with ⟨bot, mid, up, pg1, rest⟩
    simp only at rest
    symm
    nth_rewrite 1 [← rest.1]
    simp
  rw [← hc2]
  rcases (get_pg ⟨a, ⟨b, ⟨c2, ⟨len, rev2⟩⟩⟩⟩) with ⟨bot, mid, up, pg1, rest⟩
  simp only at rest
  symm
  nth_rewrite 1 [← rest.1]
  simp

def solver_helper (a : triangle) : List (ℕ × Bool) :=
  match hb': find_it a.2.2.1 with
  | none => a.2.2.1
  | some (c, d, e) =>
    match hd : d.1.dist d.2 with
    | 0 => solver_helper ⟨a.1, ⟨a.2.1, ⟨c ++ e,
        ⟨a.2.2.2.1,
        by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb', Nat.eq_of_dist_eq_zero hd]
          nth_rw 2 [← List.append_nil c]
          exact SemiThue.reduction reversing.basic⟩⟩⟩⟩
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
      rcases find_it_spec hb' with ⟨b1, b2, b3⟩
      have H : d.1 = d.2 := by exact Nat.eq_of_dist_eq_zero hd
      rcases d with ⟨x, y⟩
      simp only at H
      subst H
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · apply @get_n'_same a1 a2 a4.1 c e [(x, false), (x, true)] []
        · rfl
        · simp
        exact reversing.basic
      · apply pg_smaller_than_g
      apply pg_smaller_than_g
    · rcases a with ⟨a1, a2, a3, a4⟩
      rcases find_it_spec hb' with ⟨b1, b2, b3⟩
      rcases d with ⟨x, y⟩
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · apply @get_n'_same a1 a2 a4.1 c e [(x, false), (y, true)]
          [(y, true), (x, true), (y, false), (x, false)]
        · rfl
        · simp
        exact reversing.close hd
      · apply pg_smaller_than_g
      apply pg_smaller_than_g
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec hb' with ⟨b1, b2, b3⟩
    rcases d with ⟨x, y⟩
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · apply @get_n'_same a1 a2 a4.1 c e [(x, false), (y, true)]
        [(y, true), (x, false)]
      · rfl
      · simp
      exact reversing.apart (by aesop)
    · apply pg_smaller_than_g
    apply pg_smaller_than_g

def solver a b := solver_helper ⟨a, ⟨b, ⟨to_up_plain a ++ to_over_plain b, by simp [to_up_plain, to_over_plain]; exact ⟨⟨sorry, sorry⟩, by apply SemiThue.refl _ ⟩⟩⟩⟩

def solver_equiv  : SemiThue reversing (to_up_plain a ++  to_over_plain b) (solver a b) := by
  unfold solver solver_helper
  split
  · simp
    exact SemiThue.refl _
  simp
  split
  · sorry --simp
  let ha := find_it (to_up_plain a ++ to_over_plain b)
  cases hello : ha
  · --simp [ha]

    sorry
  sorry
  sorry
  -- match find_it (to_up_plain a ++ to_over_plain b) with
  -- | none => sorry
  --   simp [haa]
  --   exact SemiThue.refl _
  -- | some (c, d, e) => sorry
    -- match hd : d.1.dist d.2 with
    -- | 0 =>
    --   simp
    --   rw [hd]
    --   simp
    --   have H := find_it_spec ha
    --   rw [H]
    --   have H : d.1 = d.2 := by exact Nat.eq_of_dist_eq_zero hd
    --   rw [H]
    --   have H : SemiThue reversing (c ++ e) (solver_helper (a, b, c ++ e)) := by sorry
    --   have H2 : SemiThue reversing (c ++ ([(d.2, false)] ++ [(d.2, true)]) ++ e) (c ++ e) := by
    --     have H : (c ++ e) = c ++ [] ++ e := by simp
    --     rw [H]
    --     exact SemiThue.reduction reversing.basic
    --   exact H2.trans _ _ _ H
    -- | 1 =>
    --   simp
    --   rw [hd]
    --   simp
    --   have H := find_it_spec ha
    --   rw [H]
    --   have H : SemiThue reversing (c ++ (d.2, true) :: (d.1, true) :: (d.2, false) :: (d.1, false) :: e)
    --     (solver_helper (a, b, c ++ (d.2, true) :: (d.1, true) :: (d.2, false) :: (d.1, false) :: e)) := by sorry
    --     --(solver (c ++ (d.2, true) :: (d.1, true) :: (d.2, false) :: (d.1, false) :: e)) := by sorry
    --   have H2 : SemiThue reversing (c ++ ([(d.1, false), (d.2, true)]) ++ e)
    --       (c ++ (d.2, true) :: (d.1, true) :: (d.2, false) :: (d.1, false) :: e) := by
    --     have H : (c ++ (d.2, true) :: (d.1, true) :: (d.2, false) :: (d.1, false) :: e) =
    --       (c ++ [(d.2, true), (d.1, true), (d.2, false), (d.1, false)] ++ e) := by simp
    --     rw [H]
    --     exact SemiThue.reduction (reversing.close hd)
    --   exact H2.trans _ _ _ H
    -- | Nat.succ (Nat.succ n) =>
    --   simp
    --   rw [hd]
    --   simp
    --   have H := find_it_spec ha
    --   rw [H]
    --   have H : SemiThue reversing (c ++ (d.2, true) :: (d.1, false) :: e)
    --     (solver_helper (a, b, c ++ (d.2, true) :: (d.1, false) :: e)) := by sorry --(solver (c ++ (d.2, true) :: (d.1, false) :: e)) := by sorry
    --   have H2 : SemiThue reversing (c ++ ([(d.1, false), (d.2, true)]) ++ e)
    --       (c ++ (d.2, true) :: (d.1, false) :: e) := by
    --     have H : (c ++ (d.2, true) :: (d.1, false) :: e) =
    --       (c ++ [(d.2, true), (d.1, false)] ++ e) := by simp
    --     rw [H]
    --     exact SemiThue.reduction (reversing.apart (by omega))
    --   exact H2.trans _ _ _ H

#exit
def list_to_free_group (L : List (α × Bool)) : FreeGroup α := match L with
  | [] => 1
  | (a, false) :: tail => FreeGroup.of a * list_to_free_group tail
  | (a, true) :: tail => (FreeGroup.of a)⁻¹ * list_to_free_group tail

@[simp]
theorem list_to_free_group_nil : list_to_free_group ([] : List (α × Bool)) = 1 := by simp [list_to_free_group]


theorem list_to_free_group_append (a b : List (α × Bool)) :
    list_to_free_group (a ++ b) = list_to_free_group a * list_to_free_group b := by
  induction a with
  | nil => simp
  | cons head tail ih =>
    rcases head with ⟨h1, h2⟩
    cases h2 with
    | false =>
      simp
      conv => lhs; simp [list_to_free_group]
      rw [ih]
      conv => rhs; simp [list_to_free_group]
      rw [mul_assoc]
    | true =>
      simp
      conv => lhs; simp [list_to_free_group]
      rw [ih]
      conv => rhs; simp [list_to_free_group]
      rw [mul_assoc]

theorem reversing_to_group_equiv (h : SemiThue reversing a b) :
    PresentedGroup.mk Braid.braid_rels_coexeter (list_to_free_group a) =
    PresentedGroup.mk Braid.braid_rels_coexeter (list_to_free_group b) := by
  induction h with
  | refl a => rfl
  | reduction h =>
    simp [list_to_free_group_append]
    cases h with
    | basic =>
      rename_i n
      simp [list_to_free_group]
    | apart h =>
      rename_i i j
      simp only [list_to_free_group, mul_one, map_mul, map_inv]
      rw [←mul_inv_eq_one]
      apply QuotientGroup.eq.mpr
      unfold Subgroup.normalClosure
      unfold Subgroup.closure
      simp only [Subgroup.mem_sInf, Set.mem_setOf_eq]
      intro p hp
      have H : (FreeGroup.of j)⁻¹ * FreeGroup.of i * (FreeGroup.of j * (FreeGroup.of i)⁻¹)  ∈
        Group.conjugatesOfSet Braid.braid_rels_coexeter := by
        refine Group.mem_conjugatesOfSet_iff.mpr ?_
        use FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹
        constructor
        · exact Braid.separated h
        apply isConj_iff.mpr
        use .of i * (.of j)⁻¹ * (.of i)⁻¹
        group
      exact hp H
    | close h =>
      rename_i i j
      simp only [list_to_free_group, mul_one, map_mul, map_inv]
      rw [←mul_inv_eq_one]
      apply QuotientGroup.eq.mpr
      unfold Subgroup.normalClosure
      unfold Subgroup.closure
      simp only [Subgroup.mem_sInf, Set.mem_setOf_eq]
      intro p hp
      simp
      have H : (.of j)⁻¹ * ((.of i)⁻¹ * (.of j * .of i)) * (.of j * (.of i)⁻¹)  ∈
        Group.conjugatesOfSet Braid.braid_rels_coexeter := by
        refine Group.mem_conjugatesOfSet_iff.mpr ?_
        use .of i * .of j * .of i * (.of j)⁻¹ * (.of i)⁻¹ * (.of j)⁻¹
        constructor
        ·  sorry
        apply isConj_iff.mpr
        sorry
      exact hp H
  | trans a b c _ _ h1 h2=>
    exact h1.trans h2

-- theorem solver_correct (a b : List ℕ) (h : solver (to_up_plain a) (to_over_plain b) = []) :
--     BraidMonoidInf.mk a = BraidMonoidInf.mk b := by
--   have H := solver_equiv (to_up_plain a) (to_over_plain b)
--   rw [h] at H
--   apply reversing_to_group_equiv at H
--   simp [list_to_free_group_append] at H
--   sorry
--   sorry
--   sorry
