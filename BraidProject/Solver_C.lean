import BraidProject.StepTwo_C
import BraidProject.SemiThue_C
import BraidProject.Cancellability_C
import BraidProject.GridsTwo_C
import BraidProject.PartialGrid_bounded
import BraidProject.PartialGrid_rw

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


def solver_helper' (a : triangle) : {h : triangle // h.1 = a.1 ∧ h.2.1 = a.2.1} :=
  match hb' : find_it a.2.2.1 with
  | none => ⟨a, ⟨rfl, rfl⟩⟩
  | some (c, d, e) =>
    match hd : d.1.dist d.2 with
    | 0 => solver_helper' ⟨a.1, ⟨a.2.1, ⟨c ++ e,
        ⟨a.2.2.2.1,
        by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb', Nat.eq_of_dist_eq_zero hd]
          nth_rw 2 [← List.append_nil c]
          exact SemiThue.reduction reversing.basic⟩⟩⟩⟩
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

theorem solver_helper_find_it_none' : find_it (solver_helper a)= none := by
  induction ha : get_n' a using Nat.strongRecOn generalizing a
  rw [solver_helper]
  split
  · assumption
  split
  · rename_i ih l m o p hd
    apply @ih
      (get_n' ⟨a.fst, ⟨a.snd.fst, ⟨l ++ o, ⟨a.2.2.2.1,
          by
          apply a.2.2.2.2.trans
          rw [find_it_spec p, Nat.eq_of_dist_eq_zero hd]
          nth_rw 2 [← List.append_nil l]
          exact SemiThue.reduction reversing.basic⟩⟩⟩⟩)
    rw [← ha]
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec p with ⟨b1, b2, b3⟩
    have H : m.1 = m.2 := by exact Nat.eq_of_dist_eq_zero hd
    rcases m with ⟨x, y⟩
    simp only at H
    subst H
    unfold get_n'
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · apply @get_n'_same a1 a2 a4.1 l o [(x, false), (x, true)] []
      · rfl
      · simp
      apply reversing.basic
    · apply pg_smaller_than_g
    · apply pg_smaller_than_g
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
    · apply @get_n'_same a1 a2 a4.1 m o [(x, false), (y, true)]
        [(y, true), (x, true), (y, false), (x, false)]
      · rfl
      · simp
      exact reversing.close hd
    · apply pg_smaller_than_g
    · apply pg_smaller_than_g
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
  · apply @get_n'_same a1 a2 a4.1 l n [(x, false), (y, true)]
      [(y, true), (x, false)]
    · rfl
    · simp
    exact reversing.apart (by aesop)
  · apply pg_smaller_than_g
  apply pg_smaller_than_g
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
      (get_n' ⟨a.fst, ⟨a.snd.fst, ⟨p ++ r, ⟨a.2.2.2.1,
          by
          apply a.2.2.2.2.trans
          rw [find_it_spec o, Nat.eq_of_dist_eq_zero hd]
          nth_rw 2 [← List.append_nil p]
          exact SemiThue.reduction reversing.basic⟩⟩⟩⟩)
    rw [← ha]
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec o with ⟨b1, b2, b3⟩
    have H : q.1 = q.2 := by exact Nat.eq_of_dist_eq_zero hd
    rcases q with ⟨x, y⟩
    simp only at H
    subst H
    unfold get_n'
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · apply @get_n'_same a1 a2 a4.1 p r [(x, false), (x, true)] []
      · rfl
      · simp
      apply reversing.basic
    · apply pg_smaller_than_g
    · apply pg_smaller_than_g
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
    · apply @get_n'_same a1 a2 a4.1 p r [(x, false), (y, true)]
        [(y, true), (x, true), (y, false), (x, false)]
      · rfl
      · simp
      exact reversing.close hd
    · apply pg_smaller_than_g
    · apply pg_smaller_than_g
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
  · apply @get_n'_same a1 a2 a4.1 p r [(x, false), (y, true)]
      [(y, true), (x, false)]
    · rfl
    · simp
    exact reversing.apart (by aesop)
  · apply pg_smaller_than_g
  apply pg_smaller_than_g
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

def solver_helper_in_order : in_order (solver_helper' a).1.2.2.1 := by
  have H := solver_helper_find_it_none a
  exact in_order_of_find_it_none H


def solver_long (a b) (ha : List.length a > 0) (hb : List.length b > 0) :=
  solver_helper' ⟨a, ⟨b, ⟨to_up_plain a ++ to_over_plain b, by simp [to_up_plain, to_over_plain]; exact ⟨⟨ha, hb⟩, by apply SemiThue.refl _ ⟩⟩⟩⟩


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
  rcases middle_frontier_nil_or_caps pg with ⟨⟨mid_nil⟩⟩ | ⟨fm, mm, cm, ⟨problem⟩⟩
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
#check skeleton_order
def skeleton_order_to_up_plain_to_over_plain : skeleton_order
  (to_up_plain a ++ to_over_plain b) := by
  use to_up_plain a
  use to_over_plain b
  constructor
  · exact to_up_plain_false
  constructor
  · exact to_over_plain_true
  exact ⟨rfl⟩

theorem to_option_append : to_option (a ++ b) = to_option a ++ to_option b := by
  unfold to_option; simp

theorem eq_of_SemiThue_false (h : SemiThue reversing a b) (ha : is_false a) : a = b := by
  induction h with
  | refl a => rfl
  | reduction h =>
    rcases h
    · rename_i n
      specialize ha (n, true) ⟨by simp⟩
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
    · rename_i n
      specialize ha (n, false) ⟨by simp⟩
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
    · rename_i c d n
      have spec_rw : c ++ [(n, false), (n, true)] ++ d =
        (c ++ [(n, false)]) ++ ((n, true):: d) := by simp
      rw [spec_rw] at spec
      rcases List.append_eq_append_iff.mp spec with
        ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
      · rw [spec1] at one_true
        specialize one_true (n, false) ⟨by simp⟩
        simp at one_true
        exact one_true.1.elim
      rw [spec2] at two_false
      specialize two_false (n, true) ⟨by simp⟩
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

theorem to_over_plain_mul {a b : FreeMonoid ℕ} :
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
  | top_left i => exact SemiThue_rel reversing.basic
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

noncomputable def all_options_frontier_reverse (h : PartialGrid a1 b1 c1 d1 e1) :
  pg_mid_frontier_reverses_to_grid_extend_both h × pg_mid_frontier_reverses_to_grid_extend_left h
  × pg_mid_frontier_reverses_to_grid_extend_top h × pg_mid_frontier_reverses_to_grid_extend_neither h := by
  induction h with
  | single_gridt h =>
    repeat any_goals constructor
    · rename_i a b c d
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
    · rename_i a b c d
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
    · rename_i a b c d
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
    rename_i a b c d
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
  | empty a b ha ha1 hb hb1 =>
    repeat any_goals constructor
    · intro e f g i j k l m n no o op p
      rw [List.append_nil, List.append_nil, ← List.append_assoc, List.append_assoc,
        remove_ones_append, remove_ones_append, remove_ones_append]
      rw [l, m]
      exact grid_to_rev p
    · intro e f g i j k l m n o op p
      rw [remove_ones, List.append_nil] at l
      rw [List.append_nil, ← List.append_assoc, remove_ones_append, remove_ones_append]
      rw [l, m, n]
      exact grid_to_rev p
    · intro e f g i j k l m n o op p
      rw [remove_ones, List.nil_append] at l
      rw [List.append_nil, List.append_assoc, remove_ones_append]
      rw [l, m, n]
      exact grid_to_rev p
    intro e f g i j k l m n o p
    simp only [remove_ones, List.nil_append, List.append_nil] at l m
    convert grid_to_rev p
    simp [n, o]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a b bot up b2 bot2 mid2 up2
    repeat any_goals constructor
    · intro e f g i j k l m n no o op p
      have H0 : pg_mid_frontier_reverses_to_grid_extend_left g1 := g1_ih.2.1
      have H0' : pg_mid_frontier_reverses_to_grid_extend_both g2 := g2_ih.1
      have e_is : e = remover (a.reverse) ++ remover (j.reverse) := by
        rw [← remover_append, ← List.reverse_append]
        symm
        apply remove_rev_eq_remove_ones_eq_to_up_plain
        rw [← l]
        rw [remove_ones_append]
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
      rw [H.2.1] at i3 i4
      rw [H.1.1] at i3 rm1
      rw [rm1] at i2
      specialize @H0 (remover a.reverse ++ remover j.reverse) (remover b) c1 d1 j (to_up_plain e2)
      rw [rm1, to_up_plain_mul, to_up_plain_remover_rev_eq_remove_ones
        g2.left_frontier_is_false] at H0
      specialize H0 rfl
      rw [to_up_plain_append, to_up_plain_remover_rev_eq_remove_ones no, to_up_plain_remover_rev_eq_remove_ones
          g1.left_frontier_is_false, to_over_plain_remover_eq_remove_ones g1.top_frontier_is_true] at H0
      specialize H0 rfl rfl n no
      rw [rm1] at i1
      specialize H0 i1
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
      unfold pg_mid_frontier_reverses_to_grid_extend_both at H0'
      sorry

      -- specialize @H0' c1 (remover b2) g e1 (to_up e2) k l
      -- rw [rm1, to_up_plain_mul, to_up_plain_remover_rev_eq_remove_ones
      --   g2.left_frontier_is_false, List.append_left_inj, remove_up_is_plain,
      --   List.append_assoc] at H0'
      -- have h1 : remove_ones b2 = to_over_plain (remover b2) := by
      --   rw [to_over_plain_remover_eq_remove_ones]
      --   exact g2.top_frontier_is_true
      -- rw [rm1] at i2
      -- specialize @H0' rfl h1 to_up_len_pos is_false_up i2
      -- convert H0'
      -- conv =>
      --   enter [2]
      --   rw [remove_ones_append]
      -- rw [List.append_left_inj]
      -- exact remove_up_is_plain.symm
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
  | horizontal_append h g1 g2 g1_ih g2_ih => sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

noncomputable def pg_mid_frontier_reverses_to_grid (h : PartialGrid a1 b1 c1 d1 e1)
  (ha : a1 = to_up a) (hb : b1 = to_over b) (h2 : gridt a b f g) :
  SemiThue reversing (remove_ones (c1 ++ d1 ++ e1)) (to_over_plain g ++ to_up_plain f) := by
  have ⟨H2, H3⟩ := same_time h2 h
  rw [ha, hb] at H2 H3
  rw [remove_over_is_plain] at H2
  rw [remove_up_is_plain] at H3
  specialize H2 remove_up_is_plain List.prefix_rfl
  specialize H3 remove_over_is_plain List.suffix_rfl
  have nonsense1 : Σ c2, PLift (remove_ones c1 ++ c2 = to_over_plain g) := by sorry
  have nonsense2 : Σ e2, PLift (e2 ++ remove_ones e1 = to_up_plain f) := by
    sorry
  rcases nonsense1 with ⟨c2, ⟨hc2⟩⟩
  rcases nonsense2 with ⟨e2, ⟨he2⟩⟩
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
