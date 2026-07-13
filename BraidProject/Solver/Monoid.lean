import BraidProject.Solver.FindOpenPair
import BraidProject.SignedOptionList
import BraidProject.TrueFalse_C
import BraidProject.PartialGrid.Basic
import BraidProject.StepOne
import BraidProject.StepTwo_C_basic_eq
import BraidProject.GridData_length
import BraidProject.PartialGrid.Bounded
import BraidProject.Solver.StepOne_length_general
import BraidProject.PartialGrid.AddCell

namespace Braid

-- noncomputable def FrontierStyle.of_SemiThueData_reversing (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++
--     to_horizontal_edge_no_epsilon b) c)
--     (ha : a.length > 0) (hb : b.length > 0) :
--     Σ c , Σ h1 : PartialGrid.FrontierStyle (to_vertical_edge a) (to_horizontal_edge b) c,
--     PLift (SemiThueData.reversing.length h = h1.length) := by
--   have H := SemiThueData.reversing.to_grid_style_w_length_horizontal_vertical_edge h ha hb
--   rcases H with ⟨c1, h2, hl⟩
--   rw [hl.1]
--   use c1
--   have H3 := SemiThueData.grid_style.toSemiThueDataDerivation_with_length h2
--   rcases H3 with ⟨h4, hl4⟩
--   rw [hl4]
--   have H2 := @PartialGrid.FrontierStyle.of_SemiThueDataDerivation_grid_style _ _ (to_vertical_edge a) (to_horizontal_edge b) h4 rfl (is_false_to_vertical_edge) (to_vertical_edge_length_pos)
--     (is_true_to_horizontal_edge) (to_horizontal_edge_length_pos)
--   use H2
--   constructor
--   aesop

noncomputable def PartialGrid.of_SemiThueData_reversing (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
  (ha : a.length > 0) (hb : b.length > 0) :
  Σ c d e, Σ h1 : PartialGrid (to_vertical_edge a) (to_horizontal_edge b) c d e, PLift (SemiThueData.reversing.length h = h1.length) := by
  have H := SemiThueData.reversing.to_grid_style_w_length_horizontal_vertical_edge h ha hb
  rcases H with ⟨c, h3, h4⟩
  rw [h4.1]
  have H := step_two (is_false_to_vertical_edge) (to_vertical_edge_length_pos) is_true_to_horizontal_edge to_horizontal_edge_length_pos h3
  rcases H with ⟨d, e, f, h1, h2⟩
  use d, e, f, h1
  exact ⟨h2.2.1.symm⟩

theorem st_smaller_than_g (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
  (ha : a.length > 0) (hb : b.length > 0):
    ab_len a b ≥ SemiThueData.reversing.length h := by
  rcases PartialGrid.of_SemiThueData_reversing h ha hb with ⟨c, d, e, h1, hl⟩
  rw [hl.1]
  apply straight_pg_sm_g
  rfl
  rfl

abbrev triangle (a b : List ℕ) : Type := Σ c : List (ℕ × Bool),
  (SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)

open Braid

namespace Triangle

-- noncomputable def to_PartialGrid (a : triangle) : Σ bot mid top, PartialGrid (to_vertical_edge a.1)
--     (to_horizontal_edge a.2.1) bot mid top × PLift (SignedOptionList.toSignedList (bot ++ mid ++ top) = a.2.2.1) := by
--   have H := @stepOne_mid (to_vertical_edge_no_epsilon a.1 ++ to_horizontal_edge_no_epsilon a.2.1) a.2.2.1 a.2.2.2.2
--   have H1 : SignedList.NegPosData (to_vertical_edge_no_epsilon a.1 ++ to_horizontal_edge_no_epsilon a.2.1) := by
--     use to_vertical_edge_no_epsilon a.1, to_horizontal_edge_no_epsilon a.2.1
--     constructor; constructor; apply is_false_to_vertical_edge_no_epsilon
--     constructor; apply is_true_to_horizontal_edge_no_epsilon
--     rfl
--   rcases H H1 with ⟨c, Hc⟩
--   have H4 : (SignedList.to_SignedOptionList (List.map (fun y ↦ (y, false)) a.fst.reverse)).length > 0 := by
--     rw [SignedList.to_SignedOptionList_length]
--     simp only [List.map_reverse, List.length_reverse, List.length_map, gt_iff_lt]
--     exact a.2.2.2.1.1.1
--   have H5 : (SignedList.to_SignedOptionList (List.map (fun y ↦ (y, true)) a.snd.fst)).length > 0 := by
--     simp [SignedList.to_SignedOptionList_length]
--     exact a.2.2.2.1.1.2
--   have H6 : SignedList.to_SignedOptionList (to_vertical_edge_no_epsilon a.1 ++ to_horizontal_edge_no_epsilon a.snd.fst) =
--     SignedList.to_SignedOptionList (to_vertical_edge_no_epsilon a.1) ++ SignedList.to_SignedOptionList (to_horizontal_edge_no_epsilon a.snd.fst) := by
--       rw [SignedList.to_SignedOptionList_append]
--   rw [SignedList.to_SignedOptionList_append] at Hc
--   have H3 := @step_two (SignedList.to_SignedOptionList (List.map (fun y ↦ (y, false)) a.fst.reverse))
--     (SignedList.to_SignedOptionList (List.map (fun y ↦ (y, true)) a.snd.fst)) c
--     (by apply SignedList.is_false_to_SignedOptionList; simp; intro x hx; simp at hx;
--         rcases hx with ⟨a, ha⟩; aesop) H4
--     (by apply SignedList.is_true_to_SignedOptionList; simp [SignedList.is_true]) H5 Hc.1
--   rcases H3 with ⟨bot, mid, up, pg, c_is⟩
--   use bot, mid, up
--   constructor
--   · have H : a.1.length ≠ 0 := by
--         intro h
--         rw [List.eq_nil_iff_length_eq_zero.mpr h] at H4
--         simp  [SignedList.to_SignedOptionList] at H4
--     have H1 : a.2.1.length ≠ 0 := by
--       intro h
--       rw [List.eq_nil_iff_length_eq_zero.mpr h] at H5
--       simp [SignedList.to_SignedOptionList] at H5
--     have H2 : a.1 ≠ [] := by aesop
--     have H3 : a.2.1≠ [] := by aesop
--     simp [to_vertical_edge, to_horizontal_edge]
--     unfold SignedList.to_SignedOptionList at pg
--     change PartialGrid ((List.map (fun (x : ℕ × Bool) ↦ (some x.1, x.2)) ∘ (List.map (fun y ↦ (y, false)))) a.fst.reverse)
--       ((List.map (fun (x : ℕ × Bool) ↦ (some x.1, x.2)) ∘ (List.map (fun y ↦ (y, true)))) a.snd.fst) bot mid up at pg
--     have H : ∀ b, List.map (fun (x : ℕ × Bool) ↦ (some x.1, x.2)) ∘ (List.map (fun y ↦ (y, b))) = List.map (fun x => (some x, b)) := by
--       intro b
--       ext
--       simp
--     rw [H, H] at pg
--     simp at pg
--     exact pg
--   rw [c_is.1]
--   exact Hc.2.2

noncomputable def length (a : triangle a1 a2) : ℕ := ab_len a1 a2 - (SemiThueData.reversing.length a.2)

end Triangle

open Triangle

def solver_helper {a1 a2} (ha1 : a1.length > 0) (ha2 : a2.length > 0) (a : triangle a1 a2) :
    triangle a1 a2 :=
  match hb' : FindOpenPair a.1 with
  | none => a
  | some (c, d, e) =>
    match hd : d.1.dist d.2 with
    | 0 => solver_helper ha1 ha2 ⟨c ++ [] ++ e,
        by
          apply a.2.trans
          rw [FindOpenPair.spec hb']
          exact SemiThueData.step _ _ (reversing.basic hd)⟩
    | 1 => solver_helper ha1 ha2 ⟨(c ++ [(d.2, true), (d.1, true), (d.2, false), (d.1, false)] ++ e),
        by
          apply a.2.trans
          rw [FindOpenPair.spec hb']
          exact SemiThueData.step _ _ (reversing.close hd)⟩
    | Nat.succ (Nat.succ n) => solver_helper ha1 ha2 ⟨(c ++ [(d.2, true), (d.1, false)] ++ e),
        by
          apply a.2.trans
          rw [FindOpenPair.spec hb']
          exact SemiThueData.step _ _ (reversing.apart (by omega))⟩
    termination_by length a
    decreasing_by
    · rcases a with ⟨a3, a4⟩
      simp only
      rcases FindOpenPair.spec hb' with ⟨b1, b2, b3⟩
      rcases d with ⟨x, y⟩
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · simp [SemiThueData.reversing.length]
      · apply st_smaller_than_g
        assumption
        assumption
      apply st_smaller_than_g
      assumption
      assumption
    · rcases a with ⟨a3, a4⟩
      rcases FindOpenPair.spec hb' with ⟨b1, b2, b3⟩
      rcases d with ⟨x, y⟩
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · simp [SemiThueData.reversing.length]
      · apply st_smaller_than_g
        assumption
        assumption
      apply st_smaller_than_g
      assumption
      assumption
    rcases a with ⟨a3, a4⟩
    rcases FindOpenPair.spec hb' with ⟨b1, b2, b3⟩
    rcases d with ⟨x, y⟩
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [SemiThueData.reversing.length]
    · apply st_smaller_than_g
      assumption
      assumption
    apply st_smaller_than_g
    assumption
    assumption

theorem solver_helper_FindOpenPair_none {a1 a2} {ha1 : a1.length > 0} {ha2 : a2.length > 0}
    (a : triangle a1 a2)  : FindOpenPair (solver_helper ha1 ha2 a).1= none := by
  induction ha : length a using Nat.strongRecOn generalizing a
  rw [solver_helper]
  split
  · assumption
  split
  · rename_i ih l m o p hd
    apply @ih
      (length ⟨l ++ [] ++ o,
          by
          apply a.2.trans
          rw [FindOpenPair.spec p]
          exact SemiThueData.step _ _ (reversing.basic hd)⟩)
    rw [← ha]
    rcases a with ⟨a3, a4⟩
    rcases FindOpenPair.spec p with ⟨b1, b2, b3⟩
    have H : m.1 = m.2 := by exact Nat.eq_of_dist_eq_zero hd
    rcases m with ⟨x, y⟩
    simp only at H
    subst H
    unfold length
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [SemiThueData.reversing.length]
    · apply st_smaller_than_g
      assumption
      assumption
    apply st_smaller_than_g
    assumption
    assumption
    rfl
  · rename_i ih m n o p hd
    apply @ih (length ⟨(m ++ [(n.2, true), (n.1, true), (n.2, false), (n.1, false)] ++ o),
        by
          apply a.2.trans
          rw [FindOpenPair.spec p]
          exact SemiThueData.step _ _ (reversing.close hd)⟩)
    rcases a with ⟨a3, a4⟩
    rcases FindOpenPair.spec p with ⟨b1, b2, b3⟩
    rcases n with ⟨x, y⟩
    rw [← ha]
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [SemiThueData.reversing.length]
    · apply st_smaller_than_g
      assumption
      assumption
    apply st_smaller_than_g
    assumption
    assumption
    rfl
  rename_i ih l m n o p hd
  apply @ih (length ⟨(l ++ [(m.2, true), (m.1, false)] ++ n),
        by
          apply a.2.trans
          rw [FindOpenPair.spec o]
          exact SemiThueData.step _ _ (reversing.apart (by omega))⟩)
  rcases a with ⟨a3, a4⟩
  rcases FindOpenPair.spec o with ⟨b1, b2, b3⟩
  rcases m with ⟨x, y⟩
  rw [← ha]
  apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
  · simp [SemiThueData.reversing.length]
  · apply st_smaller_than_g
    assumption
    assumption
  apply st_smaller_than_g
  assumption
  assumption
  rfl

open SignedList

def SignedList.PosNegData_of_FindOpenPair_none (h : FindOpenPair a = none) : SignedList.PosNegData a := by
  induction a with
  | nil =>
    use [], []
    constructor
    exact ⟨SignedList.is_true_nil, ⟨SignedList.is_false_nil, rfl⟩⟩
  | cons head tail ih =>
    have h2 := FindOpenPair.cons_eq_none h
    specialize ih h2
    rcases ih with ⟨c, d, h1, h2, ⟨h3⟩⟩
    match head with
    | (a, true) =>
      use (a, true)::c, d
      constructor
      constructor
      · exact SignedList.is_true_cons c h1
      constructor
      · assumption
      rfl
    | (a, false) =>
      match c with
      | [] =>
        use [], (a, false)::d
        constructor
        constructor
        · exact h1
        constructor
        · exact SignedList.is_false_cons d (by assumption)
        rfl
      | (c1, true) :: c2 =>
        simp [FindOpenPair] at h
      | (c1, false) :: c2 =>
        specialize h1 (c1, false) (by simp)
        simp at h1

def solver_helper_SignedList.PosNegData {ha1 : a1.length > 0} {ha2 : a2.length > 0} (a : triangle a1 a2) : SignedList.PosNegData (solver_helper ha1 ha2 a).1 := by
  have H := @solver_helper_FindOpenPair_none _ _ ha1 ha2 a
  exact SignedList.PosNegData_of_FindOpenPair_none H

def solver_long (a b) (ha : List.length a > 0) (hb : List.length b > 0) :=
  solver_helper ha hb ⟨to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b, SemiThueData.refl ⟩

def solver_long_PosNegData (a b) (ha : List.length a > 0) (hb : List.length b > 0) :
  SignedList.PosNegData (solver_long a b ha hb).1 := by
  have H := @solver_helper_FindOpenPair_none _ _ ha hb ⟨to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b, SemiThueData.refl ⟩
  exact SignedList.PosNegData_of_FindOpenPair_none H

def solver_equiv (ha : List.length a > 0) (hb : List.length b > 0)  : SemiThueData reversing
    (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) (solver_long a b ha hb).1 := (solver_long a b ha hb).2

def final_solver (a b : List ℕ) : Bool :=
  match a with
  | [] =>
    match b with
    | [] => true
    | b1 :: b2 => false
  | a1 :: a2 =>
    match b with
    | [] => false
    | b1 :: b2 => (@solver_long (a1 :: a2) (b1 :: b2) (by simp) (by simp)).1 = []
