import BraidProject.Grids_C
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.NewListFacts
import BraidProject.Relations

namespace Braid

open List SignedList SignedOptionList

def GridData_option (a b c d : List (Option ℕ × Bool)) : Type := Braid.GridData (toList a.reverse) (toList b)
  (toList c) (toList d.reverse)

open GridData

def GridData_option_append_horiz (h1 : GridData_option a b c d) (h2 : GridData_option d e f g) : GridData_option a (b ++ e) (c ++ f) g := by
  simp only [GridData_option, toList_append]
  exact GridData.horizontal h1 h2

def GridData_option_append_vert (h1 : GridData_option a b c d) (h2 : GridData_option e c f g) : GridData_option (e ++ a) b f (g ++ d) := by
  simp [GridData_option, toList_append]
  exact GridData.vertical h1 h2

/-- A partial GridData generalizes the notion of a GridData to include "unfinished" GridDatas. -/
inductive PartialGrid : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
  | single_cell (h : CellData a b c d) : PartialGrid (to_vertical_edge a) (to_horizontal_edge b) (to_horizontal_edge c) [] (to_vertical_edge d)
  | empty (a b : List (Option ℕ × Bool)) (ha : a.length > 0) (ha1 : is_false a)
      (hb : b.length > 0) (hb : is_true b) : PartialGrid a b [] (a ++ b) []
  | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : PartialGrid a b bot [] up)
      (g2 : PartialGrid up b2 bot2 mid2 up2) : PartialGrid a (b ++ b2) (bot ++ bot2) mid2 up2
  | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : List (Option ℕ × Bool)}
      (h : mid.length > 0)
      (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid up b2 bot2 mid2 up2) :
      PartialGrid a (b ++ b2) bot (mid ++ bot2 ++ mid2) up2
  | vertical_append_one (g1 : PartialGrid a b bot [] up) (g2 : PartialGrid a1 bot bot2 mid2 up2) :
      PartialGrid (a1 ++ a) b bot2 mid2 (up2 ++ up)
  | vertical_append (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid a1 bot bot2 mid2 up2) (h : mid.length > 0) :
      PartialGrid (a1 ++ a) b bot2 (mid2 ++ up2 ++ mid) up

namespace PartialGrid

def length (h : PartialGrid a b c d e) :=
  match h with
  | single_cell h =>
    by cases h with
    | empty => exact 0
    | top_bottom i => exact 0
    | sides i => exact 0
    | top_left i => exact 1
    | adjacent i k h => exact 1
    | separated i j h => exact 1
  | empty a b ha ha1 hb hb1 => 0
  | horizontal_append_one g1 g2 => g1.length + g2.length
  | horizontal_append h g1 g2 => g1.length + g2.length
  | vertical_append_one g1 g2 => g1.length + g2.length
  | vertical_append g1 g2 h => g1.length + g2.length

noncomputable def right_frontier_is_false (h : PartialGrid a b c d e) : is_false e := by
  induction h with
  | single_cell  => exact is_false_to_vertical_edge
  | empty => exact is_false_nil
  | horizontal_append_one => assumption
  | horizontal_append => assumption
  | vertical_append_one _ _ g1_ih g2_ih =>
    exact is_false_append g2_ih g1_ih
  | vertical_append => assumption

noncomputable def  top_frontier_is_true (h : PartialGrid a b c d e) : is_true b := by
  induction h with
  | single_cell => exact is_true_to_horizontal_edge
  | empty  => assumption
  | horizontal_append_one _ _ g1_ih g2_ih => exact is_true_append g1_ih g2_ih
  | horizontal_append _ _ _ g1_ih g2_ih => exact is_true_append g1_ih g2_ih
  | vertical_append_one => assumption
  | vertical_append => assumption

noncomputable def left_frontier_is_false (h : PartialGrid a b c d e) : is_false a := by
  induction h with
    | single_cell => exact is_false_to_vertical_edge
    | empty => assumption
    | horizontal_append_one => assumption
    | horizontal_append => assumption
    | vertical_append_one _ _ g1_ih g2_ih =>
      exact is_false_append g2_ih g1_ih
    | vertical_append _ _ _ ih1 ih2 => exact is_false_append ih2 ih1

noncomputable def bottom_frontier_is_true (h : PartialGrid a b c d e) : is_true c := by
  induction h with
    | single_cell => exact is_true_to_horizontal_edge
    | empty => exact is_true_nil
    | horizontal_append_one => exact is_true_append (by assumption) (by assumption)
    | horizontal_append => assumption
    | vertical_append_one => assumption
    | vertical_append => assumption

theorem left_length_pos (h : PartialGrid a b c d e) : a.length > 0 := by
  induction h with
  | single_cell  => exact to_vertical_edge_length_pos
  | empty => assumption
  | horizontal_append_one => assumption
  | horizontal_append => assumption
  | vertical_append_one =>
    rw [List.length_append]
    omega
  | vertical_append =>
    rw [List.length_append]
    omega

theorem top_length_pos (h : PartialGrid a b c d e) : b.length > 0 := by
  induction h with
  | single_cell => exact to_horizontal_edge_length_pos
  | empty => assumption
  | horizontal_append_one =>
    rw [List.length_append]
    omega
  | horizontal_append =>
    rw [List.length_append]
    omega
  | vertical_append_one => assumption
  | vertical_append => assumption

theorem mid_length_neq_one (h : PartialGrid a b c d e) : d.length ≠ 1 := by
  intro hd
  induction h with
  | single_cell => simp at hd
  | empty => rw [List.length_append] at hd; omega
  | horizontal_append_one _ _ _ g2_ih => exact g2_ih hd
  | horizontal_append _ _ _ g1_ih =>
    rw [List.append_assoc, List.length_append] at hd
    exact g1_ih (by omega)
  | vertical_append_one _ _ _ g2_ih => exact g2_ih hd
  | vertical_append _ _ _ g1_ih =>
    rw [List.length_append] at hd
    exact g1_ih (by omega)

open PartialGrid

noncomputable def extend_bottom (h : PartialGrid a b c d e) (a2) (h2 : is_false a2) (h3 : a2 ≠ []) :
    PartialGrid (a2 ++ a) b [] (a2 ++ c ++ d) e := by
  induction h with
  | single_cell h =>
    cases a2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i c d
      rw [← List.nil_append (to_vertical_edge d), List.append_nil]
      exact PartialGrid.vertical_append_one (PartialGrid.single_cell h)
        (PartialGrid.empty (head :: tail) (to_horizontal_edge c) (by simp) h2 to_horizontal_edge_length_pos is_true_to_horizontal_edge)
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, ← List.append_assoc]
    apply PartialGrid.empty (a2 ++ a) b _ (is_false_append h2 ha1) (by assumption) hb
    rw [List.length_append]
    omega
  | horizontal_append_one g1 g2 ih1 ih2 =>
    have H := PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos_iff.mpr h3)) ih1 g2
    rw [List.append_nil] at H
    rw [← List.append_assoc]
    exact H
  | horizontal_append h g1 g2 ih1 ih2 =>
    rw [← List.append_assoc, ← List.append_assoc]
    exact PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos_iff.mpr h3)) ih1 g2
  | vertical_append_one g1 g2 ih1 ih2 =>
    rw [← List.append_assoc]
    exact PartialGrid.vertical_append_one g1 ih2
  | vertical_append g1 g2 h ih1 ih2 =>
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    exact PartialGrid.vertical_append g1 ih2 h

noncomputable def extend_side (h : PartialGrid a b c d e) (b2) (h2 : is_true b2) (h3 : b2 ≠ []) :
    PartialGrid a (b ++ b2) c (d ++ e ++ b2) [] := by
  induction h with
  | single_cell h =>
    cases b2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i c d
      have H := PartialGrid.horizontal_append_one (PartialGrid.single_cell h)
          (PartialGrid.empty (to_vertical_edge d) (head :: tail) to_vertical_edge_length_pos is_false_to_vertical_edge (by simp) h2)
      rw [List.append_nil] at H
      exact H
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, List.append_assoc]
    apply PartialGrid.empty a (b ++ b2) ha ha1 _ (is_true_append hb h2)
    rw [List.length_append]
    omega
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    have H := PartialGrid.horizontal_append_one g1 g2_ih
    rw [← List.append_assoc] at H
    exact H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    have H := PartialGrid.horizontal_append h g1 g2_ih
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at H
    exact H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    have H := PartialGrid.vertical_append g1_ih g2 (by simp; exact Or.inr (List.length_pos_iff.mpr h3))
    rw [← List.append_assoc, ← List.append_assoc, List.append_nil] at H
    rw [← List.append_assoc]
    exact H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    have H := PartialGrid.vertical_append g1_ih g2 (by simp; exact Or.inr (Or.inr (List.length_pos_iff.mpr h3)))
    rw [← List.append_assoc, ← List.append_assoc] at H
    exact H

def middle_spec (d : List (α × Bool)) := PLift (d = []) ⊕ Σ front mid caboose, PLift (d = [(front, false)] ++ mid ++ [(caboose, true)])

def middle_end (d : List (α × Bool)) := PLift (d = []) ⊕ Σ mid caboose, PLift (d = mid ++ [(caboose, true)])

def middle_start (d : List (α × Bool)) := PLift (d = []) ⊕ Σ front mid, PLift (d = [(front, false)] ++ mid)

def middle_start_append (h : middle_start (d1 ++ d2)) : middle_start d1 := by
  cases d1 with
  | nil => left; exact {down := rfl}
  | cons head tail =>
    right
    rcases h with h1 | ⟨f, m, spec⟩
    · simp only [List.cons_append, reduceCtorEq] at h1
      apply h1.1.elim
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at spec
    use f, tail
    rw [spec.1.1]
    constructor
    simp

def middle_start_from_spec (h : middle_spec d) : middle_start d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use f, m ++ [(c, true)]
  exact spec

def middle_end_from_spec (h : middle_spec d) : middle_end d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use [(f, false)] ++ m, c
  exact spec

noncomputable def middle_frontier_spec (h : PartialGrid a b c d e) : middle_spec d := by
  induction h with
  | single_cell h =>
    left; exact {down := rfl}
  | empty a b ha ha1 hb hb1 =>
    right
    match a with
    | [] => simp at ha
    | (a1, true) :: a2 =>
      specialize ha1 (a1, true) (by simp)
      simp only [Bool.true_eq_false] at ha1
    | (a1, false) :: a2 =>
      use a1
      match hbr : b.reverse with
      | [] =>
        rw [List.reverse_eq_nil_iff.mp hbr] at hb
        simp only [List.length_nil, gt_iff_lt, lt_self_iff_false] at hb
      | (b1, false) :: b2 =>
        apply congr_arg List.reverse at hbr
        rw [List.reverse_reverse] at hbr
        rw [hbr] at hb1
        specialize hb1 (b1, false) (by simp)
        simp only [Bool.false_eq_true] at hb1
      | (b1, true) :: b2 =>
        use (a2 ++ b2.reverse), b1
        constructor
        apply congr_arg List.reverse at hbr
        grind
  | horizontal_append_one g1 g2 g1_ih g2_ih => assumption
  | horizontal_append h1 g1 g2 g1_ih g2_ih =>
    rename_i bot2 _ _
    rcases g1_ih with ⟨ha⟩ | hb
    · rw [ha.1] at h1
      simp at h1
    rcases g2_ih with hc | hd
    · right; rw [hc.1, List.append_nil];
      rcases hc with ⟨f1, c1, h1⟩
      induction bot2 using List.reverseRecOn with
      | nil => rw [List.append_nil]; exact hb
      | append_singleton f2 c2 _ =>
        rcases hb with ⟨f1, m1, c1, h1⟩
        rw [h1.1]
        have H : Σ cb, PLift (c2 = (cb, true)) := is_true_singleton <| (is_true_of_append (bottom_frontier_is_true g2)).2
        rcases H with ⟨cb, cbspec⟩
        rw [cbspec.1]
        use f1, m1 ++ [(c1, true)] ++ f2, cb
        exact {down := by simp}
    rcases hb with ⟨front1, m1, caboose1, h1⟩
    rcases hd with ⟨front2, m2, caboose2, h2⟩
    right
    rw [h1.1, h2.1]
    use front1, m1 ++ [(caboose1, true)] ++ bot2 ++ [(front2, false)] ++ m2, caboose2
    exact {down := by simp}
  | vertical_append_one g1 g2 g1_ih g2_ih => assumption
  | vertical_append g1 g2 h g1_ih g2_ih =>
    right
    rcases g1_ih with h1 | h2
    · rw [h1.1] at h
      simp at h
    rcases g2_ih with h3 | h4
    · rw [h3.1, List.nil_append]
      rcases h2 with ⟨f1, m1, c1, spec⟩
      rename_i up2
      cases up2 with
      | nil =>
        use f1,m1, c1
        constructor
        rw [spec.1]; rfl
      | cons head tail =>
        have H : is_false [head] := by
          exact (is_false_of_append (right_frontier_is_false g2)).1
        rcases is_false_singleton H with ⟨hf, spec2⟩
        use hf, tail ++ [(f1, false)] ++ m1, c1
        constructor
        simp only [spec2.1, spec.1, List.cons_append, List.nil_append, List.append_assoc]
    rcases h2 with ⟨f1, m1, c1, spec1⟩
    rcases h4 with ⟨f2, m2, c2, spec2⟩
    rw [spec1.1, spec2.1]
    rename_i up2
    use f2, m2 ++ [(c2, true)] ++ up2 ++ [(f1, false)] ++ m1, c1
    exact {down := by simp}

end PartialGrid

-- change me
noncomputable def GridData_of_PartialGrid (h : PartialGrid a b c [] d) : GridData_option a b c d := by
  generalize hm : ([] : List (Option ℕ × Bool)) = m at h
  induction h with
  | single_cell h =>
    unfold GridData_option
    simp only [toList_to_vertical_edge_rev, toList_to_horizontal_edge]
    exact of_CellData h
  | empty a b =>
    apply congr_arg List.length at hm
    simp only [List.length_nil, List.length_append] at hm
    linarith
  | horizontal_append_one _ _ ih1 ih2 =>
    exact GridData_option_append_horiz (ih1 rfl) (ih2 hm)
  | horizontal_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at hm
    have H := GridData_option_append_horiz (g1_ih hm.1.symm) (g2_ih hm.2.2.symm)
    rw [hm.2.1, List.append_nil] at H
    exact H
  | vertical_append_one _ _ ih1 ih2 =>
    exact GridData_option_append_vert (ih1 rfl) (ih2 hm)
  | vertical_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at hm
    have H := GridData_option_append_vert (g1_ih hm.2.2.symm) (g2_ih hm.1.symm)
    rw [hm.2.1, List.nil_append] at H
    exact H
