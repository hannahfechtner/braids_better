import BraidProject.Relations
import BraidProject.SemiThue
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.PartialGrid.Build
import BraidProject.PartialGrid.FrontierToSink

namespace Braid

theorem SemiThueData.toSemiThue_reversing (h : SemiThueData reversing a b) : SemiThue reversing_prop a b := by
  induction h with
  | refl => rfl
  | step c d h1 =>
    cases h1 with
    | basic h =>
      rename_i i j
      rw [Nat.eq_of_dist_eq_zero h]
      exact SemiThue.step c d reversing_prop.basic
    | apart h => exact SemiThue.step c d (reversing_prop.apart h)
    | close h => exact SemiThue.step c d (reversing_prop.close h)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem SemiThueData.ofSemiThue_reversing (h : SemiThue reversing_prop a b) : Nonempty (SemiThueData reversing a b) := by
  induction h with
  | refl => apply Nonempty.intro (SemiThueData.refl)
  | step c d h1 =>
    cases h1 with
    | basic =>
      exact Nonempty.intro (SemiThueData.step c d (reversing.basic (by simp)))
    | apart h => exact Nonempty.intro (SemiThueData.step c d (reversing.apart h))
    | close h => exact Nonempty.intro (SemiThueData.step c d (reversing.close h))
  | trans _ _ ih1 ih2 => exact Nonempty.intro (SemiThueData.trans (Classical.choice ih1) (Classical.choice ih2))


theorem eq_of_SemiThue_false (h : SemiThue reversing_prop a b) (ha : SignedList.is_false a) : a = b := by
  induction h with
  | refl => rfl
  | step _ _ h =>
    rcases h
    · rename_i j
      specialize ha (j, true) (by simp)
      simp at ha
    · rename_i i j hij
      specialize ha (j, true) (by simp)
      simp at ha
    rename_i i j hij
    specialize ha (j, true) (by simp)
    simp at ha
  | trans _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

theorem eq_of_SemiThue_true (h : SemiThue reversing_prop a b) (ha : SignedList.is_true a) : a = b := by
  induction h with
  | refl => rfl
  | step _ _  h =>
    rcases h
    · rename_i i
      specialize ha (i, false) (by simp)
      simp at ha
    · rename_i i j hij
      specialize ha (i, false) (by simp)
      simp at ha
    rename_i i j hij
    specialize ha (i, false) (by simp)
    simp at ha
  | trans _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

theorem eq_of_SemiThue_SignedList.PosNegData (h : SemiThue reversing_prop a b) (ha : SignedList.PosNegData a) : a = b := by
  induction h with
  | refl => rfl
  | step _ _ h =>
    rcases ha with ⟨one, two, one_true, two_false, spec⟩
    rcases h
    · rename_i c d j
      have spec_rw : c ++ [(j, false), (j, true)] ++ d =
        (c ++ [(j, false)]) ++ ((j, true):: d) := by simp
      rw [spec_rw] at spec
      rcases List.append_eq_append_iff.mp spec with
        ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
      · rw [spec1] at one_true
        specialize one_true (j, false) (by simp)
        simp at one_true
      rw [spec2] at two_false
      specialize two_false (j, true) (by simp)
      simp at two_false
    · rename_i c d i j hij
      have spec_rw : c ++ [(i, false), (j, true)] ++ d =
        (c ++ [(i, false)]) ++ ((j, true):: d) := by simp
      rw [spec_rw] at spec
      rcases List.append_eq_append_iff.mp spec with
        ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
      · rw [spec1] at one_true
        specialize one_true (i, false) (by simp)
        simp at one_true
      rw [spec2] at two_false
      specialize two_false (j, true) (by simp)
      simp at two_false
    rename_i c d i j hij
    have spec_rw : c ++ [(i, false), (j, true)] ++ d =
      (c ++ [(i, false)]) ++ ((j, true):: d) := by simp
    rw [spec_rw] at spec
    rcases List.append_eq_append_iff.mp spec with
      ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
    · rw [spec1] at one_true
      specialize one_true (i, false) (by simp)
      simp at one_true
    rw [spec2] at two_false
    specialize two_false (j, true) (by simp)
    simp at two_false
  | trans _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

noncomputable def restricted_confluence (h1 : SemiThue reversing_prop
    (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
    (h2 : SemiThue reversing_prop (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) d)
    (ha : a.length > 0) (hb : b.length > 0) :
    ∃ e, SemiThue reversing_prop c e ∧ SemiThue reversing_prop d e := by
  have H1 := PartialGrid.of_SemiThueData_reversing (Classical.choice (SemiThueData.ofSemiThue_reversing h1)) ha hb
  have H2 := PartialGrid.of_SemiThueData_reversing (Classical.choice (SemiThueData.ofSemiThue_reversing h2)) ha hb
  rcases H1 with ⟨c1, d1, e1, pg, ⟨rm1⟩, ⟨rfl⟩⟩
  rcases H2 with ⟨c2, d2, e2, pg2, ⟨rm2⟩, ⟨rfl⟩⟩
  have H2 : Σ c3 d3, GridData a b c3 d3 := GridData.existence a b
  rcases H2 with ⟨c3, d3, gt⟩
  use (to_horizontal_edge_no_epsilon c3 ++ to_vertical_edge_no_epsilon d3)
  constructor
  · exact PartialGrid.frontier_reverses_to_grid pg toSignedList_to_vertical_edge
      toSignedList_to_horizontal_edge gt
  exact PartialGrid.frontier_reverses_to_grid pg2 toSignedList_to_vertical_edge
      toSignedList_to_horizontal_edge gt
