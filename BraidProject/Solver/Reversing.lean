import BraidProject.Relations
import BraidProject.SemiThue
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.PartialGrid.Build

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

theorem SemiThue_reversing_nil (h : SemiThue reversing_prop a b) (ha : a = []) : b = [] := by
  induction h with
  | refl => exact ha
  | step c d h => cases h ; all_goals simp at ha
  | trans _ _ _ _ => aesop

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

theorem SemiThueData_reversing_to_braid_group_equiv (h : SemiThueData reversing a b) :
  Braid.BraidGroupInf.mk (FreeGroup.mk a) =
  Braid.BraidGroupInf.mk (FreeGroup.mk b) := by
  induction h with
  | refl => rfl
  | step h =>
    rename_i e f g i
    unfold Braid.BraidGroupInf.mk
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
      map_mul, map_mul, map_mul, map_mul,
      mul_left_inj, mul_right_inj]
    cases i with
    | basic =>
      rename_i i j hij
      apply Nat.eq_of_dist_eq_zero at hij
      rw [← hij]
      change (PresentedGroup.mk ((ArtinTits.Group.relation_set Braid.BraidMatrixInf)))
        (FreeGroup.mk ([(i, false)] ++ [(i, true)])) = _
      rw [← FreeGroup.mul_mk]
      unfold FreeGroup.mk
      congr
      exact eq_div_iff_mul_eq'.mp rfl
    | apart h =>
      rename_i i j
      change (Braid.σ i)⁻¹ * Braid.σ j = Braid.σ j * (Braid.σ i)⁻¹
      apply (mul_right_inj (Braid.σ i)).mp
      apply (mul_left_inj (Braid.σ i)).mp
      group
      symm
      exact Braid.BraidGroupInf.comm h
    | close h =>
      rename_i i j
      change (Braid.σ i)⁻¹ * Braid.σ j = Braid.σ j *  Braid.σ i * (Braid.σ j)⁻¹ * (Braid.σ i)⁻¹
      apply (mul_right_inj (Braid.σ i)).mp
      apply (mul_left_inj (Braid.σ i)).mp
      apply (mul_left_inj (Braid.σ j)).mp
      group
      symm
      exact Braid.BraidGroupInf.braid h
  | trans _ _ ih1 ih2 =>
    exact ih1.trans ih2

noncomputable def grid_to_rev (h : GridData a b c d) : SemiThue reversing_prop
  (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) (to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d) := by
  induction h with
  | empty => exact SemiThue.refl
  | top_bottom i => exact SemiThue.refl
  | sides i => exact SemiThue.refl
  | top_left i => exact SemiThue.of_rel (reversing_prop.basic)
  | adjacent i k h => exact SemiThue.of_rel (reversing_prop.close h)
  | separated i j h => exact SemiThue.of_rel (reversing_prop.apart h)
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [to_vertical_edge_no_epsilon_mul, to_vertical_edge_no_epsilon_mul, List.append_assoc]
    apply (SemiThue.append_left h1_ih).trans
    rw [← List.append_assoc, ← List.append_assoc]
    exact SemiThue.append_right h2_ih
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [to_horizontal_edge_no_epsilon_mul, to_horizontal_edge_no_epsilon_mul, ← List.append_assoc]
    apply (SemiThue.append_right h1_ih).trans
    rw [List.append_assoc, List.append_assoc]
    exact SemiThue.append_left h2_ih
