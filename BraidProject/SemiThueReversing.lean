import BraidProject.Relations
import BraidProject.SemiThue
import BraidProject.DataCarrying.SemiThue
import BraidProject.DataCarrying.SignedList
import BraidProject.BraidGroup
import BraidProject.ToEdge
import BraidProject.GridData.Basic

namespace Braid

open Relations

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

theorem nil_of_SemiThue_reversing_nil (h : SemiThue reversing_prop a b) (ha : a = []) : b = [] := by
  induction h with
  | refl => exact ha
  | step c d h => cases h ; all_goals simp at ha
  | trans _ _ _ _ => aesop

theorem eq_of_SemiThue_reversing_false (h : SemiThue reversing_prop a b) (ha : SignedList.is_false a) : a = b := by
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

theorem length_zero_of_SemiThueDataDerivation_reversing_false (h : SemiThueDataDerivation reversing a b) (ha : SignedList.is_false a) : h.length reversing.length = 0 := by
  induction h with
  | refl => rfl
  | step h1 h2 ih =>
    apply SemiThueDataDerivation.toSemiThueData at h1
    have := eq_of_SemiThue_reversing_false <| SemiThueData.to_SemiThue h1 (fun a b => reversing_subset_reversing_prop)
    specialize this ha
    rw [this] at ha
    rcases reversing.spec h2 with ⟨a1, a2, ⟨rfl⟩⟩
    specialize ha (a2, true) (by simp)
    simp at ha

theorem eq_of_SemiThue_reversing_true (h : SemiThue reversing_prop a b) (ha : SignedList.is_true a) : a = b := by
  induction h with
  | refl => rfl
  | step _ _ h =>
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

theorem length_zero_of_SemiThueDataDerivation_reversing_true (h : SemiThueDataDerivation reversing a b) (ha : SignedList.is_true a) : h.length reversing.length = 0 := by
  induction h with
  | refl => rfl
  | step h1 h2 ih =>
    apply SemiThueDataDerivation.toSemiThueData at h1
    have := eq_of_SemiThue_reversing_true <| SemiThueData.to_SemiThue h1 (fun a b => reversing_subset_reversing_prop)
    specialize this ha
    rw [this] at ha
    rcases reversing.spec h2 with ⟨a1, a2, ⟨rfl⟩⟩
    specialize ha (a1, false) (by simp)
    simp at ha

theorem eq_of_SemiThue_reversing_SignedList.PosNegData (h : SemiThue reversing_prop a b) (ha : SignedList.PosNegData a) : a = b := by
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
        ⟨mid, rfl, spec2⟩ | ⟨mid, spec1, rfl⟩
      · specialize one_true (j, false) (by simp)
        simp at one_true
      specialize two_false (j, true) (by simp)
      simp at two_false
    · rename_i c d i j hij
      have spec_rw : c ++ [(i, false), (j, true)] ++ d =
        (c ++ [(i, false)]) ++ ((j, true):: d) := by simp
      rw [spec_rw] at spec
      rcases List.append_eq_append_iff.mp spec with
        ⟨mid, rfl, spec2⟩ | ⟨mid, spec1, rfl⟩
      · specialize one_true (i, false) (by simp)
        simp at one_true
      specialize two_false (j, true) (by simp)
      simp at two_false
    rename_i c d i j hij
    have spec_rw : c ++ [(i, false), (j, true)] ++ d =
      (c ++ [(i, false)]) ++ ((j, true):: d) := by simp
    rw [spec_rw] at spec
    rcases List.append_eq_append_iff.mp spec with
      ⟨mid, rfl, spec2⟩ | ⟨mid, spec1, rfl⟩
    · specialize one_true (i, false) (by simp)
      simp at one_true
    specialize two_false (j, true) (by simp)
    simp at two_false
  | trans _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

theorem SemiThueData.reversing.to_braid_group_equiv (h : SemiThueData reversing a b) :
  Braid.BraidGroupInf.mk (FreeGroup.mk a) =
  Braid.BraidGroupInf.mk (FreeGroup.mk b) := by
  induction h with
  | refl => rfl
  | step e f h =>
    rename_i c d
    simp [← FreeGroup.mul_mk]
    cases h with
    | basic h =>
      rename_i i j
      have : i = j := Nat.eq_of_dist_eq_zero h
      subst this
      change BraidGroupInf.mk (FreeGroup.mk ([(i, false)] ++ [(i, true)]) ) = 1
      rw [← FreeGroup.mul_mk]
      change BraidGroupInf.mk ((FreeGroup.of i)⁻¹ * FreeGroup.of i) = 1
      simp
    | apart h =>
      rename_i i j
      change BraidGroupInf.mk (FreeGroup.mk ([(i, false)] ++ [(j, true)]) ) =
        BraidGroupInf.mk (FreeGroup.mk ([(j, true)] ++ [(i, false)]) )
      rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul]
      change (σ i)⁻¹ * σ j = σ j * (σ i)⁻¹
      apply inv_mul_eq_of_eq_mul
      rw [← mul_assoc]
      exact eq_mul_inv_of_mul_eq (BraidGroupInf.comm h).symm
    | close h =>
      rename_i i j
      change BraidGroupInf.mk (FreeGroup.mk ([(i, false)] ++ [(j, true)])) =
        BraidGroupInf.mk (FreeGroup.mk ([(j, true)] ++ [(i, true)] ++ [(j, false)] ++ [(i, false)]))
      simp only [← FreeGroup.mul_mk]
      change (σ i)⁻¹ * σ j = σ j * σ i * (σ j)⁻¹ * (σ i)⁻¹
      apply inv_mul_eq_of_eq_mul
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
      exact eq_mul_inv_of_mul_eq (mul_inv_eq_of_eq_mul (BraidGroupInf.braid h)).symm
  | trans _ _ _ _ => aesop

noncomputable def GridData.to_SemiThue_reversing (h : GridData a b c d) : SemiThue reversing_prop
  (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) (to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d) := by
  induction h with
  | empty => exact SemiThue.refl
  | top_bottom i => exact SemiThue.refl
  | sides i => exact SemiThue.refl
  | top_left i => exact SemiThue.of_rel (reversing_prop.basic)
  | adjacent i k h => exact SemiThue.of_rel (reversing_prop.close h)
  | separated i j h => exact SemiThue.of_rel (reversing_prop.apart h)
  | vertical h1 h2 h1_ih h2_ih =>
    rw [to_vertical_edge_no_epsilon_mul, to_vertical_edge_no_epsilon_mul, List.append_assoc]
    apply (SemiThue.append_left h1_ih).trans
    rw [← List.append_assoc, ← List.append_assoc]
    exact SemiThue.append_right h2_ih
  | horizontal h1 h2 h1_ih h2_ih =>
    rw [to_horizontal_edge_no_epsilon_mul, to_horizontal_edge_no_epsilon_mul, ← List.append_assoc]
    apply (SemiThue.append_right h1_ih).trans
    rw [List.append_assoc, List.append_assoc]
    exact SemiThue.append_left h2_ih
