import BraidProject.Solver.Group
import BraidProject.Solver.MonoidCorrectness
import BraidProject.Solver.Reversing

namespace Braid

-- this is more basic, move me!
theorem bm_to_bg (h : BraidMonoidInf.mk a =
  BraidMonoidInf.mk b) :
  BraidGroupInf.mk (FreeGroup.mk (to_horizontal_edge_no_epsilon a)) =
  BraidGroupInf.mk (FreeGroup.mk (to_horizontal_edge_no_epsilon b)) := by
  apply PresentedMonoid.exact at h
  induction h with
  | of x y h =>
    cases h with
    | adjacent i => exact Braid.BraidGroupInf.braid dist_succ
    | separated i j h =>
      apply Braid.BraidGroupInf.comm
      apply or_dist_iff.mpr
      left; exact h
  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | mul _ _ ih1 ih2 =>
    rw [to_horizontal_edge_no_epsilon_mul, to_horizontal_edge_no_epsilon_mul, ← FreeGroup.mul_mk,  ← FreeGroup.mul_mk,
      map_mul, map_mul, ih1, ih2]

open Braid
theorem pg_mk_to_horizontal_edge_no_epsilon_inv :
  (BraidGroupInf.mk (FreeGroup.mk (to_horizontal_edge_no_epsilon a)))⁻¹ =
  BraidGroupInf.mk (FreeGroup.mk (to_vertical_edge_no_epsilon a)) := by
  rw [← map_inv, FreeGroup.inv_mk]
  congr
  unfold to_horizontal_edge_no_epsilon to_vertical_edge_no_epsilon FreeGroup.invRev
  simp

theorem recover_from_is_false (h : SignedList.is_false d) : to_vertical_edge_no_epsilon (List.map (fun x ↦ x.1) d).reverse = (d : List (ℕ × Bool)) := by
  rw [to_vertical_edge_no_epsilon_reverse]
  have H : (to_vertical_edge_no_epsilon (List.map (fun x ↦ x.1) d)).reverse.reverse = d.reverse := by
    rw [List.reverse_reverse]
    induction d with
    | nil => simp [to_vertical_edge_no_epsilon]
    | cons head tail ih =>
      have tf : SignedList.is_false tail := (SignedList.is_false_of_cons h).2
      unfold to_vertical_edge_no_epsilon at ih
      simp [to_vertical_edge_no_epsilon, ih tf]
      have H2 := (SignedList.is_false_of_cons h).1
      specialize H2 head (by simp)
      simp [← H2]
  exact List.reverse_injective H

theorem recover_from_is_true (h : SignedList.is_true d) : to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) d) = (d : List (ℕ × Bool)) := by
  induction d with
  | nil => simp [to_horizontal_edge_no_epsilon]
  | cons head tail ih =>
    have tt : SignedList.is_true tail := (SignedList.is_true_of_cons h).2
    specialize ih tt
    simp only [to_horizontal_edge_no_epsilon, List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · have ht : SignedList.is_true [head] := (SignedList.is_true_of_cons h).1
      specialize ht head (by simp)
      simp [← ht]
    rw [← ih]
    unfold to_horizontal_edge_no_epsilon
    simp

--okay this is fine
theorem solver_g_correct_one_direction : group_solver a b = true →
    BraidGroupInf.mk (FreeGroup.mk a) =
    BraidGroupInf.mk (FreeGroup.mk b) := by
  intro h
  unfold group_solver at h
  rcases dede : (reverse_word (a ++ (FreeGroup.invRev b))).ordered with ⟨d, e, hde⟩
  have H := correct_one_dir h
  have H2 := SemiThueData_reversing_to_braid_group_equiv ((reverse_word (a ++ (FreeGroup.invRev b))).steps)
  rw [hde.1.2.2] at H2
  rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul] at H2
  have d_is : (reverse_word (a ++ FreeGroup.invRev b)).ordered.fst = d := by aesop
  rw [d_is] at H
  have e_is : (reverse_word (a ++ FreeGroup.invRev b)).ordered.2.1 = e := by
    rw [dede]
  rw [e_is] at H
  apply bm_to_bg at H
  apply (mul_right_inj (BraidGroupInf.mk
    (FreeGroup.mk (to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) e.reverse))))⁻¹).mpr at H
  simp at H
  rw [pg_mk_to_horizontal_edge_no_epsilon_inv, recover_from_is_true hde.1.1, recover_from_is_false hde.1.2.1] at H
  apply (mul_right_inj ((BraidGroupInf.mk
        (FreeGroup.mk e))⁻¹)).mpr at H
  apply (mul_left_inj (BraidGroupInf.mk
        (FreeGroup.mk e))).mpr at H
  rw [mul_one, inv_mul_cancel, inv_mul_cancel_left] at H
  rw [← H] at H2
  apply (mul_left_inj (BraidGroupInf.mk
    (FreeGroup.mk (FreeGroup.invRev b)))⁻¹).mpr at H2
  rw [mul_inv_cancel_right, one_mul] at H2
  rw [H2, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev_invRev]
