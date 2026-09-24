import BraidProject.Solver.Group
import BraidProject.Solver.MonoidCorrectness
import BraidProject.SemiThueReversing
import BraidProject.Additions.FreeGroup

namespace Braid

open Nat

private theorem recover_from_is_true (h : SignedList.is_true d) :
    List.map (fun x => (x, true)) (List.map (fun x ↦ x.1) d) = (d : List (ℕ × Bool)) := by
  induction d with
  | nil => rfl
  | cons head tail ih =>
    have tt : SignedList.is_true tail := (SignedList.is_true_of_cons h).2
    specialize ih tt
    have ht : SignedList.is_true [head] := (SignedList.is_true_of_cons h).1
    specialize ht head (by simp)
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    rw [← ht]

private theorem recover_from_is_false {α : Type} {e : List (α × Bool)} (h : SignedList.is_false e) :
    (FreeGroup.mk (List.map (fun x ↦ (x, true)) (List.map (fun x ↦ x.1) e.reverse)))⁻¹ = FreeGroup.mk e := by
  induction e with
  | nil => rfl
  | cons head tail ih =>
    have tf : SignedList.is_false tail := (SignedList.is_false_of_cons h).2
    specialize ih tf
    have hf : SignedList.is_false [head] := (SignedList.is_false_of_cons h).1
    specialize hf head (by simp)
    conv => rhs; rw [FreeGroup.mk_cons, ← ih]
    rw [FreeGroup.inv_mk, List.reverse_cons, List.map_append, List.map_append,
      FreeGroup.invRev_append, ← FreeGroup.mul_mk]
    congr
    simp [FreeGroup.invRev, ← hf]

theorem BraidGroupInf.eq_of_braid_word_solver_true (h : braid_word_solver a b = true) :
    BraidGroupInf.mk (FreeGroup.mk a) = BraidGroupInf.mk (FreeGroup.mk b) := by
  rcases dede : (reverse_word (a ++ (FreeGroup.invRev b))).ordered with ⟨d, e, hde⟩
  have H := BraidMonoidInf.eq_of_monoid_solver h
  have H2 := SemiThueData.reversing.to_braid_group_equiv ((reverse_word (a ++ (FreeGroup.invRev b))).derivation)
  rw [hde.1.2.2] at H2
  rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul] at H2
  have d_is : (reverse_word (a ++ FreeGroup.invRev b)).ordered.fst = d := by aesop
  rw [d_is] at H
  have e_is : (reverse_word (a ++ FreeGroup.invRev b)).ordered.2.1 = e := by
    rw [dede]
  rw [e_is] at H
  apply BraidGroupInf.eq_of_BraidMonoidInf_eq at H
  rw [recover_from_is_true hde.1.1] at H
  have He : BraidGroupInf.mk (FreeGroup.mk e) = (BraidGroupInf.mk (FreeGroup.mk d))⁻¹ := by
    rw [← H, ← map_inv, recover_from_is_false hde.1.2.1]
  rw [He, mul_inv_cancel] at H2
  apply (mul_left_inj (BraidGroupInf.mk
    (FreeGroup.mk (FreeGroup.invRev b)))⁻¹).mpr at H2
  rw [mul_inv_cancel_right, one_mul] at H2
  rw [H2, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev_invRev]
