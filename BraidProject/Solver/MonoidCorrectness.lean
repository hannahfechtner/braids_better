import BraidProject.BraidLocalization
import BraidProject.SemiThueToGrid
import BraidProject.Solver.Monoid

namespace Braid

open Relations

theorem BraidMonoidInf.eq_of_monoid_solver (h : monoid_solver a b) : BraidMonoidInf.mk a =
    BraidMonoidInf.mk b := by
  simp only [monoid_solver, decide_eq_true_eq] at h
  have ha : a = List.map (fun x => x.1) (to_horizontal_edge_no_epsilon a) :=
    project_first_element_to_horizontal_edge_no_epsilon.symm
  have hb : b = List.map (fun x => x.1) (to_horizontal_edge_no_epsilon b) :=
    project_first_element_to_horizontal_edge_no_epsilon.symm
  rw [ha, hb]
  apply braidMonoid_mk_eq_of_braidGroup_mk_eq_of_positive ?_ is_true_to_horizontal_edge_no_epsilon is_true_to_horizontal_edge_no_epsilon
  have := @reverse_pair_spec a b
  rw [h] at this
  apply SemiThueDataDerivation.toSemiThueData at this
  have := SemiThueData.reversing.to_braid_group_equiv this
  rw [← FreeGroup.mul_mk, map_mul, ← FreeGroup.one_eq_mk, map_one] at this
  have : (BraidGroupInf.mk (FreeGroup.mk (to_vertical_edge_no_epsilon a)))⁻¹ *
      BraidGroupInf.mk (FreeGroup.mk (to_vertical_edge_no_epsilon a)) *
      BraidGroupInf.mk (FreeGroup.mk (to_horizontal_edge_no_epsilon b)) =
      (BraidGroupInf.mk (FreeGroup.mk (to_vertical_edge_no_epsilon a)))⁻¹ * 1 := by
    rw [← this]
    simp
  rw [BraidGroupInf.mk_to_vertical_edge, inv_inv, mul_inv_cancel, one_mul, mul_one] at this
  exact this.symm

-- alternative version
theorem BraidMonoidInf.eq_of_monoid_solver' (h : monoid_solver a b) : BraidMonoidInf.mk a =
    BraidMonoidInf.mk b := by
  simp only [monoid_solver, decide_eq_true_eq] at h
  have := (reverse_pair a b).2
  rw [h] at this
  apply SemiThueDataDerivation.toSemiThueData at this
  have empty_to_sink : ([] : List (ℕ × Bool)) = (to_horizontal_edge_no_epsilon [] ++ to_vertical_edge_no_epsilon []) := rfl
  rw [empty_to_sink] at this
  have := BraidMonoidInf.eq_of_SemiThueData_reversing_grid_frame this
  erw [List.append_nil, List.append_nil] at this
  exact this

end Braid
