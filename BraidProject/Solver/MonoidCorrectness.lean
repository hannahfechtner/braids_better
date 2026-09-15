import BraidProject.Solver.Monoid
import BraidProject.SemiThueReversing
-- import BraidProject.BraidLocalization
import BraidProject.PartialGrid.ToGrid
import BraidProject.SemiThueToGrid

namespace Braid

open Relations

theorem recover_edges_of_move_ones_split
    (h : SignedOptionList.toSignedList b' = to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d)
    (h1 : bot ++ up = move_ones b') (hbot : SignedList.is_true bot) (hup : SignedList.is_false up) :
    (SignedOptionList.toList up.reverse) = d ∧ SignedOptionList.toList bot = c := by
  have two := congr_arg SignedOptionList.toSignedList h1
  simp only [SignedOptionList.toSignedList_append, toSignedList_move_ones] at two
  rw [← two] at h
  have ⟨hbot_eq, hup_eq⟩ := SignedList.parts_eq_of_true_false_eq
    (SignedOptionList.toSignedList_is_true hbot) is_true_to_horizontal_edge_no_epsilon
    (SignedOptionList.toSignedList_is_false hup) is_false_to_vertical_edge_no_epsilon h
  exact ⟨recover_of_toSignedList_to_vertical_edge_no_epsilon hup_eq,
    recover_of_toSignedList_to_horizontal_edge_no_epsilon hbot_eq.symm⟩

theorem correct_one_dir (h : monoid_solver a b) : BraidMonoidInf.mk a =
  BraidMonoidInf.mk b := by
  simp only [monoid_solver, decide_eq_true_eq] at h
  rw [← List.append_nil a, ← List.append_nil b]
  apply bm_equiv_of_reversing'
  conv =>
    enter [3]
    rw [to_horizontal_edge_no_epsilon, to_vertical_edge_no_epsilon]
    simp only [List.map_nil, List.reverse_nil, List.append_nil]
  have H := @reverse_pair_spec a b
  rw [h] at H
  exact SemiThueDataDerivation.toSemiThueData H

theorem correct_one_dir' (h : monoid_solver a b) : BraidMonoidInf.mk a =
  BraidMonoidInf.mk b := by
  simp only [monoid_solver, decide_eq_true_eq] at h
  have := (reverse_pair a b).2
  rw [h] at this
  apply SemiThueDataDerivation.toSemiThueData at this
  have empty_to_sink : ([] : List (ℕ × Bool)) = (to_horizontal_edge_no_epsilon [] ++ to_vertical_edge_no_epsilon []) := rfl
  rw [empty_to_sink] at this
  have := Grid.braid_monoid_eq_of_grid (grid_of_rev this)
  simp only [map_mul, mul_left_inj] at this
  exact this

end Braid
