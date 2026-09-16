import BraidProject.Solver.MonoidCorrectness
import BraidProject.PartialGrid.NestedFrame
import BraidProject.SemiThue
import BraidProject.Relations
import BraidProject.PartialGrid.FrontierPossibilities
import BraidProject.PartialGrid.FrontierToSink
import BraidProject.SemiThueReversing

namespace Braid

open PartialGrid Relations

theorem monoid_solver_true_of_BraidMonoidInf_eq (h : BraidMonoidInf.mk a =
    BraidMonoidInf.mk b) : monoid_solver a b := by
  have H : grid (a*1) (b*1) 1 1 := by
    apply Grid.of_BraidMonoidInf_eq
    rw [mul_one, mul_one]
    exact h
  rw [mul_one, mul_one] at H
  have hpg := of_SemiThueData_reversing
    (Classical.choice (SemiThueData.ofSemiThue_reversing
    (GridData.to_SemiThue_reversing ((GridData.of_grid H).some))))
  have H1 := SemiThueDataDerivation.toSemiThueData <| @reverse_pair_spec a b
  rcases (reverse_pair_PosNegData a b) with ⟨c, d, hc, hd, hs⟩
  simp only [monoid_solver, decide_eq_true_eq, hs]
  rw [hs] at H1
  have hc1 : ∃ c1, c = to_horizontal_edge_no_epsilon c1 := by
    use List.map (fun x => x.1) c
    exact (to_horizontal_edge_no_epsilon_no_bool hc).symm
  have hc2 : ∃ d1, d = to_vertical_edge_no_epsilon d1 := by
    use List.map (fun x => x.1) d.reverse
    exact (to_vertical_edge_no_epsilon_no_bool hd).symm
  rcases hc1 with ⟨c1, rfl⟩
  rcases hc2 with ⟨d1, rfl⟩
  have := Grid.unicity (Grid.of_SemiThueData_reversing H1) _ _ H
  rw [← this.1, ← this.2]
  rfl

-- alternative version
theorem monoid_solver_true_of_BraidMonoidInf_eq' (h : BraidMonoidInf.mk a =
    BraidMonoidInf.mk b) : monoid_solver a b := by
  have H : grid (a*1) (b*1) 1 1 := by
    apply Grid.of_BraidMonoidInf_eq
    rw [mul_one, mul_one]
    exact h
  rw [mul_one, mul_one] at H
  have hr := GridData.to_SemiThue_reversing (GridData.of_grid H).some
  change SemiThue reversing_prop _ [] at hr
  have hpg := of_SemiThueData_reversing (Classical.choice (SemiThueData.ofSemiThue_reversing hr))
  simp only [monoid_solver, decide_eq_true_eq]
  rcases restricted_confluence hr (SemiThueData.toSemiThue_reversing
    (SemiThueDataDerivation.toSemiThueData reverse_pair_spec)) with ⟨e, h1, h2⟩
  rw [(eq_of_SemiThue_reversing_true h1 SignedList.is_true_nil)]
  exact eq_of_SemiThue_reversing_SignedList.PosNegData h2 (reverse_pair_PosNegData _ _)
