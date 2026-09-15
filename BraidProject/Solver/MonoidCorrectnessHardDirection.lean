import BraidProject.Solver.MonoidCorrectness
import BraidProject.PartialGrid.NestedFrame
import BraidProject.SemiThue
import BraidProject.Relations
import BraidProject.PartialGrid.FrontierPossibilities
import BraidProject.PartialGrid.FrontierToSink
import BraidProject.SemiThueReversing

namespace Braid

open PartialGrid Relations

theorem correct_other_dir (h : BraidMonoidInf.mk a =
    BraidMonoidInf.mk b) : monoid_solver a b := by
  have H : grid (a*1) (b*1) 1 1 := by
    apply Grid.of_BraidMonoidInf_eq
    rw [mul_one, mul_one]
    exact h
  rw [mul_one, mul_one] at H
  have Ht : GridData a b 1 1 := by
    exact (GridData.of_grid H).some
  have hr := GridData.to_SemiThue_reversing Ht
  change SemiThue reversing_prop _ [] at hr
  have hpg := of_SemiThueData_reversing (Classical.choice (SemiThueData.ofSemiThue_reversing (GridData.to_SemiThue_reversing Ht)))
  simp [monoid_solver]
  have H := @reverse_pair_spec a b
  rcases restricted_confluence hr (SemiThueData.toSemiThue_reversing
    (SemiThueDataDerivation.toSemiThueData H)) with ⟨e, h1, h2⟩
  rw [(eq_of_SemiThue_reversing_true h1 SignedList.is_true_nil)]
  apply eq_of_SemiThue_reversing_SignedList.PosNegData h2 (reverse_pair_PosNegData _ _)

theorem SignedOptionList.to_List_eq_nil_toSignedList_eq_nil (h : SignedOptionList.toList a = []) :
    SignedOptionList.toSignedList a = [] := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    unfold SignedOptionList.toList at h
    split at h
    · aesop
    · aesop
    simp_all

theorem correct_other_dir' (h : BraidMonoidInf.mk a =
    BraidMonoidInf.mk b) : monoid_solver a b := by
  have H : grid (a*1) (b*1) 1 1 := by
    apply Grid.of_BraidMonoidInf_eq
    rw [mul_one, mul_one]
    exact h
  rw [mul_one, mul_one] at H
  have Ht : GridData a b 1 1 := by
    exact (GridData.of_grid H).some
  have hpg := of_SemiThueData_reversing (Classical.choice (SemiThueData.ofSemiThue_reversing (GridData.to_SemiThue_reversing Ht)))
  have H := SemiThueDataDerivation.toSemiThueData <| @reverse_pair_spec a b
  simp only [monoid_solver, decide_eq_true_eq]
  rcases (reverse_pair_PosNegData a b) with ⟨c, d, hc, hd, hs⟩
  rw [hs]
  rw [hs] at H
  have hc1 : ∃ c1, c = to_horizontal_edge_no_epsilon c1 := by
    use List.map (fun x => x.1) c
    exact (to_horizontal_edge_no_epsilon_no_bool hc).symm
  have hc2 : ∃ d1, d = to_vertical_edge_no_epsilon d1 := by
    use List.map (fun x => x.1) d.reverse
    exact (to_vertical_edge_no_epsilon_no_bool hd).symm
  rcases hc1 with ⟨c1, rfl⟩
  rcases hc2 with ⟨d1, rfl⟩
  have := Grid.unicity (grid_of_rev H) _ _ (GridData.to_grid Ht)
  rw [← this.1, ← this.2]
  rfl
