import BraidProject.Solver.MonoidCorrectness
import BraidProject.PartialGrid.NestedFrame
import BraidProject.SemiThue
import BraidProject.Relations
import BraidProject.PartialGrid.FrontierPossibilities
import BraidProject.PartialGrid.FrontierToSink
import BraidProject.Solver.Reversing

namespace Braid

open PartialGrid
theorem correct_other_dir (h : BraidMonoidInf.mk a =
    BraidMonoidInf.mk b) : monoid_solver a b := by
  have H : grid (a*1) (b*1) 1 1 := by
    apply Grid.of_mk_eq_mk
    rw [mul_one, mul_one]
    exact h
  rw [mul_one, mul_one] at H
  have Ht : GridData a b 1 1 := by
    exact (GridData.of_grid H).some
  have hr := grid_to_rev Ht
  change SemiThue reversing_prop _ [] at hr
  have hpg := of_SemiThueData_reversing (Classical.choice (SemiThueData.ofSemiThue_reversing (grid_to_rev Ht)))
  match a with
  | [] =>
    match b with
    | [] =>
      simp [monoid_solver]
    | b1 :: b2 =>
      simp [monoid_solver]
      have H := eq_of_SemiThue_true hr is_true_to_horizontal_edge_no_epsilon
      simp [to_horizontal_edge_no_epsilon] at H
  | a1 :: a2 =>
    match b with
    | [] =>
      simp [monoid_solver]
      simp only [to_horizontal_edge_no_epsilon, List.map_nil,
        List.append_nil] at hr
      have H := eq_of_SemiThue_false hr is_false_to_vertical_edge_no_epsilon
      simp [to_vertical_edge_no_epsilon] at H
    | b1 :: b2 =>
      simp [monoid_solver]
      have H := @reverse_pair_spec (a1 :: a2) (b1 :: b2) (by simp) (by simp)
      rcases restricted_confluence hr (SemiThueData.toSemiThue_reversing
        (SemiThueDataDerivation.reversing.toSemiThueData_with_length H).1)
        (by simp) (by simp) with ⟨e, h1, h2⟩
      rw [(eq_of_SemiThue_true h1 SignedList.is_true_nil)]
      apply eq_of_SemiThue_SignedList.PosNegData h2 (reverse_pair_PosNegData _ _ _ _)

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
    apply Grid.of_mk_eq_mk
    rw [mul_one, mul_one]
    exact h
  rw [mul_one, mul_one] at H
  have Ht : GridData a b 1 1 := by
    exact (GridData.of_grid H).some
  have hpg := of_SemiThueData_reversing (Classical.choice (SemiThueData.ofSemiThue_reversing (grid_to_rev Ht)))
  match a with
  | [] =>
    match b with
    | [] =>
      simp [monoid_solver]
    | b1 :: b2 =>
      have := GridData.DeterminativeSpine.one_word Ht rfl
      change [] = _ ∧ _ at this
      simp at this
  | a1 :: a2 =>
    match b with
    | [] =>
      have := GridData.DeterminativeSpine.word_one Ht rfl
      change _ ∧ [] = _ at this
      simp at this
    | b1 :: b2 =>
      have H := SemiThueDataDerivation.toSemiThueData <| @reverse_pair_spec (a1 :: a2) (b1 :: b2) (by simp) (by simp)
      simp only [monoid_solver, decide_eq_true_eq]
      rcases (reverse_pair_PosNegData (a1 :: a2) (b1 :: b2) (by simp) (by simp)) with ⟨c, d, hc, hd, hs⟩
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
