import BraidProject.PartialGrid.ToGrid
import BraidProject.ReversingToGridStyle
import BraidProject.SemiThueReversing
import BraidProject.PartialGrid.Build

namespace Braid

open Relations

theorem grid_of_rev
    (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b)
      (to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d)) :
    grid a b c d := by
  match a with
  | [] =>
    rw [to_vertical_edge_no_epsilon_nil, List.nil_append] at h
    have h_rw := SemiThueData.toSemiThue_reversing h
    have := eq_of_SemiThue_reversing_true h_rw is_true_to_horizontal_edge_no_epsilon
    match d with
    | [] =>
      simp only [to_vertical_edge_no_epsilon_nil, List.append_nil] at this
      rw [to_horizontal_edge_no_epsilon_injective this]
      exact Grid.top_bottom_word c
    | d1 :: d2 =>
      simp only [to_vertical_edge_no_epsilon_cons] at this
      have ht : SignedList.is_true (to_horizontal_edge_no_epsilon b) := is_true_to_horizontal_edge_no_epsilon
      rw [this] at ht
      specialize ht (d1, false) (by simp)
      simp at ht
  | a1 :: a2 =>
  match b with
  | [] =>
    rw [to_horizontal_edge_no_epsilon_nil, List.append_nil] at h
    have h_rw := SemiThueData.toSemiThue_reversing h
    have := eq_of_SemiThue_reversing_false h_rw is_false_to_vertical_edge_no_epsilon
    match c with
    | [] =>
      simp only [to_horizontal_edge_no_epsilon_nil, List.nil_append] at this
      rw [to_vertical_edge_no_epsilon_injective this]
      exact Grid.sides_word d
    | c1 :: c2 =>
      simp only [to_horizontal_edge_no_epsilon_cons, List.cons_append] at this
      have ht : SignedList.is_false (to_vertical_edge_no_epsilon (a1 :: a2)) := is_false_to_vertical_edge_no_epsilon
      rw [this] at ht
      specialize ht (c1, true) (by simp)
      simp at ht
  | b1 :: b2 =>
  have ⟨c1, d1, e1, pg, ⟨hl⟩, ⟨hs⟩, hi⟩:= PartialGrid.of_SemiThueData_reversing' h (by simp) (by simp)
  have h2 : SignedList.PosNegData (SignedOptionList.toSignedList (c1 ++ d1 ++ e1)) := by
    use to_horizontal_edge_no_epsilon c, to_vertical_edge_no_epsilon d
    exact ⟨⟨is_true_to_horizontal_edge_no_epsilon, ⟨is_false_to_vertical_edge_no_epsilon, hs.symm⟩⟩⟩
  have h3 := PosNegData_of_toSignedList_PosNeg_and_irreducible h2 hi
  have : SignedOptionList.toSignedList d1 = [] := by
    rcases PartialGrid.middle_frontier_spec pg with ⟨⟨rfl⟩⟩ | ⟨front, mid_d, caboose, ⟨d_eq⟩⟩
    · rfl
    have hf : c1 ++ d1 ++ e1 =
        c1 ++ [(front, false)] ++ (mid_d ++ [(caboose, true)] ++ e1) := by
      rw [d_eq]
      simp [List.append_assoc]
    exact (empty_middle_frontier_of_pos_neg_frontier h3 hf).elim
  have h1 := GridData.to_grid <| GridData.PartialGridStyle.of_PartialGrid_almost_empty_middle_frontier pg this
  rw [toList_to_vertical_edge_rev, toList_to_horizontal_edge] at h1
  have hs' : SignedOptionList.toSignedList c1 ++ SignedOptionList.toSignedList e1 =
      to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d := by
    rw [hs, SignedOptionList.toSignedList_append, SignedOptionList.toSignedList_append, this,
      List.append_nil]
  have ⟨hc, he⟩ := SignedList.parts_eq_of_true_false_eq
    (SignedOptionList.toSignedList_is_true pg.bottom_frontier_is_true)
    is_true_to_horizontal_edge_no_epsilon
    (SignedOptionList.toSignedList_is_false pg.right_frontier_is_false)
    is_false_to_vertical_edge_no_epsilon hs'
  have hc : c = SignedOptionList.toList c1 :=
    (toSignedList_eq_to_horizontal_edge_no_epsilon_iff pg.bottom_frontier_is_true).mp hc
  have hd : d = SignedOptionList.toList e1.reverse := by
    have := (toSignedList_eq_to_vertical_edge_no_epsilon_iff pg.right_frontier_is_false).mp he
    rw [this, SignedOptionList.toList_invRev, ← SignedOptionList.toList_reverse]
  rw [hc, hd]
  exact h1

theorem bm_equiv_of_reversing'
    (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b)
      (to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d)) :
    BraidMonoidInf.mk (a ++ c) = BraidMonoidInf.mk (b ++ d) :=
  Grid.braid_monoid_eq_of_grid (grid_of_rev h)
