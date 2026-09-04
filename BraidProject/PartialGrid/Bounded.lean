import BraidProject.PartialGrid.NestedFrame

namespace Braid

open SignedOptionList PartialGrid PartialGrid.FrontierPossibilitiesEpsilonRemovedBoolRemoved

theorem PartialGrid.length_le_GridData_length
    (h : PartialGrid a b c d e) (h1 : GridData a1 b1 g f) :
    toList (FreeGroup.invRev a) = a1 → toList b = b1 →
    h.length ≤ GridData.length h1 := by
  intro ha hb
  exact (frontier_prefix h1 h
    ((toSignedList_eq_to_vertical_edge_no_epsilon_iff (left_side_is_false h)).mpr ha.symm)
    ((toSignedList_eq_to_horizontal_edge_no_epsilon_iff (top_side_is_true h)).mpr hb.symm)).2.2

theorem straight_pg_sm_g (h : PartialGrid a b c d e) (h1 : GridData a1 b1 f g)
    : a = to_vertical_edge a1 → b = to_horizontal_edge b1 → h.length ≤ GridData.length h1 := by
  intro ha hb
  apply PartialGrid.length_le_GridData_length h h1
  · rw [ha, toList_invRev_to_vertical_edge]
  rw [hb, toList_to_horizontal_edge]
