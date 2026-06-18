import BraidProject.PartialGrid.Basic
import BraidProject.Cancellability_C

open SignedOptionList

namespace Braid

namespace GridData

/- a version of grids which are read in the north-easterly direction, mirroring the conventions for partial grids -/
def PartialGridStyle (a b c d : List (Option ℕ × Bool)) : Type :=
  GridData (toList a.reverse) (toList b) (toList c) (toList d.reverse)

namespace PartialGridStyle
def append_horizontal
    (h1 : GridData.PartialGridStyle a b c d) (h2 : GridData.PartialGridStyle d e f g) :
    GridData.PartialGridStyle a (b ++ e) (c ++ f) g := by
  simp only [GridData.PartialGridStyle, toList_append]
  exact GridData.horizontal h1 h2

def append_vertical
    (h1 : GridData.PartialGridStyle a b c d) (h2 : GridData.PartialGridStyle e c f g) :
    GridData.PartialGridStyle (e ++ a) b f (g ++ d) := by
  simp only [GridData.PartialGridStyle, List.reverse_append, toList_append]
  exact GridData.vertical h1 h2

noncomputable def of_PartialGrid (h : PartialGrid a b c [] d) :
    GridData.PartialGridStyle a b c d := by
  generalize hm : ([] : List (Option ℕ × Bool)) = m at h
  induction h with
  | single_cell h =>
    unfold GridData.PartialGridStyle
    simp only [toList_to_vertical_edge_rev, toList_to_horizontal_edge]
    exact of_CellData h
  | empty a b =>
    apply congr_arg List.length at hm
    simp only [List.length_nil, List.length_append] at hm
    linarith
  | horizontal_append_one _ _ ih1 ih2 =>
    exact GridData.PartialGridStyle.append_horizontal (ih1 rfl) (ih2 hm)
  | horizontal_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at hm
    have H := GridData.PartialGridStyle.append_horizontal (g1_ih hm.1.symm) (g2_ih hm.2.2.symm)
    rw [hm.2.1, List.append_nil] at H
    exact H
  | vertical_append_one _ _ ih1 ih2 =>
    exact GridData.PartialGridStyle.append_vertical (ih1 rfl) (ih2 hm)
  | vertical_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at hm
    have H := GridData.PartialGridStyle.append_vertical (g1_ih hm.2.2.symm) (g2_ih hm.1.symm)
    rw [hm.2.1, List.nil_append] at H
    exact H

end PartialGridStyle
end GridData

namespace PartialGrid

theorem empty_middle_frontier_matches_grid
    (g1 : PartialGrid a2 b2 bot2 [] up2) (ha : a1 = toList (FreeGroup.invRev a2))
    (b4_is : b4 = toList b2) (b9 : GridData a1 b4 b7 b6) :
    b6 = toList (FreeGroup.invRev up2) ∧ b7 = toList bot2 := by
  have ha1 : a1 = toList a2.reverse := by
    simp only [toList_invRev, ← SignedOptionList.toList_reverse] at ha
    rw [ha]
  have H := GridData.PartialGridStyle.of_PartialGrid g1
  have H3 := GridData.unicity b9 H ha1 b4_is
  rw [← H3.1.1, ← H3.2.1]
  constructor
  · simp [SignedOptionList.toList_reverse]
  rfl

end PartialGrid
