import BraidProject.PartialGrid.Build
import BraidProject.PartialGrid.ToGrid

namespace Braid

theorem big_one (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) (to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d))
    : grid a b c d := by
  have H := of_SemiThueData_reversing h2 ha hb
  rcases H with ⟨c1, d1, e1, h4, h5⟩
  use c1, d1, e1, h4
  exact ⟨by rw [h5.2.1]⟩
