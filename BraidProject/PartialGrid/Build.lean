import BraidProject.PartialGrid.AddCell
import BraidProject.ReversingToGridStyle

namespace Braid
namespace PartialGrid

open Relations

-- again, we continue to use PLift as it is more visible in the infoview
noncomputable def of_SemiThueData_grid_style (ha : SignedList.is_false a) (ha1 : a.length > 0)
    (hb : SignedList.is_true b) (hb1 : b.length > 0) :
    (h : SemiThueData grid_style (a ++ b) c) → (Σ bot mid up, Σ (p : PartialGrid a b bot mid up), PLift (bot ++ mid ++ up = c) ×
    PLift (SemiThueData.length grid_style.length h = p.length)) := by
  intro h
  generalize hab : a ++ b = ab at h
  rw [← SemiThueData.toSemiThueDataDerivation_length]
  induction SemiThueData.toSemiThueDataDerivation h with
  | refl =>
    use [], a ++ b, [], PartialGrid.empty _ _ ha1 ha hb1 hb
    exact ⟨⟨by rw [List.append_nil, List.nil_append, hab]⟩, ⟨by simp [PartialGrid.length]⟩⟩
  | step h1 h2 ih =>
    rcases ih hab (SemiThueDataDerivation.toSemiThueData h1) with ⟨bot, mid, up, h3, ⟨h4⟩⟩
    rcases add_cell_with_length h3 h2 h4.1 with ⟨b, m, u, h3, h4⟩
    use b, m, u, h3
    rw [← h4.2.2.2.1, SemiThueDataDerivation.length_step h1 h2]
    exact ⟨h4.1, by aesop⟩

noncomputable def of_SemiThueData_reversing
    (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
    (ha : a.length > 0) (hb : b.length > 0) :
    Σ c1 d1 e1, Σ h1 : PartialGrid (to_vertical_edge a) (to_horizontal_edge b) c1 d1 e1,
    PLift (SemiThueData.length (fun _ => 1) h = h1.length) ×
    PLift (c = SignedOptionList.toSignedList (c1 ++ d1 ++ e1)) := by
  have ⟨c2, h3, h4⟩ := SemiThueData.reversing.to_grid_style_w_length_horizontal_vertical_edge h ha hb
  rw [h4.1.1]
  have ⟨d, e, f, h1, h2⟩ := of_SemiThueData_grid_style is_false_to_vertical_edge to_vertical_edge_length_pos
    is_true_to_horizontal_edge to_horizontal_edge_length_pos h3
  use d, e, f, h1
  exact ⟨⟨h2.2.1⟩, ⟨by rw [h2.1.1, h4.2.1.1]⟩⟩

noncomputable def of_SemiThueData_reversing'
    (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
    (ha : a.length > 0) (hb : b.length > 0) :
    Σ c1 d1 e1, Σ h1 : PartialGrid (to_vertical_edge a) (to_horizontal_edge b) c1 d1 e1,
    PLift (SemiThueData.length (fun _ => 1) h = h1.length) ×
    PLift (c = SignedOptionList.toSignedList (c1 ++ d1 ++ e1)) × irreducible (c1 ++ d1 ++ e1) := by
  have ⟨c2, h3, h4, h5⟩ := SemiThueData.reversing.to_grid_style_w_length_horizontal_vertical_edge h ha hb
  rw [h4.1]
  have ⟨d, e, f, h1, h2⟩ := of_SemiThueData_grid_style is_false_to_vertical_edge to_vertical_edge_length_pos
    is_true_to_horizontal_edge to_horizontal_edge_length_pos h3
  use d, e, f, h1
  rw [h2.1.1, h5.1.1]
  refine ⟨⟨h2.2.1⟩, ⟨rfl⟩, h5.2⟩

end PartialGrid
end Braid
