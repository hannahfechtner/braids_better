import BraidProject.PartialGrid.AddCell
import BraidProject.Solver.StepOne_length

namespace Braid

namespace PartialGrid

-- again, we continue to use PLift as it is more visible in the infoview
noncomputable def step_two_with_length (ha : SignedList.is_false a) (ha1 : a.length > 0)
    (hb : SignedList.is_true b) (hb1 : b.length > 0) :
    (h : SemiThueData grid_style (a ++ b) c) → (Σ bot mid up, Σ (p : PartialGrid a b bot mid up), PLift (bot ++ mid ++ up = c) ×
    PLift (SemiThueData.grid_style.length h = p.length)) := by
  intro h
  generalize hab : a ++ b = ab at h
  have ⟨new_deriv, new_deriv_length⟩:= SemiThueData.grid_style.toSemiThueDataDerivation_with_length h
  rw [new_deriv_length]
  clear new_deriv_length
  induction new_deriv with
  | refl =>
    use [], a ++ b, [], PartialGrid.empty _ _ ha1 ha hb1 hb
    constructor
    · constructor
      rw [List.append_nil, List.nil_append, hab]
    constructor
    simp [PartialGrid.length]
  | step h1 h2 ih =>
    rcases ih hab (SemiThueDataDerivation.toSemiThueData h1) with ⟨bot, mid, up, h3, ⟨h4⟩⟩
    rcases add_cell_with_length h3 h2 h4.1 with ⟨b, m, u, h3, h4⟩
    use b, m, u, h3
    rw [← h4.2.2.2.1, SemiThueDataDerivation.grid_style.length_step h1 h2]
    constructor
    · exact h4.1
    aesop

noncomputable def of_SemiThueData_reversing
    (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
    (ha : a.length > 0) (hb : b.length > 0) :
    Σ c1 d1 e1, Σ h1 : PartialGrid (to_vertical_edge a) (to_horizontal_edge b) c1 d1 e1,
    PLift (SemiThueData.reversing.length h = h1.length) × PLift (c = SignedOptionList.toSignedList (c1 ++ d1 ++ e1)):= by
  have H := SemiThueData.reversing.to_grid_style_w_length_horizontal_vertical_edge h ha hb
  rcases H with ⟨c2, h3, h4⟩
  rw [h4.1.1]
  have H := step_two_with_length (is_false_to_vertical_edge) (to_vertical_edge_length_pos)
    is_true_to_horizontal_edge to_horizontal_edge_length_pos h3
  rcases H with ⟨d, e, f, h1, h2⟩
  use d, e, f, h1
  constructor
  · exact ⟨h2.2.1⟩
  exact ⟨by rw [h2.1.1, h4.2.1]⟩

-- noncomputable def step_three
--     (h : SemiThue reversing_prop (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) cde) :
--     Σ c1 d1 e1, PartialGrid (to_vertical_edge a) (to_horizontal_edge b) c1 d1 e1 ×
--     PLift (SignedOptionList.toSignedList (c1 ++ d1 ++ e1) = cde) := by
--   match a with
--   | [] =>
--     have hb1 : to_horizontal_edge_no_epsilon b = cde := by
--       simp [to_vertical_edge_no_epsilon] at h
--       apply eq_of_SemiThue_true h
--       exact is_true_to_horizontal_edge_no_epsilon
--     use [], (none, false):: to_horizontal_edge b, []
--     constructor
--     · simp [to_vertical_edge]
--       apply PartialGrid.empty
--       . simp
--       · intro a ha
--         simp at ha
--         rw [ha]
--       · exact to_horizontal_edge_length_pos
--       exact is_true_to_horizontal_edge
--     constructor
--     rw [← hb1]
--     simp [toSignedList_to_horizontal_edge]
--   | a1 :: a2 =>
--   match b with
--   | [] =>
--     have ha1 : to_vertical_edge_no_epsilon (a1 :: a2) = cde := by
--       simp only [to_horizontal_edge_no_epsilon, List.map_nil,
--         List.append_nil] at h
--       apply eq_of_SemiThue_false h
--       exact is_false_to_vertical_edge_no_epsilon
--     use [], to_vertical_edge (a1 :: a2) ++ [(none, true)], []
--     constructor
--     · apply PartialGrid.empty
--       . exact to_vertical_edge_length_pos
--       · exact is_false_to_vertical_edge
--       · exact to_horizontal_edge_length_pos
--       exact is_true_to_horizontal_edge
--     constructor
--     simp [← ha1, to_vertical_edge, SignedOptionList.toSignedList]
--     sorry
--     --simp_all [SignedOptionList.toSignedList, ← ha1]
--     --exact remove_up_is_no_epsilon
--   | b1 :: b2 =>
--     sorry
--   -- have H1 := stepOne_mid h NegPosData.of_to_vertical_edge_no_epsilon_to_horizontal_edge_no_epsilon
--   -- rcases H1 with ⟨b', st, so, ⟨rm⟩⟩
--   -- rw [SignedList.to_SignedOptionList_append] at st
--   -- have H2 := step_two (SignedList.is_false_to_SignedOptionList is_false_to_vertical_edge_no_epsilon) (by simp [SignedList.to_SignedOptionList, to_vertical_edge_no_epsilon])
--   --   (SignedList.is_true_to_SignedOptionList is_true_to_horizontal_edge_no_epsilon) (by simp [SignedList.to_SignedOptionList_length, to_horizontal_edge_no_epsilon]) st
--   -- rw [← rm]
--   -- --rw [← (SignedList.to_SignedOptionList_up_no_epsilon_eq_up (by simp)), ← SignedList.to_SignedOptionList_over_no_epsilon_eq_over (by simp)]
--   -- rcases H2 with ⟨bot, mid, up, pg, ⟨b'_is⟩⟩
--   -- use bot, mid, up
--   -- use pg
--   -- constructor
--   -- rw [b'_is]
