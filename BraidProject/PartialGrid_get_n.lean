import BraidProject.PartialGrid_rw
import BraidProject.PartialGrid_add_empty

theorem two_frontiers_remove_ones_eq_means_move_ones_eq
  (h1 : PartialGrid a b c d e) (h2 : PartialGrid a b c1 d1 e1)
  (hr : remove_ones (c ++ d ++ e) = remove_ones (c1 ++ d1 ++ e1)) :
  move_ones (c ++ d ++ e) = move_ones (c1 ++ d1 ++ e1) := by sorry

theorem get_n'_same'''  (c0 c3 c₁ c₂) (hr : reversing c₁ c₂)
  (rev1 : SemiThue reversing (to_up_plain a ++ to_over_plain b) (c0 ++ c₁ ++ c3))
  (rev2 : SemiThue reversing (to_up_plain a ++ to_over_plain b) (c0 ++ c₂ ++ c3))
  (h1 : PartialGrid (to_up a) (to_over b) c5 d5 e5)
  (h6 : remove_ones (c5 ++ d5 ++ e5) = c0 ++ c₁ ++ c3)
  (h2 : PartialGrid (to_up a) (to_over b) c6 d6 e6)
  (h7 : remove_ones (c6 ++ d6 ++ e6) = c0 ++ c₂ ++ c3) :
  h1.length < h2.length := by
  rcases hr
  · rename_i n
    have H_ONE := pg_of_move_ones h1
    rcases H_ONE with ⟨cONE, dONE, eONE, pgh1m, ⟨trip_eq⟩, len_m⟩
    have silly : remove_ones (move_ones (c5 ++ d5 ++ e5)) = remove_ones (c5 ++ d5 ++ e5) := by
      rw [remove_ones_move_ones]
    rw [← silly] at h6
    have h11 : ∃ b1 b2 b3, move_ones (c5 ++ d5 ++ e5) = b1 ++ b2 ++ b3 ∧ remove_ones b1 = c0
      ∧ remove_ones b2 = [(n, false), (n, true)] ∧ remove_ones b3 = c3 :=
      triple_split h6
    rw [← remove_ones_move_ones] at h7
    have h12 : ∃ b1 b2 b3, move_ones (c6 ++ d6 ++ e6) = b1 ++ b2 ++ b3 ∧ remove_ones b1 = c0
      ∧ remove_ones b2 = [] ∧ remove_ones b3 = c3 :=
      triple_split h7
    rcases h11 with ⟨b₁, b₂, b₃, mob, h13, h14, h15⟩
    rcases h12 with ⟨b₄, b₅, b₆, mob1, h16, h17, h18⟩
    have h9 : pairsTogether (b₂) := by
      have H : pts (b₁ ++ b₂ ++ b₃) := by
        rw [← mob]
        refine pts_of_irr irreducible_move_ones
      exact H b₂ (by use b₁, b₃; exact ⟨rfl⟩)
    specialize h9 n n
    rw [h14] at h9
    specialize h9 (by use [], []; exact ⟨rfl⟩)
    rcases h9 with ⟨first, last, ⟨spec⟩⟩
    rw [len_m.1]
    have i_sandwich : cONE ++ dONE ++ eONE = (b₁ ++ first) ++ [(some n, false), (some n, true)] ++ (last ++ b₃) := by
      rw [← trip_eq, mob, ← spec]
      simp
    have big_step := add_cell_w_len pgh1m (grid_style_real.basic n) i_sandwich
    rcases big_step with ⟨nb, nm, nu, npg, ⟨fe⟩, _, _, ⟨len_n⟩⟩

    have : npg.length = h2.length := by
      have H_TWO := pg_of_move_ones h2
      rcases H_TWO with ⟨cTWO, dTWO, eTWO, pgh2m, ⟨trip_eq2⟩, len_m2⟩
      rw [len_m2.1]
      have H_THREE := pg_of_move_ones npg
      rcases H_THREE with ⟨cTHREE, dTHREE, eTHREE, pgh3m, ⟨trip_eq3⟩, len_m3⟩
      rw [len_m3.1]
      have H : move_ones (c6 ++ d6 ++ e6) = move_ones (nb ++ nm ++ nu) := by
        apply two_frontiers_remove_ones_eq_means_move_ones_eq h2 npg
        rw [← remove_ones_move_ones, h7, fe]
        simp [← spec, remove_ones] at h14
        simp [remove_ones, h13, h15]
        sorry
      rw [trip_eq3, trip_eq2] at H
      have H0 : cTWO = cTHREE ∧ dTWO = dTHREE ∧ eTWO = eTHREE := by sorry -- doable by fats about (middle) frontiers
      apply same_type_same_length_pg _ _ rfl rfl H0.1.symm H0.2.1.symm H0.2.2.symm
    rw [← this]
    exact len_n
  · rename_i n m h_nm
    rcases stepOne_mid rev1 skeleton_up_plain_over_plain with ⟨b', gs, unneeded, ⟨rm⟩⟩
    have h4 : SemiThue grid_style b' (move_ones b') :=
      equiv_move_ones
    have h5 : remove_ones (move_ones b') = remove_ones b' :=
      remove_ones_move_ones
    rw [rm] at h5
    rcases triple_split h5 with ⟨b₁, b₂, b₃, mob, h13, h14, h15⟩
    rw [mob] at h5
    have h9 : pairsTogether (b₂) := by
      have H : pts (b₁ ++ b₂ ++ b₃) := by
        rw [← mob]
        refine pts_of_irr irreducible_move_ones
      exact H b₂ (by use b₁, b₃; exact ⟨rfl⟩)
    specialize h9 n m
    rw [h14] at h9
    specialize h9 (by use [], []; exact ⟨rfl⟩)
    rcases h9 with ⟨first, last, ⟨spec⟩⟩
    have another_step : SemiThue grid_style
      (to_option (to_up_plain a ++ to_over_plain b)) (move_ones b') :=
      SemiThue.trans (to_option (to_up_plain a ++ to_over_plain b)) b' (move_ones b') gs h4
    have silly : to_option (to_up_plain a ++ to_over_plain b) =
      to_option (to_up_plain a) ++ to_option (to_over_plain b) := by
      unfold to_option
      simp
    rw [silly, mob] at another_step
    match a with
    | [] =>
      have H := pg_top_bottom_frontier h1 (by simp [remove_ones])
      have H1 : is_true (remove_ones (to_over b)) := is_true_remove_ones is_true_over
      have H2 : remove_ones (to_over b) = remove_ones (c5 ++ d5 ++ e5) := by
        rw [remove_ones_append, H.2, List.append_nil, H.1]
      rw [H2, h6] at H1
      specialize H1 (n, false) ⟨by simp⟩
      simp at H1
      exact H1.1.elim
    | a1 :: a2 =>
    match b with
    | [] =>
      have H := pg_side_frontier h1 (by simp [remove_ones])
      have H1 : is_false (remove_ones (to_up (a1 :: a2))) := is_false_remove_ones is_false_up
      have H2 : remove_ones (to_up (a1 :: a2)) = remove_ones (c5 ++ d5 ++ e5) := by
        rw [List.append_assoc, remove_ones_append, H.1, H.2, List.nil_append]
      rw [H2, h6] at H1
      specialize H1 (m, true) ⟨by simp⟩
      simp at H1
      exact H1.1.elim
    | b1 :: b2 =>
    have H := step_two (is_false_to_option to_up_plain_false) (by simp [to_option, to_up_plain])
      (is_true_to_option to_over_plain_true) (by simp [to_option, to_over_plain]) another_step
    rcases H with ⟨bot, mid, up, pg, ⟨frontier_spec⟩⟩
    have H2 := @add_cell_w_len _ _ _ _ _ _ _ (b₁ ++ first) (last ++ b₃) pg
        (grid_style_real.apart h_nm) (by rw [frontier_spec, ← spec]; simp)
    rcases H2 with ⟨nb, nm, nu, h1', ⟨fe⟩, up_spec, bot_spec, len⟩
    have first_len : pg.length = h1.length := by
      apply same_type_same_length_pg_rm
      · exact to_option_up_plain_eq_up (by simp)
      · exact to_option_over_plain_eq_over (by simp)
      aesop
    have second_len : h1'.length = h2.length := by
      apply same_type_same_length_pg_rm
      · exact to_option_up_plain_eq_up (by simp)
      · exact to_option_over_plain_eq_over (by simp)
      rw [fe, h7]
      have H : remove_ones first = [] ∧ remove_ones last = [] := by
        apply congr_arg remove_ones at spec
        rw [h14] at spec
        simp [remove_ones] at spec
        apply congr_arg List.length at spec
        simp at spec
        have H : (remove_ones first).length = 0 := by omega
        have H1 : (remove_ones last).length = 0 := by omega
        exact ⟨List.eq_nil_iff_length_eq_zero.mpr H, List.eq_nil_iff_length_eq_zero.mpr H1⟩
      simp_all [remove_ones]
    rw [← first_len, ← second_len]
    exact len.1
  rename_i n m h_nm
  rcases stepOne_mid rev1 skeleton_up_plain_over_plain with ⟨b', gs, unneeded, ⟨rm⟩⟩
  have h4 : SemiThue grid_style b' (move_ones b') :=
    equiv_move_ones
  have h5 : remove_ones (move_ones b') = remove_ones b' :=
    remove_ones_move_ones
  rw [rm] at h5
  rcases triple_split h5 with ⟨b₁, b₂, b₃, mob, h13, h14, h15⟩
  rw [mob] at h5
  have h9 : pairsTogether (b₂) := by
    have H : pts (b₁ ++ b₂ ++ b₃) := by
      rw [← mob]
      refine pts_of_irr irreducible_move_ones
    exact H b₂ (by use b₁, b₃; exact ⟨rfl⟩)
  specialize h9 n m
  rw [h14] at h9
  specialize h9 (by use [], []; exact ⟨rfl⟩)
  rcases h9 with ⟨first, last, ⟨spec⟩⟩
  have another_step : SemiThue grid_style
    (to_option (to_up_plain a ++ to_over_plain b)) (move_ones b') :=
    SemiThue.trans (to_option (to_up_plain a ++ to_over_plain b)) b' (move_ones b') gs h4
  have silly : to_option (to_up_plain a ++ to_over_plain b) =
    to_option (to_up_plain a) ++ to_option (to_over_plain b) := by
    unfold to_option
    simp
  rw [silly, mob] at another_step
  match a with
  | [] =>
    have H := pg_top_bottom_frontier h1 (by simp [remove_ones])
    have H1 : is_true (remove_ones (to_over b)) := is_true_remove_ones is_true_over
    have H2 : remove_ones (to_over b) = remove_ones (c5 ++ d5 ++ e5) := by
      rw [remove_ones_append, H.2, List.append_nil, H.1]
    rw [H2, h6] at H1
    specialize H1 (n, false) ⟨by simp⟩
    simp at H1
    exact H1.1.elim
  | a1 :: a2 =>
  match b with
  | [] =>
    have H := pg_side_frontier h1 (by simp [remove_ones])
    have H1 : is_false (remove_ones (to_up (a1 :: a2))) := is_false_remove_ones is_false_up
    have H2 : remove_ones (to_up (a1 :: a2)) = remove_ones (c5 ++ d5 ++ e5) := by
      rw [List.append_assoc, remove_ones_append, H.1, H.2, List.nil_append]
    rw [H2, h6] at H1
    specialize H1 (m, true) ⟨by simp⟩
    simp at H1
    exact H1.1.elim
  | b1 :: b2 =>
  have H := step_two (is_false_to_option to_up_plain_false) (by simp [to_option, to_up_plain])
    (is_true_to_option to_over_plain_true) (by simp [to_option, to_over_plain]) another_step
  rcases H with ⟨bot, mid, up, pg, ⟨frontier_spec⟩⟩
  have H2 := @add_cell_w_len _ _ _ _ _ _ _ (b₁ ++ first) (last ++ b₃) pg
      (grid_style_real.close h_nm) (by rw [frontier_spec, ← spec]; simp)
  rcases H2 with ⟨nb, nm, nu, h1', ⟨fe⟩, up_spec, bot_spec, len⟩
  have first_len : pg.length = h1.length := by
    apply same_type_same_length_pg_rm
    exact to_option_up_plain_eq_up (by simp)
    exact to_option_over_plain_eq_over (by simp)
    aesop
  have second_len : h1'.length = h2.length := by
    apply same_type_same_length_pg_rm
    exact to_option_up_plain_eq_up (by simp)
    exact to_option_over_plain_eq_over (by simp)
    rw [fe, h7]
    have H : remove_ones first = [] ∧ remove_ones last = [] := by
      apply congr_arg remove_ones at spec
      rw [h14] at spec
      simp [remove_ones] at spec
      apply congr_arg List.length at spec
      simp at spec
      have H : (remove_ones first).length = 0 := by omega
      have H1 : (remove_ones last).length = 0 := by omega
      exact ⟨List.eq_nil_iff_length_eq_zero.mpr H, List.eq_nil_iff_length_eq_zero.mpr H1⟩
    simp_all [remove_ones]
  rw [← first_len, ← second_len]
  exact len.1
