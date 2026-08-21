import BraidProject.Solver.MonoidCorrectness
import BraidProject.PartialGrid.NestedFrame
import BraidProject.PartialGrid.FrontierToSink

namespace Braid

noncomputable def grid_to_rev (h : GridData a b c d) : SemiThue reversing_prop
  (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) (to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d) := by
  induction h with
  | empty => exact SemiThue.refl
  | top_bottom i => exact SemiThue.refl
  | sides i => exact SemiThue.refl
  | top_left i => exact SemiThue.of_rel (reversing_prop.basic)
  | adjacent i k h => exact SemiThue.of_rel (reversing_prop.close h)
  | separated i j h => exact SemiThue.of_rel (reversing_prop.apart h)
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [to_vertical_edge_no_epsilon_mul, to_vertical_edge_no_epsilon_mul, List.append_assoc]
    apply (SemiThue.append_left h1_ih).trans
    rw [← List.append_assoc, ← List.append_assoc]
    exact SemiThue.append_right h2_ih
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [to_horizontal_edge_no_epsilon_mul, to_horizontal_edge_no_epsilon_mul, ← List.append_assoc]
    apply (SemiThue.append_right h1_ih).trans
    rw [List.append_assoc, List.append_assoc]
    exact SemiThue.append_left h2_ih

theorem eq_of_SemiThue_false (h : SemiThue reversing_prop a b) (ha : SignedList.is_false a) : a = b := by
  induction h with
  | refl => rfl
  | step _ _ h =>
    rcases h
    · rename_i j
      specialize ha (j, true) (by simp)
      simp at ha
    · rename_i i j hij
      specialize ha (j, true) (by simp)
      simp at ha
    rename_i i j hij
    specialize ha (j, true) (by simp)
    simp at ha
  | trans _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

theorem eq_of_SemiThue_true (h : SemiThue reversing_prop a b) (ha : SignedList.is_true a) : a = b := by
  induction h with
  | refl => rfl
  | step _ _  h =>
    rcases h
    · rename_i i
      specialize ha (i, false) (by simp)
      simp at ha
    · rename_i i j hij
      specialize ha (i, false) (by simp)
      simp at ha
    rename_i i j hij
    specialize ha (i, false) (by simp)
    simp at ha
  | trans _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

noncomputable def step_three (h : SemiThue reversing_prop (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) cde) :
  Σ c1 d1 e1, PartialGrid (to_vertical_edge a) (to_horizontal_edge b) c1 d1 e1 × PLift (SignedOptionList.toSignedList (c1 ++ d1 ++ e1) = cde) := by
  match a with
  | [] =>
    have hb1 : to_horizontal_edge_no_epsilon b = cde := by
      simp [to_vertical_edge_no_epsilon] at h
      apply eq_of_SemiThue_true h
      exact is_true_to_horizontal_edge_no_epsilon
    use [], (none, false):: to_horizontal_edge b, []
    constructor
    · simp [to_vertical_edge]
      apply PartialGrid.empty
      . simp
      · intro a ha
        simp at ha
        rw [ha]
      · exact to_horizontal_edge_length_pos
      exact is_true_to_horizontal_edge
    constructor
    rw [← hb1]
    simp
    sorry
  | a1 :: a2 =>
  match b with
  | [] =>
    have ha1 : to_vertical_edge_no_epsilon (a1 :: a2) = cde := by
      simp [to_horizontal_edge_no_epsilon] at h
      apply eq_of_SemiThue_false h
      exact is_false_to_vertical_edge_no_epsilon
    use [], to_vertical_edge (a1 :: a2) ++ [(none, true)], []
    constructor
    · apply PartialGrid.empty
      . exact to_vertical_edge_length_pos
      · exact is_false_to_vertical_edge
      · exact to_horizontal_edge_length_pos
      exact is_true_to_horizontal_edge
    constructor
    simp [← ha1]
    
    sorry
    --simp_all [SignedOptionList.toSignedList, ← ha1]
    --exact remove_up_is_no_epsilon
  | b1 :: b2 =>
    sorry
  -- have H1 := stepOne_mid h NegPosData.of_to_vertical_edge_no_epsilon_to_horizontal_edge_no_epsilon
  -- rcases H1 with ⟨b', st, so, ⟨rm⟩⟩
  -- rw [SignedList.to_SignedOptionList_append] at st
  -- have H2 := step_two (SignedList.is_false_to_SignedOptionList is_false_to_vertical_edge_no_epsilon) (by simp [SignedList.to_SignedOptionList, to_vertical_edge_no_epsilon])
  --   (SignedList.is_true_to_SignedOptionList is_true_to_horizontal_edge_no_epsilon) (by simp [SignedList.to_SignedOptionList_length, to_horizontal_edge_no_epsilon]) st
  -- rw [← rm]
  -- --rw [← (SignedList.to_SignedOptionList_up_no_epsilon_eq_up (by simp)), ← SignedList.to_SignedOptionList_over_no_epsilon_eq_over (by simp)]
  -- rcases H2 with ⟨bot, mid, up, pg, ⟨b'_is⟩⟩
  -- use bot, mid, up
  -- use pg
  -- constructor
  -- rw [b'_is]

--this should also go earlier

noncomputable def restricted_confluence (h1 : SemiThue reversing_prop (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
  (h2 : SemiThue reversing_prop (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) d) : Σ e, SemiThueData reversing c e × SemiThueData reversing d e := by
  have H1 := step_three h1
  have H2 := step_three h2
  rcases H1 with ⟨c1, d1, e1, pg, ⟨rm1⟩⟩
  rcases H2 with ⟨c2, d2, e2, pg2, ⟨rm2⟩⟩
  have H2 : Σ c3 d3, GridData a b c3 d3 := GridData.existence a b
  rcases H2 with ⟨c3, d3, gt⟩
  use (to_horizontal_edge_no_epsilon c3 ++ to_vertical_edge_no_epsilon d3)
  rw [← rm1, ← rm2]
  sorry
  -- constructor
  -- · exact pg_mid_frontier_reverses_to_grid pg rfl rfl gt
  -- exact pg_mid_frontier_reverses_to_grid pg2 rfl rfl gt

-- should go in semi thue rev?
theorem eq_of_SemiThue_SignedList.PosNegData (h : SemiThue reversing_prop a b) (ha : SignedList.PosNegData a) : a = b := by
  induction h with
  | refl => rfl
  | step _ _ h =>
    rcases ha with ⟨one, two, one_true, two_false, spec⟩
    rcases h
    · rename_i c d j
      have spec_rw : c ++ [(j, false), (j, true)] ++ d =
        (c ++ [(j, false)]) ++ ((j, true):: d) := by simp
      rw [spec_rw] at spec
      rcases List.append_eq_append_iff.mp spec with
        ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
      · rw [spec1] at one_true
        specialize one_true (j, false) (by simp)
        simp at one_true
      rw [spec2] at two_false
      specialize two_false (j, true) (by simp)
      simp at two_false
    · rename_i c d i j hij
      have spec_rw : c ++ [(i, false), (j, true)] ++ d =
        (c ++ [(i, false)]) ++ ((j, true):: d) := by simp
      rw [spec_rw] at spec
      rcases List.append_eq_append_iff.mp spec with
        ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
      · rw [spec1] at one_true
        specialize one_true (i, false) (by simp)
        simp at one_true
      rw [spec2] at two_false
      specialize two_false (j, true) (by simp)
      simp at two_false
    rename_i c d i j hij
    have spec_rw : c ++ [(i, false), (j, true)] ++ d =
      (c ++ [(i, false)]) ++ ((j, true):: d) := by simp
    rw [spec_rw] at spec
    rcases List.append_eq_append_iff.mp spec with
      ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
    · rw [spec1] at one_true
      specialize one_true (i, false) (by simp)
      simp at one_true
    rw [spec2] at two_false
    specialize two_false (j, true) (by simp)
    simp at two_false
  | trans _ _ ih1 ih2 =>
    specialize ih1 ha
    rw [ih1] at ha
    specialize ih2 ha
    aesop

theorem correct_other_dir (h : BraidMonoidInf.mk a =
    BraidMonoidInf.mk b) : final_solver a b := by
  have H : grid (a*1) (b*1) 1 1 := by
    apply Grid.of_mk_eq_mk
    rw [mul_one, mul_one]
    exact h
  rw [mul_one, mul_one] at H
  have Ht : GridData a b 1 1 := by
    exact (GridData.of_grid H).some
  have hr := grid_to_rev Ht
  change SemiThue reversing_prop _ [] at hr
  have hpg := step_three (grid_to_rev Ht)
  match a with
  | [] =>
    match b with
    | [] =>
      simp [final_solver]
    | b1 :: b2 =>
      simp [final_solver]
      have H := eq_of_SemiThue_true hr is_true_to_horizontal_edge_no_epsilon
      simp [to_horizontal_edge_no_epsilon] at H
  | a1 :: a2 =>
    match b with
    | [] =>
      simp [final_solver]
      simp [to_horizontal_edge_no_epsilon] at hr
      have H := eq_of_SemiThue_false hr is_false_to_vertical_edge_no_epsilon
      simp [to_vertical_edge_no_epsilon] at H
    | b1 :: b2 =>
      simp [final_solver]
      have H := @solver_equiv (a1 :: a2) (b1 :: b2) (by simp) (by simp)
      sorry
      -- rcases restricted_confluence hr H with ⟨e, h1, h2⟩
      -- have He : e = [] := (eq_of_SemiThue_true h1 SignedList.is_true_nil).symm
      -- rw [← He]
      -- apply eq_of_SemiThue_SignedList.PosNegData h2
      -- apply solver_helper_SignedList.PosNegData
