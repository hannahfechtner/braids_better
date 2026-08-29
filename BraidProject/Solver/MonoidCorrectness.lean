import BraidProject.Solver.Monoid

namespace Braid

theorem toList_to_SignedOptionList_to_vertical_edge_no_epsilon_reverse (a : List ℕ) :
    SignedOptionList.toList (SignedList.to_SignedOptionList (to_vertical_edge_no_epsilon a)).reverse = a := by
  induction a with
  | nil => simp [SignedList.to_SignedOptionList, to_vertical_edge_no_epsilon]
  | cons a1 a2 ih =>
    simp_all [SignedList.to_SignedOptionList, to_vertical_edge_no_epsilon]

theorem toList_to_SignedOptionList_to_horizontal_edge_no_epsilon (b : List ℕ) :
    SignedOptionList.toList (SignedList.to_SignedOptionList (to_horizontal_edge_no_epsilon b)) = b := by
  induction b with
  | nil => simp [SignedList.to_SignedOptionList, to_horizontal_edge_no_epsilon]
  | cons b1 b2 ih =>
    simp_all [SignedList.to_SignedOptionList, to_horizontal_edge_no_epsilon]

theorem recover_of_toSignedList_to_horizontal_edge_no_epsilon
    (h : to_horizontal_edge_no_epsilon c = SignedOptionList.toSignedList bot) :
    SignedOptionList.toList bot = c := by
  induction bot generalizing c with
  | nil => unfold to_horizontal_edge_no_epsilon at h; simp_all
  | cons head tail ih =>
    match head with
    | (none, bo) => simp [ih h]
    | (some hh, bo) =>
      simp only [SignedOptionList.toSignedList_cons_some] at h
      change _ = [(hh, bo)] ++ _ at h
      rcases to_horizontal_edge_no_epsilon_eq_append h with ⟨a₁, a₂, ha, ha₁, ha₂⟩
      simp only [SignedOptionList.toList_cons_some]
      rw [ih ha₂, ha]
      simp_all [to_horizontal_edge_no_epsilon]

theorem recover_of_toSignedList_to_vertical_edge_no_epsilon
    (h : SignedOptionList.toSignedList up = to_vertical_edge_no_epsilon d) :
    SignedOptionList.toList up.reverse = d := by
  induction up generalizing d with
  | nil => exact to_vertical_edge_no_epsilon_inj h
  | cons head tail ih =>
    rw [List.reverse_cons, SignedOptionList.toList_append]
    rw [SignedOptionList.toSignedList_cons] at h
    match head with
    | (none, bo) => simp [ih h]
    | (some hh, bo) =>
      simp only [SignedOptionList.toSignedList_cons_some, SignedOptionList.toSignedList_nil] at h
      rcases to_vertical_edge_no_epsilon_eq_append h.symm with ⟨a₁, a₂, ha, ha₁, ha₂⟩
      rw [ih ha₁.symm, ha, List.append_right_inj]
      unfold to_vertical_edge_no_epsilon at ha₂
      simp only [List.map_reverse, List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append,
        List.map_eq_singleton_iff, Prod.mk.injEq, Bool.false_eq, ↓existsAndEq, true_and] at ha₂
      simp [ha₂.1]

theorem helper_for_bottom
    (h : SignedOptionList.toSignedList b' = to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d)
    (h1 : bot ++ up = move_ones b') (hbot : SignedList.is_true bot) (hup : SignedList.is_false up) :
    (SignedOptionList.toList up.reverse) = d ∧ SignedOptionList.toList bot = c := by
  have one := congr_arg SignedOptionList.toList h1
  have two := congr_arg SignedOptionList.toSignedList h1
  simp [SignedOptionList.toList_append] at one
  simp [SignedOptionList.toSignedList_append, toSignedList_move_ones] at two
  rw [← two] at h
  rcases List.append_eq_append_iff.mp h with ⟨mid, spec1, spec2⟩ | ⟨mid, spec1, spec2⟩
  · match mid with
    | [] =>
      simp_all
      have H := recover_of_toSignedList_to_horizontal_edge_no_epsilon spec1
      have H2 := recover_of_toSignedList_to_vertical_edge_no_epsilon spec2
      simp [H, H2]
    | m1 :: m2 =>
      exfalso
      have H : SignedList.is_true (to_horizontal_edge_no_epsilon c) := is_true_to_horizontal_edge_no_epsilon
      rw [spec1] at H
      apply SignedList.is_true_of_append at H
      have H2 : SignedList.is_false (SignedOptionList.toSignedList up) :=
        SignedOptionList.toSignedList_is_false hup
      rw [spec2] at H2
      apply SignedList.is_false_of_append at H2
      have := SignedList.nil_of_is_true_and_is_false (SignedList.is_true_of_cons H.2).1 (SignedList.is_false_of_cons H2.1).1
      simp at this
  match mid with
  | [] =>
    simp_all
    have H := recover_of_toSignedList_to_horizontal_edge_no_epsilon spec1.symm
    have H2 := recover_of_toSignedList_to_vertical_edge_no_epsilon spec2.symm
    simp [H, H2]
  | m1 :: m2 =>
    exfalso
    have H : SignedList.is_true (SignedOptionList.toSignedList bot) :=
      SignedOptionList.toSignedList_is_true hbot
    rw [spec1] at H
    apply SignedList.is_true_of_append at H
    have H2 : SignedList.is_false (to_vertical_edge_no_epsilon d) := is_false_to_vertical_edge_no_epsilon
    rw [spec2] at H2
    apply SignedList.is_false_of_append at H2
    have := SignedList.nil_of_is_true_and_is_false (SignedList.is_true_of_cons H.2).1 (SignedList.is_false_of_cons H2.1).1
    simp at this

noncomputable def PosNegData_concatenate_reduction (h : SignedList.PosNegData b) (hr : SignedList.PosNegData (SignedOptionList.toSignedList (a :: b))) :
     SignedList.PosNegData (concatenate_reduction a b) := by
  induction hb : b.length generalizing a b with
  | zero =>
    rw [List.eq_nil_iff_length_eq_zero.mpr hb]
    simp [concatenate_reduction]; exact SignedList.PosNegData.singleton
  | succ n ih =>
    match b with
    | [] => simp at hb
    | (none, false) :: tail =>
      simp [concatenate_reduction]
      rcases h with ⟨c, d, c_true, d_false, cd_is⟩
      have H : c = [] := by
        match c with
        | [] => rfl
        | c1 :: c2 =>
          simp at cd_is
          rw [← cd_is.1] at c_true
          specialize c_true (none, false) (by simp)
          simp at c_true
      rw [H, List.nil_append] at cd_is
      match a with
      | (a1, false) =>
        use [], (a1, false) :: d
        constructor
        constructor
        · exact SignedList.is_true_nil
        constructor
        · exact SignedList.is_false_cons d d_false
        rw [cd_is, List.nil_append]
      | (a1, true) =>
        use [(a1, true)], d
        constructor
        constructor
        · exact SignedList.is_true_cons [] SignedList.is_true_nil
        constructor
        · exact d_false
        rw [cd_is]
        rfl
    | (some a1, false) :: tail =>
      simp [concatenate_reduction]
      rcases h with ⟨c, d, c_true, d_false, cd_is⟩
      have H : c = [] := by
        match c with
        | [] => rfl
        | c1 :: c2 =>
          simp at cd_is
          rw [← cd_is.1] at c_true
          specialize c_true (some a1, false) (by simp)
          simp at c_true
      rw [H, List.nil_append] at cd_is
      match a with
      | (a1, false) =>
        use [], (a1, false) :: d
        constructor
        constructor
        · exact SignedList.is_true_nil
        constructor
        · exact SignedList.is_false_cons d d_false
        rw [cd_is, List.nil_append]
      | (a1, true) =>
        use [(a1, true)], d
        constructor
        constructor
        · exact SignedList.is_true_cons [] SignedList.is_true_nil
        constructor
        · exact d_false
        rw [cd_is]
        rfl
    | (none, true) :: tail =>
      match a with
      | (a1, true) =>
        simp [concatenate_reduction]
        rcases h with ⟨c, d, c_true, d_false, cd_is⟩
        use (a1, true) :: c, d
        constructor
        constructor
        · exact SignedList.is_true_cons c c_true
        constructor
        · exact d_false
        rw [cd_is]
        rfl
      | (a1, false) =>
        simp [concatenate_reduction]
        simp at hb
        rw [SignedOptionList.toSignedList_cons, SignedOptionList.toSignedList, ← SignedOptionList.toSignedList_append] at hr
        specialize @ih tail (a1, false) (SignedList.PosNegData.tail h) hr hb
        rcases ih with ⟨c, d, c_true, d_false, cd_is⟩
        use (none, true) :: c, d
        constructor
        constructor
        · exact SignedList.is_true_cons c c_true
        constructor
        · exact d_false
        rw [cd_is]
        rfl
    | (some a1, true) :: tail =>
      match a with
      | (none, true) =>
        simp [concatenate_reduction]
        rcases h with ⟨c, d, c_true, d_false, hcd⟩
        use (none, true) :: c, d
        constructor
        constructor
        · exact SignedList.is_true_cons c c_true
        constructor
        · exact d_false
        rw [hcd]
        rfl
      | (some a2, true) =>
        simp [concatenate_reduction]
        rcases h with ⟨c, d, c_true, d_false, cd_is⟩
        use (a2, true) :: c, d
        constructor
        constructor
        · exact SignedList.is_true_cons c c_true
        constructor
        · exact d_false
        rw [cd_is]
        rfl
      | (none, false) =>
        simp [concatenate_reduction]
        simp at hb
        rw [SignedOptionList.toSignedList_cons, SignedOptionList.toSignedList, SignedOptionList.toSignedList, SignedOptionList.toSignedList_nil, List.nil_append] at hr
        specialize @ih tail (none, false) (SignedList.PosNegData.tail h)
          (by rw [SignedOptionList.toSignedList_cons, SignedOptionList.toSignedList, SignedOptionList.toSignedList_nil,
          List.nil_append]; exact SignedList.PosNegData.tail hr) hb
        rcases ih with ⟨c, d, c_true, d_false, hcd⟩
        use (some a1, true) :: c, d
        constructor
        constructor
        · exact SignedList.is_true_cons c c_true
        constructor
        · exact d_false
        rw [hcd]
        rfl
      | (some a2, false) =>
        simp [SignedOptionList.toSignedList] at hr
        rcases hr with ⟨c, d, c_true, d_false, hcd⟩
        have H : c = [] := by
          match c with
          | [] => rfl
          | c1 :: c2 =>
            simp at hcd
            rw [← hcd.1] at c_true
            specialize c_true (a2, false) (by simp)
            simp at c_true
        rw [H, List.nil_append] at hcd
        rw [← hcd] at d_false
        specialize d_false (a1, true) (by simp)
        simp at d_false

noncomputable def PosNegData_move_ones_of_PosNegData_toSignedList (h : SignedList.PosNegData (SignedOptionList.toSignedList b)) :
  SignedList.PosNegData (move_ones b) := by
  induction b with
  | nil => simp; exact SignedList.PosNegData.nil
  | cons head tail ih =>
    simp [move_ones]
    have H : SignedList.PosNegData (SignedOptionList.toSignedList tail) := by
      match head with
      | (none, b) =>
        simp [SignedOptionList.toSignedList] at h
        exact h
      | (some a, b) =>
        apply SignedList.PosNegData.tail
        simp [SignedOptionList.toSignedList] at h
        exact h
    specialize ih H
    apply PosNegData_concatenate_reduction ih
    rcases ih with ⟨c, d, c_true, d_false, hcd⟩
    match head with
    | (none, b) =>
      use SignedOptionList.toSignedList c, SignedOptionList.toSignedList d
      constructor
      constructor
      · exact SignedOptionList.toSignedList_is_true c_true
      constructor
      · exact SignedOptionList.toSignedList_is_false d_false
      simp [SignedOptionList.toSignedList, hcd]
    | (some a1, true) =>
      use (a1, true) :: SignedOptionList.toSignedList c, SignedOptionList.toSignedList d
      constructor
      constructor
      · apply SignedList.is_true_cons
        exact SignedOptionList.toSignedList_is_true c_true
      constructor
      · exact SignedOptionList.toSignedList_is_false d_false
      simp [SignedOptionList.toSignedList, hcd]
    | (some a1, false) =>
      simp [SignedOptionList.toSignedList, toSignedList_move_ones]
      simp [SignedOptionList.toSignedList] at h
      exact h

theorem bm_equiv_of_reversing (ha : List.length a > 0) (hb : List.length b > 0)
  (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) (to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d)) :
  BraidMonoidInf.mk (a ++ c) = BraidMonoidInf.mk (b ++ d) := by
  have H0 := stepOne h NegPosData.of_to_vertical_edge_no_epsilon_to_horizontal_edge_no_epsilon
    PosNegData.of_to_horizontal_edge_no_epsilon_to_vertical_edge_no_epsilon
  rcases H0 with ⟨b', st, so, io, ⟨rm⟩⟩
  have silly : SignedList.to_SignedOptionList (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) =
    SignedList.to_SignedOptionList (to_vertical_edge_no_epsilon a) ++ SignedList.to_SignedOptionList (to_horizontal_edge_no_epsilon b) := by
    unfold SignedList.to_SignedOptionList
    simp
  rw [silly] at st
  have H2 : SemiThueData grid_style b' (move_ones b') := equiv_move_ones
  have H3 := SemiThueData.trans st H2
  have H := step_two_with_length (SignedList.is_false_to_SignedOptionList is_false_to_vertical_edge_no_epsilon)
    (by simp [ha, SignedList.to_SignedOptionList, to_vertical_edge_no_epsilon]) (SignedList.is_true_to_SignedOptionList is_true_to_horizontal_edge_no_epsilon)
    (by simp [hb, SignedList.to_SignedOptionList, to_horizontal_edge_no_epsilon]) H3
  rcases H with ⟨bot, mid, up, pg, ⟨b'_is⟩⟩
  rcases PartialGrid.middle_frontier_spec pg with ⟨⟨mid_nil⟩⟩ | ⟨fm, mm, cm, ⟨problem⟩⟩
  · rw [mid_nil] at pg
    have grid1 := GridData.PartialGridStyle.of_PartialGrid pg
    unfold GridData.PartialGridStyle at grid1
    rw [mid_nil, List.append_nil] at b'_is
    have hbot := helper_for_bottom rm b'_is.1 pg.bottom_frontier_is_true
      pg.right_frontier_is_false
    rw [← hbot.1, ← hbot.2]
    --rw [recover_of_toSignedList_to_horizontal_edge_no_epsilon ?_]
    -- remove_SignedList.to_SignedOptionList_to_vertical_edge_no_epsilon, hbot.1, hbot.2] at grid1
    have H := Braid.GridData.braid_eq grid1
    convert H
    · rw [← toList_to_SignedOptionList_to_vertical_edge_no_epsilon_reverse a]
      congr
      exact (toList_to_SignedOptionList_to_vertical_edge_no_epsilon_reverse a).symm
    rw [← toList_to_SignedOptionList_to_horizontal_edge_no_epsilon b]
    congr
    exact (toList_to_SignedOptionList_to_horizontal_edge_no_epsilon b).symm
  rw [problem] at b'_is
  exfalso
  have H : SignedList.PosNegData (SignedOptionList.toSignedList b') := by
    rw [rm]
    exact PosNegData.of_to_horizontal_edge_no_epsilon_to_vertical_edge_no_epsilon
  have H1 : SignedList.PosNegData (move_ones b') := PosNegData_move_ones_of_PosNegData_toSignedList H
  rcases H1 with ⟨a1, a2, a1_true, a2_false, ha12⟩
  rw [ha12] at b'_is
  rw [← List.append_assoc, List.append_assoc (bot ++ ([(fm, false)] ++ mm))] at b'_is
  rcases List.append_eq_append_iff.mp b'_is.1 with
    ⟨middle, spec1, spec2⟩ | ⟨middle, spec1, spec2⟩
  · rw [spec1] at a1_true
    specialize a1_true (fm, false) (by simp)
    simp at a1_true
  rw [spec2] at a2_false
  specialize a2_false (cm, true) (by simp)
  simp at a2_false

theorem correct_one_dir (h : final_solver a b) : BraidMonoidInf.mk a =
  BraidMonoidInf.mk b := by
  match a with
  | [] =>
    match b with
    | [] => rfl
    | b1 :: b2 =>
      simp [final_solver] at h
  | a1 :: a2 =>
    match b with
    | [] => simp [final_solver] at h
    | b1 :: b2 =>
      simp [final_solver] at h
      rw [← List.append_nil (a1 :: a2), ← List.append_nil (b1 :: b2)]
      apply bm_equiv_of_reversing (by simp) (by simp)
      conv =>
        enter [3]
        rw [to_horizontal_edge_no_epsilon, to_vertical_edge_no_epsilon]
        simp
      have H := @solver_equiv (a1 :: a2) (b1 :: b2) (by simp) (by simp)
      rw [h] at H
      exact H


end Braid
