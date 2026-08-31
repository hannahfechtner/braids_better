import BraidProject.StepOne
import BraidProject.SemiThue_length_general

namespace Braid

noncomputable def equiv_insert_w_len : {h1 : SemiThueData grid_style (a :: L) (concatenate_reduction a L) // SemiThueData.grid_style.length h1 = 0} := by
  have H : ∀ t L a, L.length ≤ t → {h1 : SemiThueData grid_style (a :: L) (concatenate_reduction a L) // SemiThueData.grid_style.length h1 = 0} := by
    intro t
    induction t
    · intro L a len
      simp at len
      rw [len]
      use SemiThueData.refl
      rfl
    rename_i n ih
    intro L a len
    match a with
    | (none, true) =>
      have H : (concatenate_reduction (none, true) L) = (none, true) :: L := by simp
      rw [H]
      use SemiThueData.refl
      rfl
    | (none, false) =>
      match L with
      | [] => use SemiThueData.refl; rfl
      | (none, true) :: tail =>
        simp at len
        use SemiThueData.trans (SemiThueData.grid_style.append_right_w_length _ (@SemiThueData.step _ _ _ _ [] [] grid_style.empty)).1 (SemiThueData.cons (ih tail _ len).1)
        simp only [SemiThueData.grid_style.length_trans, Nat.add_eq_zero_iff]
        exact ⟨(SemiThueData.grid_style.append_right_w_length _ _).2,
          SemiThueData.grid_style.cons.trans (ih tail _ len).2⟩
      | (none, false) :: tail =>
        use SemiThueData.refl
        rfl
      | (some c, true) :: tail1 =>
        simp at len
        specialize ih tail1 (none, false) len
        use SemiThueData.trans (SemiThueData.grid_style.append_right_w_length _ (@SemiThueData.step _ _ _ _ [] [] (grid_style.up c))).1 (SemiThueData.cons ih.1)
        simp only [SemiThueData.grid_style.length_trans, Nat.add_eq_zero_iff]
        exact ⟨(SemiThueData.grid_style.append_right_w_length _ _).2,
          SemiThueData.grid_style.cons.trans ih.2⟩
      | (some c, false) :: tail1 =>
        use SemiThueData.refl
        rfl
    | (some b, true) =>
      match L with
      | [] => use SemiThueData.refl; rfl
      | (none, true) :: tail => use SemiThueData.refl ; rfl
      | (none, false) :: tail => use SemiThueData.refl ; rfl
      | (some c, true) :: tail1 => use SemiThueData.refl ; rfl
      | (some c, false) :: tail1 => use SemiThueData.refl ; rfl
    | (some b, false) =>
      match L with
      | [] => use SemiThueData.refl ; rfl
      | (none, true) :: tail =>
        simp at len
        specialize ih tail (some b, false) len
        use SemiThueData.trans (SemiThueData.grid_style.append_right_w_length _ (@SemiThueData.step _ _ _ _ [] [] (grid_style.over b))).1 (SemiThueData.cons ih.1)
        simp only [SemiThueData.grid_style.length_trans, Nat.add_eq_zero_iff]
        exact ⟨(SemiThueData.grid_style.append_right_w_length _ _).2,
          SemiThueData.grid_style.cons.trans ih.2⟩
      | (none, false) :: tail => use SemiThueData.refl ; rfl
      | (some c, true) :: tail1 => use SemiThueData.refl ; rfl
      | (some c, false) :: tail1 => use SemiThueData.refl ; rfl
  exact H L.length _ _ (by simp)


noncomputable def equiv_move_ones_for_len : SemiThueData grid_style L (move_ones L) := by
  induction L
  · exact SemiThueData.refl
  rename_i head tail ih
  exact SemiThueData.trans (SemiThueData.cons ih) (equiv_insert_w_len).1

@[simp]
theorem equiv_insert_length_zero {b c} : SemiThueData.grid_style.length (@equiv_insert_w_len b c).1 = 0 := by
  exact (@equiv_insert_w_len b c).2

@[simp]
theorem move_ones_length_zero {b} : SemiThueData.grid_style.length (@equiv_move_ones_for_len b) = 0 := by
  induction b with
  | nil => simp [equiv_move_ones_for_len]
  | cons head tail ih =>
    unfold equiv_move_ones_for_len
    simp only [SemiThueData.grid_style.length_trans, Nat.add_eq_zero_iff]
    refine ⟨?_, equiv_insert_length_zero⟩
    exact SemiThueData.grid_style.cons.trans ih

noncomputable def SemiThueData.grid_style.reversing_step_w_length (d1)
      (gr : SemiThueData grid_style (SignedList.to_SignedOptionList a) b')
      (b'_is : SignedOptionList.toSignedList b' =
      e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b')
      (rel_holds : grid_style_nontrivial
      [(some c1, false), (some c2, true)] d1) :
      Σ b', (gr' : SemiThueData grid_style (SignedList.to_SignedOptionList a) b') ×
      PLift (SignedOptionList.toSignedList b' =
      e ++ (SignedOptionList.toSignedList d1) ++ f) × irreducible b' ×
      PLift (SemiThueData.grid_style.length gr + 1 = SemiThueData.grid_style.length gr'):= by
  have H1 : [(c1, false), (c2, true)].InfixData (SignedOptionList.toSignedList b') := by
    rw [b'_is]
    use e, f
    exact {down := rfl}
  rcases (pairsTogether_of_irreducible pt_b) b' (List.InfixData.refl b') c1 c2 H1 with ⟨w, t, hwt⟩
  rw [← hwt.1] at b'_is
  rw [SignedOptionList.toSignedList_append, SignedOptionList.toSignedList_append] at b'_is
  simp only [SignedOptionList.toSignedList] at b'_is
  have ptw : pairsTogether w := by
    rw [← hwt.1] at pt_b
    exact (pairsTogether_append (pairsTogether_append (pairsTogether_of_irreducible pt_b)).1).1
  have ptt : pairsTogether t := by
    rw [← hwt.1, List.append_assoc] at pt_b
    exact (pairsTogether_append (pairsTogether_append (pairsTogether_of_irreducible pt_b)).2).2
  rw [← hwt.1] at pt_b
  have := giant_list_split b'_is (irreducible_append (irreducible_append pt_b).1).1
    (irreducible_append pt_b).2
  rcases this with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
  · use move_ones (w ++ d1 ++ t)
    have hi := hwt.1.symm
    subst hi
    use (by apply SemiThueData.trans gr; exact SemiThueData.trans (SemiThueData.step _ _ (by cases rel_holds with
        | basic n => exact grid_style.basic c1
        | apart h => exact grid_style.apart h
        | close h => exact grid_style.close h)) equiv_move_ones_for_len)
    constructor
    · exact {down := by rw [toSignedList_move_ones, SignedOptionList.toSignedList_append, SignedOptionList.toSignedList_append, h2.1.1,
        h2.1.2]}
    constructor
    · exact move_ones_irreducible
    constructor
    cases rel_holds <;> simp
  · use move_ones (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
    have hi := hwt.1.symm
    subst hi
    have hi2 := hw.1.1
    subst hi2
    use
      (by apply SemiThueData.trans gr; apply (SemiThueData.grid_style.append_right_w_length _ <|
      (SemiThueData.grid_style.append_right_w_length _ (SemiThueData.step _ _ (by
        cases rel_holds with
        | basic n => exact grid_style.basic c1
        | apart h => exact grid_style.apart h
        | close h => exact grid_style.close h))).1).1.trans equiv_move_ones_for_len)
    constructor
    · rw [toSignedList_move_ones, SignedOptionList.toSignedList_append, SignedOptionList.toSignedList_append, hw.1.2.1, hw.1.2.2]
      exact {down := by simp [SignedOptionList.toSignedList, SignedOptionList.toSignedList_append]}
    constructor
    · exact move_ones_irreducible
    constructor
    cases rel_holds <;> simp
  use move_ones (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
  have hi := hwt.1.symm
  rw [List.append_assoc] at hi
  subst hi
  have another := ht.1.1
  subst another
  rw [List.append_assoc, List.append_assoc, List.append_assoc, ← List.append_assoc t1]
  use (by apply SemiThueData.trans gr ((SemiThueData.grid_style.append_left_w_length _
            ((SemiThueData.grid_style.append_left_w_length _ (SemiThueData.step _ _ (by
                cases rel_holds with
                | basic n => exact grid_style.basic c1
                | apart h => exact grid_style.apart h
                | close h => exact grid_style.close h))).1)).1.trans equiv_move_ones_for_len))
  constructor
  · rw [toSignedList_move_ones, SignedOptionList.toSignedList_append, SignedOptionList.toSignedList_append, ht.1.2.1, ht.1.2.2]
    exact {down := by simp [SignedOptionList.toSignedList, SignedOptionList.toSignedList_append]}
  constructor
  · exact move_ones_irreducible
  constructor
  simp only [SemiThueData.grid_style.length_trans, SemiThueData.grid_style.length_step,
    move_ones_length_zero, Nat.add_zero,
    SemiThueData.grid_style.length_append_left_w_length]
  cases rel_holds <;> rfl


noncomputable def SemiThueDataDerivation.reversing.to_grid_style_w_length
  (h : SemiThueDataDerivation reversing a b) :
   Σ b', (h1 : SemiThueData grid_style (SignedList.to_SignedOptionList a) b') ×
   PLift (SignedOptionList.toSignedList b' = b) × irreducible b' ×
   PLift (SemiThueDataDerivation.reversing.length h = SemiThueData.grid_style.length h1) := by
  induction h with
  | refl =>
    rename_i a
    use SignedList.to_SignedOptionList a, SemiThueData.refl
    constructor
    · exact { down := SignedOptionList.toSignedList_toSignedOptionList}
    constructor
    · exact SignedList.toSignedOptionList_irreducible
    constructor
    rfl
  | step h1 h2 ih =>
    rename_i c d e f g
    rcases ih with ⟨b', gr, b'_is, pt_b⟩
    cases h2 with
    | basic h_dist =>
      apply Nat.eq_of_dist_eq_zero at h_dist
      have H := SemiThueData.grid_style.reversing_step_w_length ([(none, true), (none, false)]) gr  b'_is.1 pt_b.1 --(.basic h_dist)
      rw [h_dist] at H
      specialize H (.basic _)
      rcases H with ⟨b'', gr', b'_is', pt_b', hlen⟩
      use b'', gr'
      constructor
      · constructor
        rw [b'_is'.1]
        simp [SignedOptionList.toSignedList]
      constructor
      · exact pt_b'
      constructor
      rw [SemiThueDataDerivation.reversing.length]
      rw [pt_b.2.1]
      exact hlen.1
    | apart h_dist =>
      rename_i i j
      have H := SemiThueData.grid_style.reversing_step_w_length ([(some j, true), (some i, false)]) gr b'_is.1 pt_b.1 (.apart h_dist)
      rcases H with ⟨b'', gr', b'_is', pt_b', hlen⟩
      use b'', gr'
      constructor
      · constructor
        rw [b'_is'.1]
        simp [SignedOptionList.toSignedList]
      constructor
      · exact pt_b'
      constructor
      rw [SemiThueDataDerivation.reversing.length]
      rw [pt_b.2.1]
      exact hlen.1
    | close h_dist =>
      rename_i i j
      have H := SemiThueData.grid_style.reversing_step_w_length ([(some j, true), (some i, true), (some j, false), (some i, false)]) gr b'_is.1 pt_b.1 (.close h_dist)
      rcases H with ⟨b'', gr', b'_is', pt_b', hlen⟩
      use b'', gr'
      constructor
      · constructor
        rw [b'_is'.1]
        simp [SignedOptionList.toSignedList]
      constructor
      · exact pt_b'
      constructor
      rw [SemiThueDataDerivation.reversing.length]
      rw [pt_b.2.1]
      exact hlen.1

noncomputable def SemiThueData.reversing.to_grid_style_w_length (h : SemiThueData reversing a b) :
   Σ b', (h1 : SemiThueData grid_style (SignedList.to_SignedOptionList a) b') × PLift
  (SignedOptionList.toSignedList b' = b) × irreducible b' × PLift (SemiThueData.reversing.length h = SemiThueData.grid_style.length h1) := by
  have H := (SemiThueData.reversing.toSemiThueDataDerivation_with_length h)
  have H2 := SemiThueDataDerivation.reversing.to_grid_style_w_length H.1
  rcases H2 with ⟨b', h1, h2, irr, hl⟩
  use b', h1, h2, irr
  rw [← hl.1]
  exact H.2

noncomputable def SemiThueData.reversing.to_grid_style_w_length_no_irr_fact (h : SemiThueData reversing a c) :
    Σ c1, Σ (h1 : SemiThueData grid_style (SignedList.to_SignedOptionList a) c1),
    PLift (SemiThueData.reversing.length h = SemiThueData.grid_style.length h1) := by
  have H := SemiThueData.reversing.to_grid_style_w_length h
  rcases H with ⟨c1, h1, h2, h3, hl⟩
  use c1, h1
  exact hl

noncomputable def SemiThueData.reversing.to_grid_style_w_length_horizontal_vertical_edge
    (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
    (ha : a.length > 0) (hb : b.length > 0) :
    Σ c1, Σ (h1 : SemiThueData grid_style ((to_vertical_edge a) ++ (to_horizontal_edge b)) c1),
    PLift (SemiThueData.reversing.length h = SemiThueData.grid_style.length h1) ×
    PLift (SignedOptionList.toSignedList c1 = c) := by
  rcases SemiThueData.reversing.to_grid_style_w_length h with ⟨c1, h1, hl⟩
  rw [← (toSignedOptionList_to_vertical_edge_no_epsilon ha), ← (toSignedOptionList_to_horizontal_edge_no_epsilon hb), ← SignedList.to_SignedOptionList_append]
  use c1, h1
  exact ⟨hl.2.2, hl.1⟩
