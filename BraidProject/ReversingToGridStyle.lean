import BraidProject.PairInfixIrreducibleCases
import BraidProject.ToEdge

namespace Braid

open Relations

noncomputable def SemiThueData.grid_style_reversing_step (d1)
      (gr : SemiThueData grid_style (SignedList.to_SignedOptionList a) b')
      (b'_is : SignedOptionList.toSignedList b' =
      e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b')
      (rel_holds : grid_style_nontrivial
      [(some c1, false), (some c2, true)] d1) :
      Σ b', (gr' : SemiThueData grid_style (SignedList.to_SignedOptionList a) b') ×
      PLift (SignedOptionList.toSignedList b' =
      e ++ (SignedOptionList.toSignedList d1) ++ f) × irreducible b' ×
      PLift (SemiThueData.length grid_style.length gr + 1 = SemiThueData.length grid_style.length gr'):= by
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
  have := pair_infix_irreducible_cases b'_is (irreducible_append (irreducible_append pt_b).1).1
    (irreducible_append pt_b).2
  rcases this with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
  · use move_ones (w ++ d1 ++ t)
    have hi := hwt.1.symm
    subst hi
    use (by apply SemiThueData.trans gr; exact SemiThueData.trans (SemiThueData.step _ _ (by cases rel_holds with
        | basic n => exact grid_style.basic c1
        | apart h => exact grid_style.apart h
        | close h => exact grid_style.close h)) equiv_move_ones)
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
      (by
      apply SemiThueData.trans gr
      refine SemiThueData.trans ?_ equiv_move_ones
      apply SemiThueData.append_right
      apply SemiThueData.append_right
      apply SemiThueData.step _ _ (grid_style.of_grid_style_nontrivial rel_holds))
    constructor
    · rw [toSignedList_move_ones, SignedOptionList.toSignedList_append, SignedOptionList.toSignedList_append, hw.1.2.1, hw.1.2.2]
      exact {down := by simp [SignedOptionList.toSignedList, SignedOptionList.toSignedList_append]}
    constructor
    · exact move_ones_irreducible
    constructor
    simp
    cases rel_holds <;> rfl
  use move_ones (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
  have hi := hwt.1.symm
  rw [List.append_assoc] at hi
  subst hi
  have another := ht.1.1
  subst another
  rw [List.append_assoc, List.append_assoc, List.append_assoc, ← List.append_assoc t1]
  use (by
      apply SemiThueData.trans gr
      refine SemiThueData.trans ?_ equiv_move_ones
      apply SemiThueData.append_left
      apply SemiThueData.append_left
      apply SemiThueData.step _ _ (grid_style.of_grid_style_nontrivial rel_holds))
  constructor
  · rw [toSignedList_move_ones, SignedOptionList.toSignedList_append, SignedOptionList.toSignedList_append, ht.1.2.1, ht.1.2.2]
    exact {down := by simp [SignedOptionList.toSignedList, SignedOptionList.toSignedList_append]}
  constructor
  · exact move_ones_irreducible
  constructor
  simp [List.cons_append, List.nil_append, SemiThueData.length_trans,
    Nat.add_left_cancel_iff]
  cases rel_holds <;> rfl

open SignedOptionList SignedList in
noncomputable def SemiThueDataDerivation.reversing.to_grid_style_w_length
    (h : SemiThueDataDerivation reversing a b) :
    Σ b', (h1 : SemiThueData grid_style (SignedList.to_SignedOptionList a) b') ×
    PLift (SignedOptionList.toSignedList b' = b) × irreducible b' ×
    PLift (SemiThueDataDerivation.length reversing.length h = SemiThueData.length grid_style.length h1) := by
  induction h with
  | refl =>
    rename_i a
    use SignedList.to_SignedOptionList a, SemiThueData.refl
    exact ⟨⟨toSignedList_toSignedOptionList⟩, toSignedOptionList_irreducible, ⟨rfl⟩⟩
  | step h1 h2 ih =>
    rename_i c d e f g
    rcases ih with ⟨b', gr, b'_is, pt_b⟩
    rcases reversing.spec h2 with ⟨i, j, ⟨rfl⟩⟩
    have H := SemiThueData.grid_style_reversing_step (toSignedOptionList_nil_to_empty_corner d) gr  b'_is.1 pt_b.1
    rcases H (reversing.to_grid_style_nontrivial h2) with ⟨b'', gr', b'_is', pt_b', hlen⟩
    use b'', gr'
    rw [b'_is'.1, SemiThueDataDerivation.length, pt_b.2.1]
    unfold reversing.length
    exact ⟨⟨by simp⟩, pt_b', ⟨hlen.1⟩⟩

noncomputable def SemiThueData.reversing.to_grid_style_w_length (h : SemiThueData reversing a b) :
   Σ b', (h1 : SemiThueData grid_style (SignedList.to_SignedOptionList a) b') × PLift
  (SignedOptionList.toSignedList b' = b) × irreducible b' × PLift (SemiThueData.length (fun _ => 1) h = SemiThueData.length grid_style.length h1) := by
  have ⟨b', h1, h2, irr, hl⟩ := SemiThueDataDerivation.reversing.to_grid_style_w_length (SemiThueData.toSemiThueDataDerivation h)
  use b', h1, h2, irr
  rw [← hl.1]
  exact ⟨SemiThueData.toSemiThueDataDerivation_length.symm⟩

-- the following two theorems have some overlap; they are stated so as to match their individual use cases precisely
noncomputable def SemiThueData.reversing.to_grid_style_w_length_horizontal_vertical_edge
    (h : SemiThueData reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
    (ha : a.length > 0) (hb : b.length > 0) :
    Σ c1, Σ (h1 : SemiThueData grid_style ((to_vertical_edge a) ++ (to_horizontal_edge b)) c1),
    PLift (SemiThueData.length (fun _ => 1) h = SemiThueData.length grid_style.length h1) ×
    PLift (SignedOptionList.toSignedList c1 = c) × irreducible c1 := by
  rcases SemiThueData.reversing.to_grid_style_w_length h with ⟨c1, h1, hl⟩
  rw [← (toSignedOptionList_to_vertical_edge_no_epsilon ha), ← (toSignedOptionList_to_horizontal_edge_no_epsilon hb), ← SignedList.to_SignedOptionList_append]
  use c1, h1
  exact ⟨hl.2.2, hl.1, hl.2.1⟩

open SignedOptionList List

noncomputable def SemiThueData.reversing.to_grid_style_NegPos_to_PosNeg (h : SemiThueData reversing a b) (ha : SignedList.NegPosData a)
    (hb : SignedList.PosNegData b) :
    Σ b', SemiThueData grid_style (SignedList.to_SignedOptionList a) b' ×
    SignedList.NegPosData (SignedList.to_SignedOptionList a) × SignedList.PosNegData b' ×
    PLift (SignedOptionList.toSignedList b' = b) := by
  rcases SemiThueData.reversing.to_grid_style_w_length h with ⟨b', gr, b'_is, pt_b⟩
  use b'
  constructor
  · exact gr
  constructor
  · exact SignedList.toSignedOptionList_NegPosData ha
  constructor
  · apply PosNegData_of_toSignedList_PosNeg_and_irreducible _ pt_b.1
    rw [b'_is.1]
    exact hb
  exact b'_is
