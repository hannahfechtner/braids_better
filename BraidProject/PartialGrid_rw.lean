import BraidProject.PartialGrid_bounded

-- noncomputable def foo (h : PartialGrid a b c (d1 ++ d2 ++ []) e) :
--     {h1 : PartialGrid a b c (d1 ++ d2) e // h.length = h1.length} := by
--   revert h
--   generalize h2 : d1 ++ d2 ++ [] = d'
--   rw [List.append_nil] at h2
--   subst h2
--   intro h
--   use h

-- noncomputable def foo'' (h' : d1 = d2) (h1 : PartialGrid a b c d1 e) :
--     {h2 : PartialGrid a b c d2 e // h1.length = h2.length} := by
--   revert h1
--   subst h'
--   intro h
--   use h

-- noncomputable def foo''' (h : PartialGrid a b c (d1 ++ d2 ++ []) e) :
--     {h1 : PartialGrid a b c (d1 ++ d2) e // h.length = h1.length} := foo'' (by simp) _

-- noncomputable def foo' (h : PartialGrid a b c ([] ++ d) e) :
--     (h1 : PartialGrid a b c d e) × PLift (h.length = h1.length) := by
--   use h
--   exact ⟨rfl⟩

-- theorem unique_split_horiz_extended (h : PartialGrid a0 b0 c0 d0 e0)
--     (h1 : PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid e1 b2 c2 d2 e2)
--     (h3 : PartialGrid a3 b3 c3 d3 e3) (h4 : PartialGrid e3 b4 c4 d4 e4) (he1 : e1.length > 0) (he3 : e3.length > 0)
--     (ha : a1 = a3) (hb1 : b1 = b3) (hb2 : b2 = b4) (he : e2 = e4)
--     (hf : c1 ++ d1 ++ c2 ++ d2 = c3 ++ d3 ++ c4 ++ d4)
--     (ha0 : a0 = a1) (hb0 : b0 = b1 ++ b2) (hf : (c0 = c1 ∧ d0 = d1 ++ c2++d2) ∨ (c0 = c1 ++ c2 ∧ d0 = d2 ∧ d1 = [])) (he0 : e0 = e2) :
--     e1 = e3 ∧ d1 = d3 ∧ c2 = c4 ∧ d2 = d4 ∧ c1 = c3 := by
--   induction h generalizing a1 b1 c1 d1 e1 b2 c2 d2 e2 a3 b3 c3 d3 e3 b4 c4 d4 e4  with
--   | single_gridt h =>
--     rename_i hf1 a5 b5 c5 d5
--     cases h
--     all_goals
--       simp only [to_over] at hb0
--       rcases List.append_eq_singleton_iff.mp hb0.symm with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
--       · have H := PartialGrid.top_length_pos h1
--         rw [b1_is] at H
--         simp at H
--       have H := PartialGrid.top_length_pos h2
--       rw [b2_is] at H
--       simp at H
--   | empty a b ha ha1 hb hb1 =>
--     exfalso
--     rcases hf with ⟨hc0, hd0⟩ | ⟨hc0, hd0, d1_nil⟩
--     · rcases middle_frontier_nil_or_caps h1 with ⟨⟨d1_nil⟩⟩ | ⟨frontd1, midd1, caboosed1, d1_spec⟩
--       · exact (not_both_empty_early h1 hc0.symm d1_nil).elim
--       rcases middle_frontier_nil_or_caps h2 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, midd2, caboosed2, d2_spec⟩
--       · exact (not_both_empty h2 d2_nil he0.symm).elim
--       rw [d1_spec.1, d2_spec.1] at hd0
--       --stupid list fact
--       sorry
--     rw [List.nil_eq, List.append_eq_nil_iff] at hc0
--     exact not_both_empty_early h1 hc0.1 d1_nil
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     rename_i hf1 a5 b5 bot5 up5 b6 bot6 mid6 up6
--     rcases List.append_eq_append_iff.mp hb0 with ⟨as, one, two⟩ | back
--     · match as with
--       | [] =>
--         simp at one two
--         sorry
--       | afront :: arest => sorry
--     sorry --specialize g1_ih ha0
--   | horizontal_append h g1 g2 g1_ih g2_ih => sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry

-- theorem unique_split_horiz
--     (h1 : PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid e1 b2 c2 d2 e2)
--     (h3 : PartialGrid a3 b3 c3 d3 e3) (h4 : PartialGrid e3 b4 c4 d4 e4) (he1 : e1.length > 0) (he3 : e3.length > 0)
--     (ha : a1 = a3) (hb1 : b1 = b3) (hb2 : b2 = b4) (he : e2 = e4)
--     (hf : c1 ++ d1 ++ c2 ++ d2 = c3 ++ d3 ++ c4 ++ d4) : e1 = e3 ∧ d1 = d3 ∧ c2 = c4 ∧ d2 = d4 ∧ c1 = c3 := by
--   match d1 with
--   | [] =>
--     apply unique_split_horiz_extended (PartialGrid.horizontal_append_one h1 h2) h1 h2 h3 h4 he1 he3 ha hb1 hb2 he hf rfl rfl
--       (Or.inr ⟨rfl, ⟨rfl, rfl⟩⟩) rfl
--   | d11 :: d12 =>
--     exact unique_split_horiz_extended (PartialGrid.horizontal_append (by simp) h1 h2) h1 h2 h3 h4 he1 he3 ha hb1 hb2 he hf rfl rfl (Or.inl ⟨rfl, rfl⟩) rfl

-- theorem unique_split_horiz_tt
--     (h1 : PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid e1 b2 c2 d2 e2)
--     (h3 : PartialGrid a3 b3 c3 d3 e3) (h4 : PartialGrid e3 b4 c4 d4 e4) (he1 : e1.length > 0) (he3 : e3.length > 0)
--     (ha : a1 = a3) (hb1 : b1 = b3) (hb2 : b2 = b4) (he : e2 = e4)
--     (hf : c1 ++ d1 ++ c2 ++ d2 = c3 ++ d3 ++ c4 ++ d4) : e1 = e3 ∧ d1 = d3 ∧ c2 = c4 ∧ d2 = d4 ∧ c1 = c3 := by
--   induction h1 with
--   | single_gridt h =>
--     cases h with
--     | empty =>
--       simp [to_up, to_over] at hf
--       simp [to_up, to_over]
--       match d3 with
--       | [] =>
--         have d24 : d2 = d4 := by sorry -- stupid list fact
--         simp [to_up] at ha
--         simp [to_over] at hb1
--         have H := pg_empty h3 ha.symm hb1.symm rfl
--         aesop
--       | d31 :: d32 =>
--         have H : e3 = [] := by sorry -- this can be done by induction on partial grids
--         rw [H] at he3
--         simp at he3
--     | top_bottom i =>
--       simp [to_up, to_over]
--       simp [to_up] at ha
--       simp [to_over] at hb1
--       match d3 with
--       | [] =>
--         simp [to_over] at hf
--         have d24 : d2 = d4 := by sorry -- stupid list fact
--         have H := pg_top_bottom h3 ha.symm hb1.symm rfl
--         aesop
--       | d31 :: d32 => sorry
--     | sides i => sorry
--     | top_left i => sorry
--     | adjacent i k h => sorry
--     | separated i j h =>
--       simp [to_up, to_over]
--       simp [to_up] at ha
--       simp [to_over] at hb1
--       match d3 with
--       | [] =>
--         simp [to_over] at hf
--         have d24 : d2 = d4 := by sorry -- stupid list fact
--         have H := pg_separated h3 ha.symm hb1.symm rfl (or_dist_iff.mpr h)
--         aesop
--       | d31 :: d32 => sorry
--   | empty a b ha ha1 hb hb => simp at he1
--   | horizontal_append_one g1 g2 g1_ih g2_ih => sorry
--   | horizontal_append h g1 g2 g1_ih g2_ih => sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry

-- theorem empty_frontier_unique (h1: PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid a2 b2 c2 [] e2)
--   (ha : a1 = a2) (hb : b1 = b2) (hd : d1 = []): c1 = c2 ∧ e1 = e2 := by
--   induction h1 with
--   | single_gridt h => sorry
--   | empty a b ha ha1 hb hb => sorry
--   | horizontal_append_one g1 g2 g1_ih g2_ih => sorry
--   | horizontal_append h g1 g2 g1_ih g2_ih => sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry

theorem empty_helper
    (g : PartialGrid a b c d e) (c_is : c = []) (d_is : d = a ++ b) (e_is : e = []) :
    g.length = 0 := by
  induction g with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i => simp [to_up, to_over] at d_is
    | adjacent i j h => simp [to_up, to_over] at d_is
    | separated i j h => simp [to_up, to_over] at d_is
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp at c_is
    exact (not_both_empty_early g1 c_is.1 rfl).elim
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases middle_frontier_nil_or_caps g1 with ⟨⟨mid_nil⟩⟩ | ⟨frontm, midm, caboosem, specm⟩
    · exact (not_both_empty_early g1 c_is mid_nil).elim
    rcases middle_frontier_nil_or_caps g2 with ⟨⟨mid2_nil⟩⟩ | ⟨frontm2, midm2, caboosem2, specm2⟩
    · exact (not_both_empty g2 mid2_nil e_is).elim
    rw [specm.1, specm2.1] at d_is
    rename_i f g i j k l m n o
    rcases List.append_eq_append_iff.mp d_is with ⟨as, one, two⟩ | ⟨as, one, two⟩
    · have H : is_false f := g1.left_frontier_is_false
      rw [one] at H
      specialize H (caboosem, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    have H : is_true (g ++ l) := by
      apply is_true_of_true_true
      exact g1.top_frontier_is_true
      exact g2.top_frontier_is_true
    rw [two] at H
    specialize H (frontm2, false) ⟨by simp⟩
    simp at H
    exact H.1.elim
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    simp at e_is
    exact (not_both_empty g1 rfl e_is.2).elim
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases middle_frontier_nil_or_caps g1 with ⟨⟨mid_nil⟩⟩ | ⟨frontm, midm, caboosem, specm⟩
    · exact (not_both_empty g1 mid_nil e_is).elim
    rcases middle_frontier_nil_or_caps g2 with ⟨⟨mid2_nil⟩⟩ | ⟨frontm2, midm2, caboosem2, specm2⟩
    · exact (not_both_empty_early g2 c_is mid2_nil).elim
    rw [specm.1, specm2.1] at d_is
    rename_i f g i j k l m n o
    rcases List.append_eq_append_iff.mp d_is with ⟨as, one, two⟩ | ⟨as, one, two⟩
    · have H : is_false (l ++ f) := by
        apply is_false_of_false_false
        exact g2.left_frontier_is_false
        exact g1.left_frontier_is_false
      rw [one] at H
      specialize H (caboosem2, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    have H : is_true g := g1.top_frontier_is_true
    rw [two] at H
    specialize H (frontm, false) ⟨by simp⟩
    simp at H
    exact H.1.elim

theorem same_type_same_length_pg (g1 : PartialGrid a b c d e) (g2 : PartialGrid a1 b1 c1 d1 e1) :
    a = a1 → b = b1 → c = c1 → d = d1 → e = e1 → g1.length = g2.length := by
  induction g1 generalizing a1 b1 c1 d1 e1 with
  | single_gridt h =>
    rename_i f g l m
    intro a_is b_is c_is d_is e_is
    cases h with
    | empty =>
      simp [PartialGrid.length]
      simp [to_up] at a_is
      simp [to_over] at b_is
      exact (all_ones_length_pg _ a_is.symm b_is.symm).symm
    | top_bottom i =>
      simp [PartialGrid.length]
      simp [to_up] at a_is
      simp [to_over] at b_is
      exact (top_bottom_length_pg _ a_is.symm b_is.symm).symm
    | sides i =>
      simp [PartialGrid.length]
      simp [to_up] at a_is
      simp [to_over] at b_is
      exact (side_side_length_pg _ a_is.symm b_is.symm).symm
    | top_left i =>
      simp [PartialGrid.length]
      simp [to_up] at a_is
      simp [to_over] at b_is
      have rme : remove_ones (c1 ++ d1 ++ e1) = [] := by
        rw [← c_is, ← d_is, ← e_is]
        simp [remove_ones]
      exact (top_left_length_pg _ a_is.symm b_is.symm rme).symm
    | adjacent i j h =>
      simp [PartialGrid.length]
      simp [to_up] at a_is
      simp [to_over] at b_is
      have rme : remove_ones (c1 ++ d1 ++ e1) =
        [(j, true), (i, true), (j, false), (i, false)] := by
        rw [← c_is, ← d_is, ← e_is]
        simp [remove_ones]
      exact (adjacent_length_pg _ a_is.symm b_is.symm rme h).symm
    | separated i j h =>
      simp [PartialGrid.length]
      simp [to_up] at a_is
      simp [to_over] at b_is
      have rme : remove_ones (c1 ++ d1 ++ e1) = [(j, true), (i, false)] := by
        rw [← c_is, ← d_is, ← e_is]
        simp [remove_ones]
      exact (separated_length_pg _ a_is.symm b_is.symm rme (or_dist_iff.mpr h)).symm
  | empty a b ha ha1 hb hb1 =>
    intro a_is b_is c_is d_is e_is
    simp [PartialGrid.length]
    symm
    rw [a_is, b_is] at d_is
    exact empty_helper _ c_is.symm d_is.symm e_is.symm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a3 b3 bot3 up3 b4 bot4 mid4 up4 g3
    intro a_is b_is c_is d_is e_is
    have split_it := splittable_vertically_of_pg' g2 _ _ b_is.symm (PartialGrid.top_length_pos g1) (PartialGrid.top_length_pos g3)
    rcases split_it with ⟨mid, c2, d2, c3, d3, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
    · rw [len]
      specialize g1_ih i1 a_is rfl
      specialize g2_ih i2
      rw [← c_is, ← d_is] at long
      sorry
      -- have H := unique_split_horiz g1 g3 i1 i2 (PartialGrid.left_length_pos g3)
      --   (PartialGrid.left_length_pos i2) a_is rfl rfl e_is (by simp [long])
      -- specialize g1_ih H.2.2.2.2 H.2.1 H.1
      -- specialize g2_ih H.1 rfl H.2.2.1 H.2.2.2.1 e_is
      -- simp [g1_ih, g2_ih, PartialGrid.length]
    rcases b with ⟨d5, d6, h5, ⟨len⟩, ⟨e1_nil⟩, ⟨d_is⟩, ⟨b4_is⟩⟩
    rw [e1_nil] at e_is
    sorry
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a3 b3 bot3 mid3 up3 b4 bot4 mid4 up4 g3
    intro a_is b_is c_is d_is e_is
    have split_it := splittable_vertically_of_pg' g2 _ _ b_is.symm (PartialGrid.top_length_pos g1) (PartialGrid.top_length_pos g3)
    rcases split_it with ⟨mid, c2, d2, c3, d3, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
    · rw [len]
      specialize g1_ih i1 a_is rfl
      specialize g2_ih i2
      rw [← c_is, ← d_is, ← List.append_assoc, ← List.append_assoc] at long
      sorry
      -- have H := unique_split_horiz g1 g3 i1 i2 (PartialGrid.left_length_pos g3)
      --   (PartialGrid.left_length_pos i2) a_is rfl rfl e_is long
      -- specialize g1_ih H.2.2.2.2 H.2.1 H.1
      -- specialize g2_ih H.1 rfl H.2.2.1 H.2.2.2.1 e_is
      -- simp [g1_ih, g2_ih, PartialGrid.length]
    rw [PartialGrid.length]
    rcases b with ⟨k1, k2, j1,⟨len⟩, ⟨e1_nil⟩, ⟨d1_is⟩, ⟨b4_is⟩⟩
    rw [len]
    specialize g1_ih j1 a_is rfl c_is
    sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

-- theorem same_type_same_length_pg_rm (g1 : PartialGrid a b c d e) (g2 : PartialGrid a1 b1 c1 d1 e1) :
--     a = a1 → b = b1 → remove_ones (c ++ d++ e) = remove_ones (c1 ++ d1 ++ e1) → g1.length = g2.length := by
--   induction g1 generalizing a1 b1 c1 d1 e1 g2 with
--   | single_gridt h =>
--     rename_i f g l m
--     intro a1_is a2_is rm
--     cases h with
--     | empty =>
--       simp [PartialGrid.length]
--       simp [to_up] at a1_is
--       simp [to_over] at a2_is
--       exact (all_ones_length_pg _ a1_is.symm a2_is.symm).symm
--     | top_bottom i =>
--       simp [PartialGrid.length]
--       simp [to_up] at a1_is
--       simp [to_over] at a2_is
--       exact (top_bottom_length_pg _ a1_is.symm a2_is.symm).symm
--     | sides i =>
--       simp [PartialGrid.length]
--       simp [to_up] at a1_is
--       simp [to_over] at a2_is
--       exact (side_side_length_pg _ a1_is.symm a2_is.symm).symm
--     | top_left i =>
--       simp [PartialGrid.length]
--       simp [to_up] at a1_is
--       simp [to_over] at a2_is
--       simp only [to_over, List.append_nil, to_up, List.cons_append, List.nil_append, remove_ones] at rm
--       exact (top_left_length_pg _ a1_is.symm a2_is.symm rm.symm).symm
--     | adjacent i j h =>
--       simp [PartialGrid.length]
--       simp [to_up] at a1_is
--       simp [to_over] at a2_is
--       simp only [to_over_cons_cons, to_over_singleton, List.append_nil, to_up_cons_cons,
--         to_up_singleton, List.cons_append, List.nil_append, remove_ones] at rm
--       exact (adjacent_length_pg _ a1_is.symm a2_is.symm rm.symm h).symm
--     | separated i j h =>
--       simp [PartialGrid.length]
--       simp [to_up] at a1_is
--       simp [to_over] at a2_is
--       simp only [to_over, List.map_cons, List.map_nil, List.append_nil, to_up, List.reverse_cons,
--         List.reverse_nil, List.nil_append, List.cons_append, remove_ones] at rm
--       exact (separated_length_pg _ a1_is.symm a2_is.symm rm.symm (or_dist_iff.mpr h)).symm
--   | empty a b ha ha1 hb hb1 =>
--     intro a1_is a2_is rm
--     simp [PartialGrid.length]
--     rw [a1_is, a2_is, List.nil_append, List.append_nil] at rm
--     sorry -- exact (skeleton_length_pg _ rm).symm
--   | horizontal_append_one g1 g3 g1_ih g2_ih =>
--     rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
--     intro a2_is b2b3_is rm
--     rw [PartialGrid.length]
--     rcases splittable_vertically_of_pg' g2 _ _ b2b3_is.symm (PartialGrid.top_length_pos g1) (PartialGrid.top_length_pos g3)
--       with ⟨mid4, c4, d4, c5, d5, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
--     · rw [len]
--       specialize g1_ih i1 a2_is rfl
--       specialize g2_ih i2

--       sorry
--     sorry
--   | horizontal_append h g1 g2 g1_ih g2_ih => sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry

inductive grid_style_real : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| basic (n : ℕ) : grid_style_real [(some n, false), (some n, true)] [(none, true), (none, false)]
| apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style_real [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style_real [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

def gs_of_real (h : grid_style_real a b) : grid_style a b := by
  match h with
  | grid_style_real.basic n => exact grid_style.basic n
  | grid_style_real.apart hdist => exact grid_style.apart hdist
  | grid_style_real.close hdist => exact grid_style.close hdist

noncomputable def grid_style_real_split (h : grid_style_real i j) : Σ a b, PLift (i = [(some a, false), (some b, true)]) := by
  induction h with
  | basic =>
    rename_i n
    use n, n
    exact {down := rfl}
  | apart h =>
    rename_i i j
    use i, j
    exact {down := rfl}
  | close h =>
    rename_i i j
    use i, j
    exact {down := rfl}

noncomputable def grid_rel_real_means (h : grid_style_real i j) : Σ a b c d,
    (h1 : cell (option_to_cell (some a)) (option_to_cell (some b)) c d) ×
    PLift (i = [(some a, false), (some b, true)] ∧ j = to_over d ++ to_up c) ×
    PLift ((PartialGrid.single_gridt h1).length = 1):= by
  cases h with
  | basic n =>
    use n, n, [], []
    exact ⟨cell.top_left n, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | apart h =>
    rename_i i j
    use i, j, [i], [j]
    exact ⟨cell.separated i j (or_dist_iff.mp h), ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | close h =>
    rename_i i j
    use i, j, [i, j], [j, i]
    exact ⟨cell.adjacent i j h, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩

noncomputable def skeleton_one_one_real (h : grid_style_real i j) (ha : a.length > 0) (hb : b.length > 0)
    (i_is : i = [(a3, false), (b3, true)]) (ab : [(a3, false), (b3, true)] = a ++ b) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = j) × PLift (h1.length = 1) := by
  rcases grid_rel_real_means h with ⟨a1, b1, c1, d1, h_cell, ⟨i_is', j_is⟩, len⟩
  use to_over d1, [], to_up c1
  have ab_is := List.append_eq_len_two ha hb ab.symm
  rw [ab_is.1, ab_is.2]
  change _ = [(a3, false)] ++ [(b3, true)] at i_is
  rw [i_is'] at i_is
  have happ := List.append_eq_len_two (by simp) (by simp) i_is.symm
  rw [happ.1, happ.2]
  rw [← over_oc, ← up_oc]
  use PartialGrid.single_gridt h_cell
  rw [List.append_nil]
  constructor
  · exact ⟨j_is.symm⟩
  exact len

noncomputable def skeleton_one_cons_real (h2 : grid_style_real i j) (fe : a ++ b = ([(a3, false), (b3, true)] ++ head :: tail))
    (b_is : b = b1 ++ head :: tail) (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b)
    (ab_is : [(a3, false), (b3, true)] = a ++ b1) (i_is : i = [(a3, false), (b3, true)]):
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = [] ++ j ++ head :: tail) ×
    PLift (h1.length = 1):= by
  have ht_true : is_true (head :: tail) := by
    rw [b_is] at hb
    exact (is_true_append hb).2
  rcases grid_rel_real_means h2 with ⟨a2, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  use to_over d2, to_up c2 ++ head :: tail, []
  have H2 := PartialGrid.empty (to_up c2) (head :: tail) (by simp [to_up_len_pos]) is_false_up (by simp) ht_true
  have H3 := PartialGrid.horizontal_append_one (PartialGrid.single_gridt h_cell) H2
  simp only [up_oc, over_oc, List.singleton_append, List.append_nil] at H3
  have helper := i_is.symm.trans i_is'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at helper
  have ha : a = [(some a2, false)] := by
    rw [← helper.1]
    exact bool_change_second ha1 ha ab_is.symm
  have hb : b = (some b2, true) :: head :: tail := by
    rw [← helper.2]
    rw [ha] at fe
    simp only [List.singleton_append, List.cons_append, List.cons.injEq, Prod.mk.injEq,
      and_true] at fe
    exact fe.2
  rw [ha, hb]
  use H3
  constructor
  · rw [j_is]
    exact {down := by simp}
  have : H3.length = (PartialGrid.horizontal_append_one (PartialGrid.single_gridt h_cell) H2).length :=
    same_type_same_length_pg H3 ((PartialGrid.single_gridt h_cell).horizontal_append_one H2) rfl
        rfl (by simp) rfl rfl
  rw [PartialGrid.length, hl.1] at this
  have : H2.length = (PartialGrid.empty (to_up c2) (head :: tail) (by simp [to_up_len_pos]) is_false_up (by simp) ht_true).length :=
    same_type_same_length_pg
      H2 (PartialGrid.empty (to_up c2) (head :: tail) (by simp [to_up_len_pos]) is_false_up (by simp) ht_true) rfl
        rfl (by simp) rfl rfl
  rw [PartialGrid.length] at this
  constructor
  omega

noncomputable def skeleton_cons_one_real (h2 : grid_style_real i j) (a_is : a = head :: tail ++ a2)
    (ha : is_false a) (hb : is_true b) (ab_is : [(a3, false), (b3, true)] = a2 ++ b1)
    (i_is : i = [(a3, false), (b3, true)]) (b_is : b = b1) (hb1 : b.length > 0) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = head :: tail ++ j ++ []) ×
    PLift (h1.length = 1):= by
  rcases grid_rel_real_means h2 with ⟨a5, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  have ht_false : is_false (head :: tail) := by
    rw [a_is] at ha
    exact (is_false_append ha).1
  have H2 := PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos]) ht_false (by simp [to_over_len_pos]) is_true_over
  have H3 := PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell) H2
  use [], head::tail ++ to_over d2, to_up c2
  rw [a_is]
  have H := i_is.symm.trans i_is'
  simp at H
  rw [List.nil_append, up_oc, over_oc, ← H.1, ← H.2] at H3
  have H2 : b = [(b3, true)] := by
    rw [b_is]
    rw [b_is] at hb1
    rw [b_is] at hb
    exact bool_change_first hb1 hb ab_is.symm
  have H1 : a2 = [(a3, false)] := by
    rw [← b_is, ← H2] at ab_is
    change [(a3, false)] ++ b = _ ++ b at ab_is
    exact (List.append_cancel_right ab_is).symm
  rw [H1, H2]
  use H3
  constructor
  · rw [j_is]
    exact {down := by simp}
  constructor
  have : H3.length = (PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell)
      (PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos])
      ht_false (by simp [to_over_len_pos]) is_true_over)).length :=
    same_type_same_length_pg H3
      ((PartialGrid.single_gridt h_cell).vertical_append_one
      (PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos])
      ht_false (by simp [to_over_len_pos]) is_true_over)) (by simp [H.1, up_oc])
      (by simp [H.2, over_oc]) rfl rfl rfl
  rw [PartialGrid.length, hl.1, PartialGrid.length] at this
  exact this

noncomputable def skeleton_cons_cons_real (gs : grid_style_real i j)
    (ha : is_false (head :: tail)) (hb : is_true (headb :: tailb))
    (i_is : i = [(a3, false), (b3, true)]) :
    Σ bot mid up, (h1 : PartialGrid (head :: tail ++ [(a3, false)])
    ([(b3, true)] ++ headb :: tailb) bot mid up) ×
    PLift (bot ++ mid ++ up = head :: tail ++ j ++ headb :: tailb) × PLift (h1.length = 1):= by
  rcases grid_rel_real_means gs with ⟨a5, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  use [], head :: tail ++ to_over d2 ++ to_up c2 ++ headb :: tailb, []
  have H2 := PartialGrid.empty (head :: tail) (to_over d2) (by simp) ha (by simp [to_over_len_pos]) is_true_over
  have H3 := PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell) H2
  have H4 := PartialGrid.empty (to_up c2) (headb :: tailb) to_up_len_pos is_false_up (by simp) hb
  have H5 := PartialGrid.horizontal_append (by simp) H3 H4
  rw [List.append_nil] at H5
  have hi := i_is.symm.trans i_is'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hi
  rw [← hi.1, up_oc, ← hi.2, over_oc] at H5
  simp only [List.cons_append, List.singleton_append, List.append_assoc]
  simp only [List.cons_append, List.singleton_append, List.append_assoc] at H5
  rw [← List.append_assoc (to_over d2), ← List.append_assoc tail, ← List.append_assoc tail] at H5
  use H5
  constructor
  · exact {down := by simp [j_is]}
  constructor
  have : H5.length = (PartialGrid.horizontal_append (by simp)
      (PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell)
      (PartialGrid.empty (head :: tail) (to_over d2) (by simp) ha (by simp [to_over_len_pos]) is_true_over))
      (PartialGrid.empty (to_up c2) (headb :: tailb) to_up_len_pos is_false_up (by simp) hb)).length :=
    same_type_same_length_pg H5 _ (by simp [hi.1, up_oc])
      (by simp [hi.2, over_oc]) rfl (by simp) rfl
  rw [this, PartialGrid.length, PartialGrid.length, hl.1, PartialGrid.length]
  simp [PartialGrid.length]

open PartialGrid

noncomputable def add_cell_w_len (h : PartialGrid a b bot mid up) (hg : grid_style_real i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
    Σ nb nm nu, (h1 : PartialGrid a b nb nm nu) × PLift (nb ++ nm ++ nu = k ++ j ++ l) × List.Suffix' up nu × List.Prefix' bot nb ×
    PLift (h.length < h1.length) := by
  rcases grid_style_real_split hg with ⟨a1, b1, ⟨i_is⟩⟩
  rw [i_is] at fe
  induction h generalizing k l with
  | single_gridt h =>
    exfalso
    rw [List.append_nil] at fe
    exact over_up_neq_false_true fe
  | empty a b ha ha1 hb hb1 =>
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
              List.singleton_append] at fe
    rcases over_up_splits_at_i ha1 hb1 ha fe with ⟨a1, a2, b1, b2, a_is, b_is, i_is, k_is, l_is⟩
    cases a1 with
    | nil =>
      rw [List.nil_append] at a_is
      rw [a_is] at ha1
      rw [← k_is]
      cases b2 with
      | nil =>
        rw [← l_is, List.append_nil]
        rw [List.append_nil] at b_is
        rw [b_is] at hb
        rw [← a_is,← b_is] at i_is
        rw [List.nil_append]
        rw [← b_is] at hb
        have H := skeleton_one_one_real hg (by assumption) hb (by assumption) i_is
        rcases H with ⟨b, m, u, h3, h4, hl⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.nil_suffix_C, ⟨List.nil_prefix_C, ?_⟩⟩⟩⟩
        constructor
        simp [PartialGrid.length, hl.1]
      | cons head tail =>
        rw [← l_is]
        rw [← k_is, List.nil_append, ← l_is] at fe
        rw [← a_is] at ha1
        have := skeleton_one_cons_real hg fe b_is ha1 ha hb1 (by rw [← a_is] at i_is; exact i_is)
          (by assumption)
        rcases this with ⟨b, m, u, h3, h4, hl⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.nil_suffix_C, ⟨List.nil_prefix_C, ?_⟩⟩⟩⟩
        constructor
        simp [PartialGrid.length, hl.1]
    | cons head tail =>
      cases b2 with
      | nil =>
        rw [← k_is, ← l_is,]
        rw [List.append_nil] at b_is
        have := skeleton_cons_one_real hg a_is ha1 hb1 i_is (by assumption) b_is hb
        rcases this with ⟨b, m, u, h3, h4, ⟨hl⟩⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.nil_suffix_C, ⟨List.nil_prefix_C, ?_⟩⟩⟩⟩
        simp [PartialGrid.length]
        constructor
        omega
      | cons headb tailb =>
        rw [a_is] at ha1
        rw [b_is] at hb1
        have H3 := bool_split (is_false_append ha1).2 (is_true_append hb1).1 i_is
        rw [← k_is, ← l_is]
        have := skeleton_cons_cons_real hg (is_false_append ha1).1 (is_true_append hb1).2 (by assumption)
        rcases this with ⟨b', m, u, h3, h4⟩
        use b', m, u
        rw [← H3.1, ← H3.2, ← b_is, ← a_is] at h3
        use h3
        constructor
        · exact h4.1
        constructor
        · exact List.nil_suffix_C
        constructor
        · exact List.nil_prefix_C
        rename_i old
        have : h3.length = old.length :=
          same_type_same_length_pg h3 old (by rw [a_is, H3.1]) (by rw [b_is, H3.2]) rfl rfl (by simp [H3.1, H3.2])
        rw [this, h4.2.1]
        constructor
        simp [PartialGrid.length]
  | horizontal_append_one g1 g2 ih1 ih2 =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    rcases big_split_first (PartialGrid.bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
    rcases @ih2 k₂ l eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
    use bot2 ++ bot1, mid1, up1
    use PartialGrid.horizontal_append_one g1 pg1
    constructor
    · simp [k_is, k₁_is, fe]
      simp at fe1
      exact fe1
    refine ⟨h5, ⟨(List.prefix_append_right_inj_C).2 h6.1, ?_⟩⟩
    constructor
    simp [PartialGrid.length]
    exact h6.2.1
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
    have := double_split_horiz (bottom_frontier_is_true g1) (Sum.inl (bottom_frontier_is_true g2))
      (right_frontier_is_false g2) fe (middle_frontier_nil_or_caps g1)
      (middle_frontier_nil_or_caps g2)
    rcases this with hl | hr
    · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
      rcases g2_ih k2_is.symm with ⟨bot3, mid3, up3, hpg, hf⟩
      use bot2, mid2 ++ bot3++mid3, up3
      use PartialGrid.horizontal_append h g1 hpg
      simp [k_is, k1_is, k2_is, hf.1.1]
      constructor
      · exact ⟨trivial⟩
      constructor
      · exact hf.2.1
      constructor
      · exact bot2.prefix_refl_C
      constructor
      simp [PartialGrid.length, hf.2.2.2.1]
    rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
    have H3 : bot2 ++ mid2 ++ up2 = k ++ [(some a1, false), (some b1, true)] ++ (l₁ ++ up2) := by
      rw [← l2_is]
      simp
    have H := @g1_ih k (l₁ ++ up2) H3
    rcases @g1_ih k (l₁ ++ up2) H3 with ⟨bot4, mid4, up4, hpg, ⟨hf⟩, ⟨to_add, ⟨spec⟩⟩, back2, ⟨h6⟩⟩
    cases mid4 with
    | nil =>
      cases to_add with
      | nil =>
        use bot4 ++ bot3, mid3, up3
        rw [List.nil_append] at spec
        rw [← spec] at hpg
        use PartialGrid.horizontal_append_one hpg g2
        simp only [PartialGrid.length]
        constructor
        · rw [spec, ← List.append_assoc, List.append_nil] at hf
          apply List.append_cancel_right at hf
          rw [hf, l_is, l1_is]
          exact ⟨by simp⟩
        constructor
        · exact List.suffix_refl_C
        constructor
        · rcases back2 with ⟨r, hr⟩
          use r ++ bot3
          rw [← hr.1]
          constructor
          simp
        constructor
        simp
        rename_i old
        have H : hpg.length = old.length :=
          same_type_same_length_pg hpg old rfl rfl rfl rfl spec
        simp [H, h6]
      | cons heade taile =>
        use bot4, (heade :: taile) ++ bot3 ++ mid3, up3
        simp only [PartialGrid.length]
        have lf : is_false (heade :: taile) := by
            have H0 : is_false up4 := by exact right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_append H0).1
        have H := PartialGrid.extend_bottom_w_len g2 (heade::taile) lf (by simp)
        rw [← spec] at hpg
        have H2 := PartialGrid.horizontal_append_one hpg H.1
        simp only [List.append_nil, List.cons_append] at H2
        simp only [List.cons_append, List.append_assoc, List.append_assoc]
        use H2
        constructor
        · constructor
          rw [← spec] at hf
          rw [List.append_nil, ← List.append_assoc, ← List.append_assoc, List.append_left_inj] at hf
          rw [l_is, l1_is]
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
            ← List.append_assoc, ← List.append_assoc, ← List.cons_append, ← List.cons_append,
            ← List.cons_append, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
            List.append_left_inj, List.append_left_inj, List.append_left_inj, hf]
        constructor
        · exact List.suffix_refl_C
        constructor
        · exact back2
        constructor
        have : H2.length = (PartialGrid.horizontal_append_one hpg H.1).length :=
          same_type_same_length_pg H2 (PartialGrid.horizontal_append_one hpg H.1) rfl rfl (by simp) rfl rfl
        rw [this]
        simp [PartialGrid.length]
        rename_i old
        have : hpg.length = old.length :=
          same_type_same_length_pg hpg old rfl rfl rfl rfl spec
        rw [this]
        have : g2.length = H.1.length := H.2.1
        rw [← this]
        simp_all
    | cons head tail =>
      cases to_add with
      | nil =>
        use bot4, head::tail ++ bot3 ++ mid3, up3
        rw [List.nil_append] at spec
        rw [← spec] at hpg
        use PartialGrid.horizontal_append (by simp) hpg g2
        constructor
        · rw [spec, ← List.append_assoc] at hf
          change bot4 ++ ([head] ++ tail) ++ up4 = k ++ j ++ l₁ ++ up4 at hf
          rw [← List.append_assoc] at hf
          constructor
          change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up3 = _
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.append_cancel_right hf]
          simp [l_is, l1_is]
        constructor
        · exact List.suffix_refl_C
        constructor
        · assumption
        simp [PartialGrid.length]
        constructor
        rename_i old
        have H : hpg.length = old.length :=
          same_type_same_length_pg hpg old rfl rfl rfl rfl spec
        simp [H, h6]
      | cons heade taile =>
        use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up3
        have lf : is_false (heade :: taile) := by
          have H0 : is_false up4 := right_frontier_is_false hpg
          rw [← spec] at H0
          exact (is_false_append H0).1
        rw [← spec] at hpg
        have H3 := (PartialGrid.extend_bottom_w_len g2 (heade::taile) lf (by simp))
        have H2 := PartialGrid.horizontal_append (by simp) hpg H3.1
        have nonsense : head :: tail ++ [] ++ (heade :: taile ++ bot3 ++ mid3) =
          (head :: tail ++ heade :: taile ++ bot3 ++ mid3) := by simp
        rw [← nonsense]
        use H2
        constructor
        · rw [l_is, l1_is]
          rw [← spec, ← List.append_assoc, ← List.append_assoc] at hf
          apply List.append_cancel_right at hf
          constructor
          conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
          simp
        constructor
        · exact List.suffix_refl_C
        constructor
        · assumption
        have : H2.length = (PartialGrid.horizontal_append (by simp) hpg
          H3.1).length :=
          same_type_same_length_pg H2 _ rfl rfl rfl rfl rfl
        simp [this, PartialGrid.length]
        rename_i old
        have : hpg.length = old.length :=
          same_type_same_length_pg hpg old rfl rfl rfl rfl spec
        rw [this]
        rw [← H3.2.1]
        constructor
        omega
  | vertical_append_one g1 g2 ih1 ih2 =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
      rcases @ih2 _ _ eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
      use bot1, mid1, up1 ++ up2
      use PartialGrid.vertical_append_one g1 pg1
      constructor
      · constructor
        rw [l_is, l₂_is, ← List.append_assoc, fe1.1, ← List.append_assoc]
      constructor
      · exact List.suffix_append_right_C h5
      constructor
      · exact h6.1
      constructor
      simp [PartialGrid.length, h6.2.1]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a b bot mid up a2 bot2 mid2 up2
    have := double_split_horiz' (bottom_frontier_is_true g2) (Sum.inr (right_frontier_is_false g2))
      (right_frontier_is_false g1) fe (middle_frontier_nil_or_caps g2) (middle_frontier_nil_or_caps g1)
    rcases this with ⟨k1, k2, k_is, k1_is, k2_is⟩ | ⟨l1, l2, l_is, l1_is, l2_is⟩
    · specialize @g1_ih (bot ++ k2) l (by rw [List.append_assoc, ← k2_is]; simp)
      rcases g1_ih with ⟨nb, nm, nu, pg, fe', upp, botp, len⟩
      rcases botp with ⟨to_add, spec⟩
      cases to_add with
      | nil =>
        rw [List.append_nil] at spec
        rw [← spec.1] at pg
        rw [spec.1] at fe'
        cases nm with
        | nil =>
          use bot2, mid2, up2++nu
          use PartialGrid.vertical_append_one pg g2
          simp only [List.append_nil, List.append_assoc, List.append_cancel_left_eq] at fe'
          constructor
          · constructor
            rw [fe'.1, k_is, k1_is]
            simp
          rcases upp with ⟨t, ⟨ht⟩⟩
          constructor
          · use up2 ++ t; exact ⟨by simp [ht]⟩
          constructor
          · exact List.prefix_refl_C
          constructor
          simp [PartialGrid.length]
          rename_i old
          have H : pg.length = old.length :=
            same_type_same_length_pg pg old rfl rfl spec.1 rfl rfl
          rw [H]
          exact len.1
        | cons head tail =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          use PartialGrid.vertical_append pg g2 (by simp)
          constructor
          · rw [k_is]
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            constructor
            conv => rhs; rw [List.append_assoc, List.append_assoc, ← fe'.1, k1_is]
            simp
          constructor
          · exact upp
          constructor
          · exact List.prefix_refl_C
          constructor
          simp [PartialGrid.length]
          rename_i old
          have H : pg.length = old.length :=
            same_type_same_length_pg pg old rfl rfl spec.1 rfl rfl
          rw [H]
          exact len.1
      | cons head tail =>
        cases nm with
        | nil =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          have H1 : is_true (head:: tail) := by
            have H : is_true nb := bottom_frontier_is_true pg
            rw [← spec.1] at H
            exact (is_true_append H).2
          have H2 := (extend_side_w_len g2 (head::tail) H1 (by simp))
          rw [spec.1] at H2
          use PartialGrid.vertical_append_one pg H2.1
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_nil, List.append_assoc, List.cons_append,
              List.append_cancel_left_eq] at fe'
            constructor
            simp [k_is, k1_is, spec.1, fe'.1]
          constructor
          · exact upp
          constructor
          · exact List.prefix_refl_C
          constructor
          simp [PartialGrid.length, len.1, H2.2.1]
        | cons head1 tail1 =>
          use bot2, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
          have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec.1] at H
              exact (is_true_append H).2
          have H2 := (extend_side_w_len g2 (head::tail) H1 (by simp))
          rw [spec.1] at H2
          have H := PartialGrid.vertical_append pg H2.1 (by simp)
          rw [List.append_nil] at H
          use H
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            constructor
            simp [k_is, k1_is, spec.1, fe'.1]
          constructor
          · exact upp
          constructor
          · exact List.prefix_refl_C
          constructor
          simp [PartialGrid.length]
          have : H.length = (PartialGrid.vertical_append pg H2.1 (by simp)).length :=
            same_type_same_length_pg H (PartialGrid.vertical_append pg H2.1 (by simp)) rfl rfl rfl (by simp) rfl
          rw [this, PartialGrid.length]
          rw [← H2.2.1]
          simp [len.1]
    rw [← l2_is] at g2_ih
    rcases @g2_ih k l1 (by simp) with ⟨nb, nm, nu, pg, fe', upp, botp⟩
    use nb, nm ++ nu ++mid, up
    use PartialGrid.vertical_append g1 pg h
    constructor
    · constructor
      rw [l_is, l1_is, ← List.append_assoc, ← List.append_assoc, fe'.1, ← List.append_assoc, ← List.append_assoc]
    constructor
    · exact List.suffix_refl_C
    constructor
    · exact botp.1
    constructor
    simp [PartialGrid.length, botp.2.1]

theorem get_n'_same''  (c0 c3 c₁ c₂) (hr : reversing c₁ c₂)
  (h1 : PartialGrid a b c5 d5 e5)
  (h6 : remove_ones (c5 ++ d5 ++ e5) = c0 ++ c₁ ++ c3)
  (h2 : PartialGrid a b c6 d6 e6)
  (h7 : remove_ones (c6 ++ d6 ++ e6) = c0 ++ c₂ ++ c3) :
  h1.length < h2.length := by
  sorry
