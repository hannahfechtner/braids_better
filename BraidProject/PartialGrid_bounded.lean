import BraidProject.PartialGrid_split

theorem pg_skeleton (h : PartialGrid a b c d e) (hd : d = a ++ b) :
    c = [] ∧ e = [] := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp [to_up, to_over] at hd
  | empty a b ha ha1 hb hb =>
    exact ⟨rfl, rfl⟩
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    have H := PartialGrid.horizontal_append_one g1 g2
    sorry -- should be doable because of equivalence
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    have H := PartialGrid.horizontal_append h g1 g2
    sorry
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    have H := PartialGrid.vertical_append_one g1 g2
    sorry
  | vertical_append g1 g2 h g1_ih g2_ih =>
    have H := PartialGrid.vertical_append g1 g2 h
    sorry

--requires weak uniqueness
-- theorem empty_middle_frontier_eq_sides (h1 : PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid a2 b2 c2 d2 e2)
--   (ha : a1 = a2) (hb : b1 = b2) (hd : d1 = d2) : c1 = c2 ∧ e1 = e2 := by
--   induction h1 generalizing a2 b2 c2 d2 e2 with
--   | single_gridt h =>
--     cases h with
--     | empty =>
--       simp [to_up] at ha
--       simp [to_over] at hb
--       simp [to_up, to_over]
--       have H := pg_empty h2 ha.symm hb.symm hd.symm
--       aesop
--     | top_bottom i =>
--       simp [to_up] at ha
--       simp [to_over] at hb
--       simp [to_up, to_over]
--       have H := pg_top_bottom h2 ha.symm hb.symm hd.symm
--       aesop
--     | sides i =>
--       simp [to_up] at ha
--       simp [to_over] at hb
--       simp [to_up, to_over]
--       have H := pg_side_side h2 ha.symm hb.symm hd.symm
--       aesop
--     | top_left i =>
--       simp [to_up] at ha
--       simp [to_over] at hb
--       simp [to_up, to_over]
--       have H := pg_top_left h2 ha.symm hb.symm hd.symm
--       aesop
--     | adjacent i k h =>
--       simp [to_up] at ha
--       simp [to_over] at hb
--       simp [to_up, to_over]
--       have H := pg_adjacent h2 ha.symm hb.symm hd.symm h
--       aesop
--     | separated i j h =>
--       simp [to_up] at ha
--       simp [to_over] at hb
--       simp [to_up, to_over]
--       have H := pg_separated h2 ha.symm hb.symm hd.symm (or_dist_iff.mpr h)
--       aesop
--   | empty a b ha ha1 hb hb1 =>
--     have H := pg_skeleton h2 (by aesop)
--     aesop
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     rename_i a3 b3 bot3 up3 b4 bot4 mid4 up4
--     have b3_len : b3.length > 0 := PartialGrid.top_length_pos g1
--     rcases splittable_vertically_of_pg' h2 _ _ hb.symm
--       (PartialGrid.top_length_pos g1) (PartialGrid.top_length_pos g2)
--       with ⟨es, c5, d5, c6, d6, i1, i2, ⟨long⟩, ⟨len⟩⟩ | h2
--     · specialize g1_ih i1 ha rfl
--       specialize g2_ih i2
--       sorry
--     sorry
--   | horizontal_append h g1 g2 g1_ih g2_ih => sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry

-- theorem horizontal_one_helper (g1 : PartialGrid a1 b1 bot1 [] up1)
--     (g2 : PartialGrid up1 b2 bot2 mid2 up2)
--     (rm : remove_ones (a1 ++ (b1 ++ b2)) = remove_ones (bot1 ++ bot2 ++ mid2 ++ up2)) :
--     remove_ones a1 ++ remove_ones b1 = remove_ones bot1 ++ remove_ones up1 := by
--   induction a1 using List.reverseRecOn generalizing b1 bot1 up1 b2 bot2 mid2 up2 with
--   | nil =>
--     have H := PartialGrid.left_length_pos g1
--     simp at H
--   | append_singleton front caboose ih =>
--     sorry


-- theorem skeleton_length_pg (h : PartialGrid a b c d e) : remove_ones (a ++ b) = remove_ones (c ++ d ++ e) → h.length = 0 := by
--   induction h with
--   | single_gridt h =>
--     cases h with
--     | empty => simp [PartialGrid.length]
--     | top_bottom i => simp [PartialGrid.length]
--     | sides i => simp [PartialGrid.length]
--     | top_left i =>
--       intro rm
--       simp [to_up, to_over, remove_ones] at rm
--     | adjacent i k h =>
--       intro rm
--       simp [to_up, to_over, remove_ones] at rm
--     | separated i j h =>
--       intro rm
--       simp [to_up, to_over, remove_ones] at rm
--   | empty a b ha ha1 hb hb => simp [PartialGrid.length]
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     simp only [remove_ones_append, List.append_nil] at g1_ih
--     simp only [remove_ones_append, List.append_assoc] at g2_ih
--     intro rm
--     rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
--     have hg1 : g1.length = 0 := by
--       apply g1_ih
--       sorry
--     have hg2 : g2.length = 0 := by
--       apply g2_ih
--       sorry
--     rw [PartialGrid.length, hg1, hg2]
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     simp only [remove_ones_append, List.append_nil] at g1_ih
--     simp only [remove_ones_append, List.append_assoc] at g2_ih
--     intro rm
--     rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
--     have hg1 : g1.length = 0 := by
--       apply g1_ih
--       sorry
--     have hg2 : g2.length = 0 := by
--       apply g2_ih
--       sorry
--     rw [PartialGrid.length, hg1, hg2]
--   | vertical_append_one g1 g2 g1_ih g2_ih =>
--     simp only [remove_ones_append, List.append_nil] at g1_ih
--     simp only [remove_ones_append, List.append_assoc] at g2_ih
--     intro rm
--     rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
--     have hg1 : g1.length = 0 := by
--       apply g1_ih
--       sorry
--     have hg2 : g2.length = 0 := by
--       apply g2_ih
--       sorry
--     rw [PartialGrid.length, hg1, hg2]
--   | vertical_append g1 g2 h g1_ih g2_ih =>
--     simp only [remove_ones_append, List.append_nil] at g1_ih
--     simp only [remove_ones_append, List.append_assoc] at g2_ih
--     intro rm
--     rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
--     have hg1 : g1.length = 0 := by
--       apply g1_ih
--       sorry
--     have hg2 : g2.length = 0 := by
--       apply g2_ih
--       sorry
--     rw [PartialGrid.length, hg1, hg2]

-- theorem empty_helper (g2 : PartialGrid a1 b1 c1 d1 e1)
--     (c_is : [] = c1) (d_is : a1 ++ b1 = d1)
--     (e_is : [] = e1) : g2.length = 0 := by
--   induction g2 with
--   | single_gridt h =>
--     rename_i a b c d
--     match a with
--     | [] => simp [to_up] at d_is
--     | af :: atail => simp [to_up] at d_is
--   | empty a b ha ha1 hb hb => simp [PartialGrid.length]
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     exfalso
--     simp at c_is
--     exact not_both_empty_early g1 c_is.1 rfl
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
--     specialize g1_ih c_is
--     simp [e_is] at g2_ih
--     match bot3 with
--     | [] =>
--       specialize g2_ih e_is.symm
--       sorry
--     | bot31 :: bot32 => sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih =>
--     exfalso
--     simp at e_is
--     apply not_both_empty g1 rfl e_is.2
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry
#check unicity_c

theorem unique_split_horiz_extended (h : PartialGrid a0 b0 c0 d0 e0)
    (h1 : PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid e1 b2 c2 d2 e2)
    (h3 : PartialGrid a3 b3 c3 d3 e3) (h4 : PartialGrid e3 b4 c4 d4 e4) (he1 : e1.length > 0) (he3 : e3.length > 0)
    (ha : a1 = a3) (hb1 : b1 = b3) (hb2 : b2 = b4) (he : e2 = e4)
    (hf : c1 ++ d1 ++ c2 ++ d2 = c3 ++ d3 ++ c4 ++ d4)
    (ha0 : a0 = a1) (hb0 : b0 = b1 ++ b2) (hf : (c0 = c1 ∧ d0 = d1 ++ c2++d2) ∨ (c0 = c1 ++ c2 ∧ d0 = d2 ∧ d1 = [])) (he0 : e0 = e2) :
    e1 = e3 ∧ d1 = d3 ∧ c2 = c4 ∧ d2 = d4 ∧ c1 = c3 := by
  induction h generalizing a1 b1 c1 d1 e1 b2 c2 d2 e2 a3 b3 c3 d3 e3 b4 c4 d4 e4  with
  | single_gridt h =>
    rename_i hf1 a5 b5 c5 d5
    cases h
    all_goals
      simp only [to_over] at hb0
      rcases List.append_eq_singleton_iff.mp hb0.symm with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
      · have H := PartialGrid.top_length_pos h1
        rw [b1_is] at H
        simp at H
      have H := PartialGrid.top_length_pos h2
      rw [b2_is] at H
      simp at H
  | empty a b ha ha1 hb hb1 =>
    exfalso
    rcases hf with ⟨hc0, hd0⟩ | ⟨hc0, hd0, d1_nil⟩
    · rcases middle_frontier_nil_or_caps h1 with ⟨⟨d1_nil⟩⟩ | ⟨frontd1, midd1, caboosed1, d1_spec⟩
      · exact (not_both_empty_early h1 hc0.symm d1_nil).elim
      rcases middle_frontier_nil_or_caps h2 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, midd2, caboosed2, d2_spec⟩
      · exact (not_both_empty h2 d2_nil he0.symm).elim
      rw [d1_spec.1, d2_spec.1] at hd0
      --stupid list fact
      sorry
    rw [List.nil_eq, List.append_eq_nil_iff] at hc0
    exact not_both_empty_early h1 hc0.1 d1_nil
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i hf1 a5 b5 bot5 up5 b6 bot6 mid6 up6
    rcases List.append_eq_append_iff.mp hb0 with ⟨as, one, two⟩ | back
    · match as with
      | [] =>
        simp at one two
        sorry
      | afront :: arest => sorry
    sorry --specialize g1_ih ha0
  | horizontal_append h g1 g2 g1_ih g2_ih => sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

theorem unique_split_horiz
    (h1 : PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid e1 b2 c2 d2 e2)
    (h3 : PartialGrid a3 b3 c3 d3 e3) (h4 : PartialGrid e3 b4 c4 d4 e4) (he1 : e1.length > 0) (he3 : e3.length > 0)
    (ha : a1 = a3) (hb1 : b1 = b3) (hb2 : b2 = b4) (he : e2 = e4)
    (hf : c1 ++ d1 ++ c2 ++ d2 = c3 ++ d3 ++ c4 ++ d4) : e1 = e3 ∧ d1 = d3 ∧ c2 = c4 ∧ d2 = d4 ∧ c1 = c3 := by
  match d1 with
  | [] =>
    apply unique_split_horiz_extended (PartialGrid.horizontal_append_one h1 h2) h1 h2 h3 h4 he1 he3 ha hb1 hb2 he hf rfl rfl
      (Or.inr ⟨rfl, ⟨rfl, rfl⟩⟩) rfl
  | d11 :: d12 =>
    exact unique_split_horiz_extended (PartialGrid.horizontal_append (by simp) h1 h2) h1 h2 h3 h4 he1 he3 ha hb1 hb2 he hf rfl rfl (Or.inl ⟨rfl, rfl⟩) rfl

theorem unique_split_horiz_tt
    (h1 : PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid e1 b2 c2 d2 e2)
    (h3 : PartialGrid a3 b3 c3 d3 e3) (h4 : PartialGrid e3 b4 c4 d4 e4) (he1 : e1.length > 0) (he3 : e3.length > 0)
    (ha : a1 = a3) (hb1 : b1 = b3) (hb2 : b2 = b4) (he : e2 = e4)
    (hf : c1 ++ d1 ++ c2 ++ d2 = c3 ++ d3 ++ c4 ++ d4) : e1 = e3 ∧ d1 = d3 ∧ c2 = c4 ∧ d2 = d4 ∧ c1 = c3 := by
  induction h1 with
  | single_gridt h =>
    cases h with
    | empty =>
      simp [to_up, to_over] at hf
      simp [to_up, to_over]
      match d3 with
      | [] =>
        have d24 : d2 = d4 := by sorry -- stupid list fact
        simp [to_up] at ha
        simp [to_over] at hb1
        have H := pg_empty h3 ha.symm hb1.symm rfl
        aesop
      | d31 :: d32 =>
        have H : e3 = [] := by sorry -- this can be done by induction on partial grids
        rw [H] at he3
        simp at he3
    | top_bottom i =>
      simp [to_up, to_over]
      simp [to_up] at ha
      simp [to_over] at hb1
      match d3 with
      | [] =>
        simp [to_over] at hf
        have d24 : d2 = d4 := by sorry -- stupid list fact
        have H := pg_top_bottom h3 ha.symm hb1.symm rfl
        aesop
      | d31 :: d32 => sorry
    | sides i => sorry
    | top_left i => sorry
    | adjacent i k h => sorry
    | separated i j h =>
      simp [to_up, to_over]
      simp [to_up] at ha
      simp [to_over] at hb1
      match d3 with
      | [] =>
        simp [to_over] at hf
        have d24 : d2 = d4 := by sorry -- stupid list fact
        have H := pg_separated h3 ha.symm hb1.symm rfl (or_dist_iff.mpr h)
        aesop
      | d31 :: d32 => sorry
  | empty a b ha ha1 hb hb => simp at he1
  | horizontal_append_one g1 g2 g1_ih g2_ih => sorry
  | horizontal_append h g1 g2 g1_ih g2_ih => sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

theorem empty_frontier_unique (h1: PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid a2 b2 c2 [] e2)
  (ha : a1 = a2) (hb : b1 = b2) (hd : d1 = []): c1 = c2 ∧ e1 = e2 := by
  induction h1 with
  | single_gridt h => sorry
  | empty a b ha ha1 hb hb => sorry
  | horizontal_append_one g1 g2 g1_ih g2_ih => sorry
  | horizontal_append h g1 g2 g1_ih g2_ih => sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

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
    sorry --exact empty_helper _ c_is d_is e_is
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a3 b3 bot3 up3 b4 bot4 mid4 up4 g3
    intro a_is b_is c_is d_is e_is
    have split_it := splittable_vertically_of_pg' g2 _ _ b_is.symm (PartialGrid.top_length_pos g1) (PartialGrid.top_length_pos g3)
    rcases split_it with ⟨mid, c2, d2, c3, d3, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
    · rw [len]
      specialize g1_ih i1 a_is rfl
      specialize g2_ih i2
      rw [← c_is, ← d_is] at long
      have H := unique_split_horiz g1 g3 i1 i2 (PartialGrid.left_length_pos g3)
        (PartialGrid.left_length_pos i2) a_is rfl rfl e_is (by simp [long])
      specialize g1_ih H.2.2.2.2 H.2.1 H.1
      specialize g2_ih H.1 rfl H.2.2.1 H.2.2.2.1 e_is
      simp [g1_ih, g2_ih, PartialGrid.length]
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
      have H := unique_split_horiz g1 g3 i1 i2 (PartialGrid.left_length_pos g3)
        (PartialGrid.left_length_pos i2) a_is rfl rfl e_is long
      specialize g1_ih H.2.2.2.2 H.2.1 H.1
      specialize g2_ih H.1 rfl H.2.2.1 H.2.2.2.1 e_is
      simp [g1_ih, g2_ih, PartialGrid.length]
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

theorem unique_g_pg_c
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_up a1 = a2)
    (b4_is : to_over b4 = b2)
    (b9 : gridt a1 b4 b6 b7) : to_up b6 = up2 ∧ to_over b7 = bot2 := by
    have H := gridt_of_PartialGrid g1
    unfold gridt_option at H
    have H3 := unicity_c b9 H
    sorry

theorem to_up_inj (h : to_up a = to_up b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons head tail =>
      simp [to_up] at h
      have H2 : List.getLast? [(none, false)] =
        List.getLast? ((List.map (fun x ↦ (some x, false)) tail).reverse ++ [(some head, false)]) := by
        rw [h]
      simp at H2
  | cons head tail ih =>
    cases b with
    | nil =>
      simp [to_up] at h
      have H2 : List.getLast? [(none, false)] =
        List.getLast? ((List.map (fun x ↦ (some x, false)) tail).reverse ++ [(some head, false)]) := by
        rw [h]
      simp at H2
    | cons headb tailb =>
      simp [to_up] at h
      have H2 : List.getLast? ((List.map (fun x ↦ (some x, false)) tail).reverse ++ [(some head, false)]) =
        List.getLast? ((List.map (fun x ↦ (some x, false)) tailb).reverse ++ [(some headb, false)]) := by
        rw [h]
      simp at H2
      simp [H2]
      apply ih
      rw [← H2] at h
      simp at h
      cases tail with
      | nil =>
        cases tailb with
        | nil => rfl
        | cons t1 t2 => simp at h
      | cons t1 t2 =>
        cases tailb with
        | nil =>
          simp at h
        | cons t3 t4 =>
          simp only [to_up]
          simp at h
          simp [h]

theorem to_over_inj (h : to_over a = to_over b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons head tail =>
      simp [to_over] at h
  | cons head tail ih =>
    cases b with
    | nil =>
      simp [to_over] at h
    | cons headb tailb =>
      simp [to_over] at h
      simp [h]
      apply ih
      cases tail with
      | nil =>
        cases tailb with
        | nil => rfl
        | cons t1 t2 => simp at h
      | cons t3 t4 =>
        cases tailb with
        | nil => simp at h
        | cons t1 t2 =>
          simp [to_over]
          simp at h
          exact h.2

theorem split_it_helper (h : to_over [i] ++ ra = to_over a1) : ∃ rra, a1 = FreeMonoid.of i * rra := by
  induction a1  with
  | nil => simp [to_up] at h
  | cons head tail ih =>
    simp [to_over] at h
    use tail
    rw [h.1]
    rfl

def property (a) := ∀ b c d e a1 b1 c1 e1, PartialGrid a b c d e → gridt a1 b1 e1 c1 →
    a = to_up a1 → b = to_over b1 → remover c <+: c1 ∧ remover e.reverse <+: e1

theorem ridic : ∀ a, property a := by
  intro a
  induction ha : a.length using Nat.strongRecOn generalizing a with
  | ind n ih =>
    intro b c d e a1 b1 c1 e1 h h1 a_is b_is
    induction h generalizing a1 b1 e1 c1 with
    | single_gridt h =>
      cases h with
      | empty =>
        apply to_up_inj at a_is
        apply to_over_inj at b_is
        have h1 := all_ones_t h1 a_is.symm b_is.symm
        aesop
      | top_bottom i =>
        apply to_up_inj at a_is
        apply to_over_inj at b_is
        have h1 := i_top_bottom_t h1 _ a_is.symm b_is.symm
        aesop
      | sides i =>
        apply to_up_inj at a_is
        apply to_over_inj at b_is
        have h1 := i_side_side_t h1 _ a_is.symm b_is.symm
        aesop
      | top_left i =>
        apply to_up_inj at a_is
        apply to_over_inj at b_is
        have h1 := i_top_left_t h1 _ a_is.symm b_is.symm
        aesop
      | adjacent i k h =>
        apply to_up_inj at a_is
        apply to_over_inj at b_is
        have h1 := i_adjacent_t h1 _ _ a_is.symm b_is.symm h
        change _ = [i, k] ∧ _ = [k, i] at h1
        simp [h1]
        aesop
      | separated i j h =>
        apply to_up_inj at a_is
        apply to_over_inj at b_is
        have h1 := helpier_ij_t h1 _ _ h a_is.symm b_is.symm
        change _ = [i] ∧ _ = [j] at h1
        aesop
    | empty a b ha ha1 hb hb => simp [remover]
    | horizontal_append_one g1 g2 g1_ih g2_ih =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      have H : ∃ b4 b5, b1 = b4 * b5 ∧ b4.length > 0 ∧ b5.length > 0 := by sorry
      rcases H with ⟨b4, b5, b1_is, b4_len, b5_len⟩
      have splitty := splittable_vertically_of_gridt h1 _ _ b1_is
      rcases splitty with ⟨rest, c1, c2, g3, g4, ⟨c_is⟩, ⟨len1⟩⟩
      have hb : b2 = to_over b4 := by sorry
      have hb1 : b3 = to_over b5 := by sorry
      have hup2 : up2 = to_up rest := by sorry -- from g1 and g3
      have hbot2 : bot2 = to_over c1 := by sorry -- from g1 and g3
      specialize g1_ih ha _ _ _ _ g3 a_is hb
      -- specialize ih up2.length
      -- simp [g2_ih.2, remover_append, hbot2]
      -- change _ <+: (_ ++ _)
      -- refine (List.prefix_append_right_inj c1).mpr ?_
      -- exact g2_ih.1
      sorry
    | horizontal_append h g1 g2 g1_ih g2_ih => sorry
    | vertical_append_one g1 g2 g1_ih g2_ih => sorry
    | vertical_append g1 g2 h g1_ih g2_ih => sorry

theorem grid_pg_suffix_prefix (h : PartialGrid a b c d e) (h1 : gridt a1 b1 e1 c1)
    (ha : a = to_up a1) (hb : b = to_over b1) : remover c <+: c1 ∧ remover e.reverse <+: e1 := by
  induction h generalizing a1 b1 e1 c1 with
  | single_gridt h =>
    cases h with
    | empty =>
      apply to_up_inj at ha
      apply to_over_inj at hb
      have h1 := all_ones_t h1 ha.symm hb.symm
      aesop
    | top_bottom i =>
      apply to_up_inj at ha
      apply to_over_inj at hb
      have h1 := i_top_bottom_t h1 _ ha.symm hb.symm
      aesop
    | sides i =>
      apply to_up_inj at ha
      apply to_over_inj at hb
      have h1 := i_side_side_t h1 _ ha.symm hb.symm
      aesop
    | top_left i =>
      apply to_up_inj at ha
      apply to_over_inj at hb
      have h1 := i_top_left_t h1 _ ha.symm hb.symm
      aesop
    | adjacent i k h =>
      apply to_up_inj at ha
      apply to_over_inj at hb
      have h1 := i_adjacent_t h1 _ _ ha.symm hb.symm h
      change _ = [i, k] ∧ _ = [k, i] at h1
      simp [h1]
      aesop
    | separated i j h =>
      apply to_up_inj at ha
      apply to_over_inj at hb
      have h1 := helpier_ij_t h1 _ _ h ha.symm hb.symm
      change _ = [i] ∧ _ = [j] at h1
      aesop
  | empty a b ha ha1 hb hb =>
    simp [remover]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    have H : ∃ b4 b5, b1 = b4 * b5 ∧ b4.length > 0 ∧ b5.length > 0 := by sorry
    rcases H with ⟨b4, b5, b1_is, b4_len, b5_len⟩
    have splitty := splittable_vertically_of_gridt h1 _ _ b1_is
    rcases splitty with ⟨rest, c1, c2, g3, g4, ⟨c_is⟩, ⟨len1⟩⟩
    have hb : b2 = to_over b4 := by sorry
    have hb1 : b3 = to_over b5 := by sorry
    have hup2 : up2 = to_up rest := by sorry -- from g1 and g3
    have hbot2 : bot2 = to_over c1 := by sorry -- from g1 and g3
    specialize g1_ih g3 ha hb
    specialize g2_ih g4 hup2 hb1
    simp [g2_ih.2, remover_append, hbot2]
    change _ <+: (_ ++ _)
    refine (List.prefix_append_right_inj c1).mpr ?_
    exact g2_ih.1
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
    have H : ∃ b4 b5, b1 = b4 * b5 ∧ b4.length > 0 ∧ b5.length > 0 := by sorry
    rcases H with ⟨b4, b5, b1_is, b4_len, b5_len⟩
    have splitty := splittable_vertically_of_gridt h1 _ _ b1_is
    rcases splitty with ⟨rest, c1, c2, g3, g4, ⟨c_is⟩, ⟨len1⟩⟩
    have hb : b2 = to_over b4 := by sorry
    have hb1 : b3 = to_over b5 := by sorry
    specialize g1_ih g3 ha hb
    constructor
    · exact List.prefix_of_append g1_ih.1
    rcases g1_ih.2 with ⟨rest2, hr⟩
    have H := splittable_horizontally_of_gridt g4 _ _ hr.symm
    rcases H with ⟨u, c1, c2, g5, g6, e1_is⟩
    specialize g2_ih g4



    sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry


-- theorem straight_pg_sm_g (h : PartialGrid a b c d e) (h1 : gridt a1 b1 f g)
--     : a <:+ to_up a1 → b <+: to_over b1 → h.length ≤ h1.length := by
--   induction h generalizing a1 b1 f g with
--   | single_gridt h =>
--     intro ha hb
--     cases h with
--     | empty => simp [PartialGrid.length]
--     | top_bottom i => simp [PartialGrid.length]
--     | sides i => simp [PartialGrid.length]
--     | top_left i =>
--       simp [PartialGrid.length]
--       rcases ha with ⟨ra, hra⟩
--       rcases hb with ⟨rb, hrb⟩
--       have H1 : ∃ rra, a1 = .of i * rra := by sorry
--       have H2 : ∃ rrb, b1 = .of i * rrb := split_it_helper hrb
--       rcases H1 with ⟨rra, dsa⟩
--       rcases H2 with ⟨rrb, dsb⟩
--       rcases splittable_horizontally_of_gridn h1 _ _ dsa with ⟨rest, c1, c2, g1, g2, ⟨c_is⟩, ⟨len1⟩⟩
--       rcases splittable_vertically_of_gridn g1 _ _ dsb with ⟨rest2, d1, d2, g3, g4, ⟨d_is⟩, ⟨len2⟩⟩
--       rw [len1, len2, gridt_length_top_left g3 rfl rfl]
--       omega
--       -- rw [PartialGrid.length, gridt_length_top_left h1 _ (to_over_inj hb)]
--     | adjacent i k h =>
--       simp [PartialGrid.length]
--       rcases ha with ⟨ra, hra⟩
--       rcases hb with ⟨rb, hrb⟩
--       have H1 : ∃ rra, a1 = .of i * rra := by sorry
--       have H2 : ∃ rrb, b1 = .of k * rrb := split_it_helper hrb
--       rcases H1 with ⟨rra, dsa⟩
--       rcases H2 with ⟨rrb, dsb⟩
--       rcases splittable_horizontally_of_gridn h1 _ _ dsa with ⟨rest, c1, c2, g1, g2, ⟨c_is⟩, ⟨len1⟩⟩
--       rcases splittable_vertically_of_gridn g1 _ _ dsb with ⟨rest2, d1, d2, g3, g4, ⟨d_is⟩, ⟨len2⟩⟩
--       rw [len1, len2, gridt_length_adjacent g3 rfl rfl h]
--       omega
--     | separated i j h =>
--       simp [PartialGrid.length]
--       rcases ha with ⟨ra, hra⟩
--       rcases hb with ⟨rb, hrb⟩
--       have H1 : ∃ rra, a1 = .of i * rra := by sorry
--       have H2 : ∃ rrb, b1 = .of j * rrb := split_it_helper hrb
--       rcases H1 with ⟨rra, dsa⟩
--       rcases H2 with ⟨rrb, dsb⟩
--       rcases splittable_horizontally_of_gridn h1 _ _ dsa with ⟨rest, c1, c2, g1, g2, ⟨c_is⟩, ⟨len1⟩⟩
--       rcases splittable_vertically_of_gridn g1 _ _ dsb with ⟨rest2, d1, d2, g3, g4, ⟨d_is⟩, ⟨len2⟩⟩
--       rw [len1, len2, gridt_length_separated g3 _ rfl (or_dist_iff.mpr h)]
--       omega
--       rfl
--       --rw [PartialGrid.length, gridt_length_separated h1 (to_up_inj ha) (to_over_inj hb) (or_dist_iff.mpr h)]
--   | empty a b ha ha1 hb hb =>
--     simp [PartialGrid.length]
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
--     intro ha hb
--     have b2_ne_nil : b2 ≠ [] := by
--       intro hb2
--       rw [hb2] at g1
--       have H := PartialGrid.top_length_pos g1
--       simp at H
--     have b3_neq_nil : b3 ≠ [] := by
--       intro hb3
--       rw [hb3] at g2
--       have H := PartialGrid.top_length_pos g2
--       simp at H
--     have H : ∃ b4 b5, to_over b5 = b3 ∧ to_over b4 = b2 ∧ ((b4 ++ b5) <+: b1) := by
--       sorry
--     rcases H with ⟨b4, b5, b5_is, b4_is, H⟩
--     rcases H with ⟨rest, hr⟩
--     rcases splittable_vertically_of_gridn h1 _ _ hr.symm with ⟨b6, b7, b8, b9, gt, ⟨g_is⟩, ⟨len⟩⟩
--     specialize g1_ih b9 ha
--     rw [len]
--     have b45_ne_nil : b4 ++ b5 ≠ [] := by
--       intro hb45
--       have hb4 : b4 = [] ∧ b5 = [] := List.append_eq_nil_iff.mp hb45
--       rw [hb4.1] at b4_is
--       rw [hb4.2] at b5_is
--       simp [to_over] at b4_is
--       simp [to_over] at b5_is
--       rw [← b4_is, ← b5_is] at hb
--       cases b1 with
--       | h0 =>
--         change _ <+: [(none, true)] at hb
--         simp [List.cons_prefix_cons, List.prefix_nil, List.cons_ne_self, and_false] at hb
--       | ih x xs =>
--         change _ <+: (some x, true) :: List.map (fun x ↦ (some x, true)) xs at hb
--         simp at hb
--     have nonsense : b2 <+: to_over (Append.append b4 b5)  := by
--       have h1 : b2 <+: to_over b4 := by
--         rw [b4_is]
--       simp [b45_ne_nil, to_over]
--       cases h : Append.append b4 b5
--       · apply (b45_ne_nil h).elim
--       rename_i head tail
--       simp only
--       rw [← h]
--       change b2 <+: List.map (fun x ↦ (some x, true)) (b4 ++ b5)
--       rw [List.map_append]
--       refine List.prefix_of_append ?_
--       sorry


--     specialize g1_ih nonsense
--     simp [PartialGrid.length]
--     apply Nat.add_le_add g1_ih
--     apply g2_ih
--     --have hb6 : to_up b6 = up2 := (unique_g_pg_c g1 ha b4_is b9).1
--     sorry
--     sorry
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     rename_i a3 b3 bot3 mid3 up3 b4 bot4 mid4 up4
--     intro ha hb
--     have b3_ne_nil : b3 ≠ [] := by
--       intro hb3
--       rw [hb3] at g1
--       have H := PartialGrid.top_length_pos g1
--       simp at H
--     have b4_neq_nil : b4 ≠ [] := by
--       intro hb4
--       rw [hb4] at g2
--       have H := PartialGrid.top_length_pos g2
--       simp at H
--     have H : ∃ b5 b6, to_over b6 = b4 ∧ to_over b5 = b3 ∧ b1 = b5 ++ b6 := by
--       sorry
--     rcases H with ⟨b5, b6, b6_is, b5_is, H⟩
--     rcases splittable_vertically_of_gridn h1 b5 b6 H with ⟨b7, b8, b9, b10, gt, ⟨g_is⟩, ⟨len⟩⟩
--     specialize g1_ih b10 ha
--     rw [len]
--     sorry
--     -- specialize g1_ih b5_is
--     -- simp [PartialGrid.length]
--     -- apply Nat.add_le_add g1_ih
--     -- have hb7 : to_up b7 = up3 := by sorry
--     -- apply g2_ih _ hb7 b6_is
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry
def to_up_plain (a : List ℕ) : List (ℕ × Bool) := List.map (fun x => (x, false)) a.reverse

def to_over_plain (a : List ℕ) : List (ℕ × Bool) := List.map (fun x => (x, true)) a

theorem remove_up_is_plain : remove_ones (to_up i) = to_up_plain i := by
  induction i with
  | nil => rfl
  | cons head tail ih =>
    match tail with
    | [] =>
      simp [remove_ones, to_up_plain]
    | t1 :: t2 =>
      have H1 : (to_up (head :: t1 :: t2)) = (to_up (t1 :: t2)) ++ [(some head, false)] := by
        simp [to_up]
      rw [H1, remove_ones_append, ih]
      simp [to_up_plain, remove_ones]

theorem helper_pg_empty (h : PartialGrid a b c d e) : remove_ones a = [] → remove_ones b =  [] →
    h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i =>
      intro ha
      simp [remove_ones, to_up] at ha
    | adjacent i k h =>
      intro ha
      simp [remove_ones, to_up] at ha
    | separated i j h =>
      intro ha
      simp [remove_ones, to_up] at ha
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih => sorry
  | horizontal_append h g1 g2 g1_ih g2_ih => sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

theorem prefix_of_bottom (h : gridt i j k l) (h1 : PartialGrid a b mid d2 e2)
  (ha : a = to_up i) (hbj : remove_ones b <+: to_over_plain j) : remove_ones mid <+: to_over_plain l := by
  induction h1 generalizing i j k l with
  | single_gridt h => sorry
  | empty a b ha ha1 hb hb =>
    simp [remove_ones]
  | horizontal_append_one g1 g2 g1_ih g2_ih => sorry
  | horizontal_append h g1 g2 g1_ih g2_ih =>

    sorry -- this is immediate
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

theorem eq_remover_of_remove_ones_eq_to_over_plain (h : remove_ones b = to_over_plain j) : j = remover b := by
  induction b generalizing j with
  | nil =>
    simp [remove_ones, to_over_plain] at h
    simp [h, remover]
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [remove_ones] at h
      simp [remover]
      exact ih h
    | (some a, _) =>
      simp [remove_ones] at h
      simp [remover]
      match j with
      | [] => simp [to_over_plain] at h
      | j1 :: j2 =>
        simp [to_over_plain] at h
        unfold to_over_plain at ih
        specialize ih h.2
        aesop

theorem remove_ones_eq_to_over_plain_of_eq_remover (h  : j = remover b) (hb : is_true b) : remove_ones b = to_over_plain j := by
  induction b generalizing j with
  | nil =>
    simp [remove_ones, to_over_plain]
    sorry
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [remove_ones]
      simp [remover] at h
      apply ih h
      sorry
    | (some a, true) =>
      simp [remove_ones]
      simp [remover] at h
      match j with
      | [] => simp [to_over_plain] at h
      | j1 :: j2 =>
        simp [to_over_plain] at h
        unfold to_over_plain at ih
        specialize ih h.2
        rw [ih]
        simp [to_over_plain]
        aesop
        sorry
    | (some a, false) => sorry -- exfalso

theorem prefix_of_bottom_emf' (h : gridt i j k l) (h1 : PartialGrid a b mid [] e2)
  (ha : a = to_up i) (hbj : remove_ones b <+: to_over_plain j) : remove_ones mid <+: to_over_plain l := by
  rcases hbj with ⟨r, hr⟩
  match r with
  | [] =>
    have H := gridt_of_PartialGrid h1
    simp [gridt_option] at H
    have H1 := unicity_c h H
    rw [ha] at H1
    specialize H1 remover_up_rev.symm
    rw [List.append_nil] at hr
    have H2 := eq_remover_of_remove_ones_eq_to_over_plain hr
    specialize H1 H2
    have H : remove_ones mid = to_over_plain l := by
      apply remove_ones_eq_to_over_plain_of_eq_remover H1.2.1.symm
      exact h1.bottom_frontier_is_true
    rw [H]
  | r1 :: r2 =>
    sorry

theorem prefix_of_bottom' (h : gridt i j k l) (h1 : PartialGrid a b mid d2 e2)
  (ha : a = to_up i) (hbj : remove_ones b <+: to_over_plain j) : remove_ones mid <+: to_over_plain l := by
  induction h generalizing a b mid d2 e2 with
  | empty => sorry
  | top_bottom i => sorry
  | sides i => sorry
  | top_left i => sorry
  | adjacent i k h => sorry
  | separated i j h => sorry
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    have ha1 : a = to_up q ++ to_up m := by sorry
    rcases splittable_horizontally_of_pg h1 _ _ ha1 (by sorry) (by sorry)
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · specialize h1_ih i1 rfl hbj
      exact h2_ih i2 rfl h1_ih
    rcases baaad with ⟨_, _, _, _, _, _, ⟨mid_nil⟩, _⟩
    aesop
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    have H : to_over_plain (n * q) = to_over_plain n ++ to_over_plain q := by
      simp [to_over_plain]
      sorry
    rw [H] at hbj
    have H : ∃ b1 b2, b = b1 ++ b2 ∧
      remove_ones b1 = to_over_plain n ∧ remove_ones b2 = to_over_plain q := by sorry
    rcases H with ⟨b1, b2, b_is, b1_is, b2_is⟩
    rcases splittable_vertically_of_pg' h1 _ _ b_is (by sorry) (by sorry)
      with ⟨d4, e4, d5, e3, mid4, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · specialize h1_ih i1 ha (by rw [b1_is])
      match d4 with
      | [] => sorry
      | d41 :: d42 =>
        specialize h2_ih i2


    sorry

theorem pg_sm_g_eq1 (h : PartialGrid a b c d e) (h1 : gridt a1 b1 f g)
    : remove_ones a = to_up_plain a1 → remove_ones b = to_over_plain b1 → h.length ≤ h1.length := by
  induction h1 generalizing a b c d e with
  | empty => sorry
  | top_bottom i => sorry
  | sides i => sorry
  | top_left i => sorry
  | adjacent i k h => sorry
  | separated i j h => sorry
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i i j k l m n o
    intro a_is b_is
    have H : a =  to_up m ++ to_up i := by sorry
    rcases splittable_horizontally_of_pg h _ _ H (by sorry) (by sorry)
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl]
      have hi1 : i1.length ≤ h1.length := by
        exact h1_ih i1 (remove_up_is_plain) b_is
      have hi2 : i2.length ≤ h2.length := by
        have H : remove_ones mid <+: to_over_plain l := prefix_of_bottom h1 i1 rfl b_is -- the interesting sorry
        rcases H with ⟨r, hr⟩
        have i3 := PartialGrid.extend_side_w_len i2 (List.map (fun x => (some x.1, x.2)) r)
          (by sorry) (by sorry)
        specialize h2_ih i3.1 (remove_up_is_plain)
        rw [← hr] at h2_ih
        simp [remove_ones] at h2_ih
        rw [i3.2.1]
        apply h2_ih
        sorry -- this is stupid
      simp [gridt.length]
      omega
    rcases baaad with ⟨ db, c1, drest, i1, ⟨long⟩, ⟨db_is⟩, ⟨c_nil⟩, ⟨len⟩⟩
    specialize h1_ih i1 (remove_up_is_plain) b_is
    simp [gridt.length]
    omega
  | horizontal h1 h2 h1_ih h2_ih => sorry
