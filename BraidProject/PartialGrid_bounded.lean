import BraidProject.PartialGrid_prefix_suffix

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

-- theorem same_type_same_length_pg (g1 : PartialGrid a b c d e) (g2 : PartialGrid a1 b1 c1 d1 e1) :
--     a = a1 → b = b1 → c = c1 → d = d1 → e = e1 → g1.length = g2.length := by
--   induction g1 generalizing a1 b1 c1 d1 e1 with
--   | single_gridt h =>
--     rename_i f g l m
--     intro a_is b_is c_is d_is e_is
--     cases h with
--     | empty =>
--       simp [PartialGrid.length]
--       simp [to_up] at a_is
--       simp [to_over] at b_is
--       exact (all_ones_length_pg _ a_is.symm b_is.symm).symm
--     | top_bottom i =>
--       simp [PartialGrid.length]
--       simp [to_up] at a_is
--       simp [to_over] at b_is
--       exact (top_bottom_length_pg _ a_is.symm b_is.symm).symm
--     | sides i =>
--       simp [PartialGrid.length]
--       simp [to_up] at a_is
--       simp [to_over] at b_is
--       exact (side_side_length_pg _ a_is.symm b_is.symm).symm
--     | top_left i =>
--       simp [PartialGrid.length]
--       simp [to_up] at a_is
--       simp [to_over] at b_is
--       have rme : remove_ones (c1 ++ d1 ++ e1) = [] := by
--         rw [← c_is, ← d_is, ← e_is]
--         simp [remove_ones]
--       exact (top_left_length_pg _ a_is.symm b_is.symm rme).symm
--     | adjacent i j h =>
--       simp [PartialGrid.length]
--       simp [to_up] at a_is
--       simp [to_over] at b_is
--       have rme : remove_ones (c1 ++ d1 ++ e1) =
--         [(j, true), (i, true), (j, false), (i, false)] := by
--         rw [← c_is, ← d_is, ← e_is]
--         simp [remove_ones]
--       exact (adjacent_length_pg _ a_is.symm b_is.symm rme h).symm
--     | separated i j h =>
--       simp [PartialGrid.length]
--       simp [to_up] at a_is
--       simp [to_over] at b_is
--       have rme : remove_ones (c1 ++ d1 ++ e1) = [(j, true), (i, false)] := by
--         rw [← c_is, ← d_is, ← e_is]
--         simp [remove_ones]
--       exact (separated_length_pg _ a_is.symm b_is.symm rme (or_dist_iff.mpr h)).symm
--   | empty a b ha ha1 hb hb1 =>
--     intro a_is b_is c_is d_is e_is
--     simp [PartialGrid.length]
--     symm
--     rw [a_is, b_is] at d_is
--     sorry --exact empty_helper _ c_is d_is e_is
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     rename_i a3 b3 bot3 up3 b4 bot4 mid4 up4 g3
--     intro a_is b_is c_is d_is e_is
--     have split_it := splittable_vertically_of_pg' g2 _ _ b_is.symm (PartialGrid.top_length_pos g1) (PartialGrid.top_length_pos g3)
--     rcases split_it with ⟨mid, c2, d2, c3, d3, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
--     · rw [len]
--       specialize g1_ih i1 a_is rfl
--       specialize g2_ih i2
--       rw [← c_is, ← d_is] at long
--       have H := unique_split_horiz g1 g3 i1 i2 (PartialGrid.left_length_pos g3)
--         (PartialGrid.left_length_pos i2) a_is rfl rfl e_is (by simp [long])
--       specialize g1_ih H.2.2.2.2 H.2.1 H.1
--       specialize g2_ih H.1 rfl H.2.2.1 H.2.2.2.1 e_is
--       simp [g1_ih, g2_ih, PartialGrid.length]
--     rcases b with ⟨d5, d6, h5, ⟨len⟩, ⟨e1_nil⟩, ⟨d_is⟩, ⟨b4_is⟩⟩
--     rw [e1_nil] at e_is
--     sorry
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     rename_i a3 b3 bot3 mid3 up3 b4 bot4 mid4 up4 g3
--     intro a_is b_is c_is d_is e_is
--     have split_it := splittable_vertically_of_pg' g2 _ _ b_is.symm (PartialGrid.top_length_pos g1) (PartialGrid.top_length_pos g3)
--     rcases split_it with ⟨mid, c2, d2, c3, d3, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
--     · rw [len]
--       specialize g1_ih i1 a_is rfl
--       specialize g2_ih i2
--       rw [← c_is, ← d_is, ← List.append_assoc, ← List.append_assoc] at long
--       have H := unique_split_horiz g1 g3 i1 i2 (PartialGrid.left_length_pos g3)
--         (PartialGrid.left_length_pos i2) a_is rfl rfl e_is long
--       specialize g1_ih H.2.2.2.2 H.2.1 H.1
--       specialize g2_ih H.1 rfl H.2.2.1 H.2.2.2.1 e_is
--       simp [g1_ih, g2_ih, PartialGrid.length]
--     rw [PartialGrid.length]
--     rcases b with ⟨k1, k2, j1,⟨len⟩, ⟨e1_nil⟩, ⟨d1_is⟩, ⟨b4_is⟩⟩
--     rw [len]
--     specialize g1_ih j1 a_is rfl c_is
--     sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry

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
