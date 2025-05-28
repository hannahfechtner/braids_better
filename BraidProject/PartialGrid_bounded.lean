import BraidProject.PartialGrid_split

noncomputable def foo (h : PartialGrid a b c (d1 ++ d2 ++ []) e) :
    {h1 : PartialGrid a b c (d1 ++ d2) e // h.length = h1.length} := by
  revert h
  generalize h2 : d1 ++ d2 ++ [] = d'
  rw [List.append_nil] at h2
  subst h2
  intro h
  use h

noncomputable def foo'' (h' : d1 = d2) (h1 : PartialGrid a b c d1 e) :
    {h2 : PartialGrid a b c d2 e // h1.length = h2.length} := by
  revert h1
  subst h'
  intro h
  use h

noncomputable def foo''' (h : PartialGrid a b c (d1 ++ d2 ++ []) e) :
    {h1 : PartialGrid a b c (d1 ++ d2) e // h.length = h1.length} := foo'' (by simp) _

noncomputable def foo' (h : PartialGrid a b c ([] ++ d) e) :
    (h1 : PartialGrid a b c d e) × PLift (h.length = h1.length) := by
  use h
  exact ⟨rfl⟩

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

theorem remove_ones_eq_to_over_plain_of_eq_remover (h  : j = remover b) (hb : is_true b) :
    remove_ones b = to_over_plain j := by
  induction b generalizing j with
  | nil =>
    simp [remover] at h
    simp [remove_ones, to_over_plain]
    exact h
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [remove_ones]
      simp [remover] at h
      apply ih h
      exact (is_true_split hb).2
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
        exact (is_true_split hb).2
    | (some a, false) =>
      specialize hb (some a, false) ⟨by simp⟩
      simp at hb
      exact hb.1.elim

theorem to_over_plain_remover_eq_remove_ones(h : is_true b) : to_over_plain (remover b) = remove_ones b := by
  induction b with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [to_over_plain, remove_ones, ← ih (is_true_split h).2, remover]
    | (some a, true) =>
      simp [to_over_plain, remove_ones, ← ih (is_true_split h).2, remover]
    | (some a, false) =>
      have H := (is_true_split h).1 (some a, false) ⟨by simp⟩
      simp at H
      exact H.1.elim

theorem to_up_plain_remover_rev_eq_remove_ones (h : is_false a) : to_up_plain (remover a.reverse) = remove_ones a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [to_up_plain, remove_ones, ← ih (is_false_split h).2, remover_append, remover]
    | (some a, true) =>
      have H := (is_false_split h).1 (some a, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    | (some a, false) =>
      simp [to_up_plain, remove_ones, ← ih (is_false_split h).2, remover_append, remover]

theorem to_up_plain_inj (h : to_up_plain a = to_up_plain b) : a = b := by
  simp [to_up_plain] at h
  exact (List.map_inj_right (by simp)).mp h

theorem to_over_plain_inj (h : to_over_plain a = to_over_plain b) : a = b := by
  simp [to_over_plain] at h
  exact (List.map_inj_right (by simp)).mp h

theorem unique_g_pg_c
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_up a1 = a2)
    (b4_is : to_over b4 = b2)
    (b9 : gridt a1 b4 b6 b7) : to_up_plain b6 = remove_ones up2 ∧ to_over_plain b7 = remove_ones bot2 := by
    have H := gridt_of_PartialGrid g1
    unfold gridt_option at H
    have H3 := unicity_c b9 H
    rw [← ha, ← b4_is] at H3
    specialize H3 remover_up_rev.symm remover_over.symm
    rw [← H3.1.1, ← H3.2.1]
    constructor
    · apply to_up_plain_remover_rev_eq_remove_ones
      exact g1.right_frontier_is_false
    apply to_over_plain_remover_eq_remove_ones
    exact g1.bottom_frontier_is_true

theorem unique_g_pg_c_ones_okay
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_up_plain a1 = remove_ones a2)
    (b4_is : to_over_plain b4 = remove_ones b2)
    (b9 : gridt a1 b4 b6 b7) : to_up_plain b6 = remove_ones up2 ∧ to_over_plain b7 = remove_ones bot2 := by
    have ha1 : a1 = remover a2.reverse := by
      rw [← to_up_plain_remover_rev_eq_remove_ones] at ha
      · exact to_up_plain_inj ha
      exact g1.left_frontier_is_false
    have hb4 : b4 = remover b2 := by
      rw [← to_over_plain_remover_eq_remove_ones] at b4_is
      · exact to_over_plain_inj b4_is
      exact g1.top_frontier_is_true
    have H := gridt_of_PartialGrid g1
    unfold gridt_option at H
    have H3 := unicity_c b9 H
    specialize H3 ha1 hb4
    rw [← H3.1.1, ← H3.2.1]
    constructor
    · apply to_up_plain_remover_rev_eq_remove_ones
      exact g1.right_frontier_is_false
    apply to_over_plain_remover_eq_remove_ones
    exact g1.bottom_frontier_is_true

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

-- theorem grid_pg_suffix_prefix (h : PartialGrid a b c d e) (h1 : gridt a1 b1 e1 c1)
--     (ha : a = to_up a1) (hb : b = to_over b1) : remover c <+: c1 ∧ remover e.reverse <+: e1 := by
--   induction h generalizing a1 b1 e1 c1 with
--   | single_gridt h =>
--     cases h with
--     | empty =>
--       apply to_up_inj at ha
--       apply to_over_inj at hb
--       have h1 := all_ones_t h1 ha.symm hb.symm
--       aesop
--     | top_bottom i =>
--       apply to_up_inj at ha
--       apply to_over_inj at hb
--       have h1 := i_top_bottom_t h1 _ ha.symm hb.symm
--       aesop
--     | sides i =>
--       apply to_up_inj at ha
--       apply to_over_inj at hb
--       have h1 := i_side_side_t h1 _ ha.symm hb.symm
--       aesop
--     | top_left i =>
--       apply to_up_inj at ha
--       apply to_over_inj at hb
--       have h1 := i_top_left_t h1 _ ha.symm hb.symm
--       aesop
--     | adjacent i k h =>
--       apply to_up_inj at ha
--       apply to_over_inj at hb
--       have h1 := i_adjacent_t h1 _ _ ha.symm hb.symm h
--       change _ = [i, k] ∧ _ = [k, i] at h1
--       simp [h1]
--       aesop
--     | separated i j h =>
--       apply to_up_inj at ha
--       apply to_over_inj at hb
--       have h1 := helpier_ij_t h1 _ _ h ha.symm hb.symm
--       change _ = [i] ∧ _ = [j] at h1
--       aesop
--   | empty a b ha ha1 hb hb =>
--     simp [remover]
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
--     have H : ∃ b4 b5, b1 = b4 * b5 ∧ b4.length > 0 ∧ b5.length > 0 := by sorry
--     rcases H with ⟨b4, b5, b1_is, b4_len, b5_len⟩
--     have splitty := splittable_vertically_of_gridt h1 _ _ b1_is
--     rcases splitty with ⟨rest, c1, c2, g3, g4, ⟨c_is⟩, ⟨len1⟩⟩
--     have hb : b2 = to_over b4 := by sorry
--     have hb1 : b3 = to_over b5 := by sorry
--     have hup2 : up2 = to_up rest := by sorry -- from g1 and g3
--     have hbot2 : bot2 = to_over c1 := by sorry -- from g1 and g3
--     specialize g1_ih g3 ha hb
--     specialize g2_ih g4 hup2 hb1
--     simp [g2_ih.2, remover_append, hbot2]
--     change _ <+: (_ ++ _)
--     refine (List.prefix_append_right_inj c1).mpr ?_
--     exact g2_ih.1
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
--     have H : ∃ b4 b5, b1 = b4 * b5 ∧ b4.length > 0 ∧ b5.length > 0 := by sorry
--     rcases H with ⟨b4, b5, b1_is, b4_len, b5_len⟩
--     have splitty := splittable_vertically_of_gridt h1 _ _ b1_is
--     rcases splitty with ⟨rest, c1, c2, g3, g4, ⟨c_is⟩, ⟨len1⟩⟩
--     have hb : b2 = to_over b4 := by sorry
--     have hb1 : b3 = to_over b5 := by sorry
--     specialize g1_ih g3 ha hb
--     constructor
--     · exact List.prefix_of_append g1_ih.1
--     rcases g1_ih.2 with ⟨rest2, hr⟩
--     have H := splittable_horizontally_of_gridt g4 _ _ hr.symm
--     rcases H with ⟨u, c1, c2, g5, g6, e1_is⟩
--     specialize g2_ih g4



--     sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry

theorem helper_pg_empty (h : PartialGrid a b c d e) : remove_ones a = [] → remove_ones b =  [] →
    remove_ones c = [] ∧ remove_ones e = [] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length, remove_ones]
    | top_bottom i => simp [PartialGrid.length, remove_ones]
    | sides i => simp [PartialGrid.length, remove_ones]
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
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i f g h i j k l m
    intro f_is gj_is
    rw [remove_ones_append] at gj_is
    apply List.append_eq_nil_iff.mp at gj_is
    specialize g1_ih f_is gj_is.1
    specialize g2_ih g1_ih.2.1 gj_is.2
    rw [remove_ones_append, PartialGrid.length]
    aesop
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i f g i j k l m n o
    intro f_is gl_is
    rw [remove_ones_append] at gl_is
    apply List.append_eq_nil_iff.mp at gl_is
    specialize g1_ih f_is gl_is.1
    specialize g2_ih g1_ih.2.1 gl_is.2
    rw [PartialGrid.length]
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i f g h i j k l m
    intro jf_is g_is
    rw [remove_ones_append] at jf_is
    apply List.append_eq_nil_iff.mp at jf_is
    specialize g1_ih jf_is.2 g_is
    specialize g2_ih jf_is.1 g1_ih.1
    rw [remove_ones_append, PartialGrid.length]
    aesop
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i f g i j k l m n o
    intro lf_is g_is
    rw [remove_ones_append] at lf_is
    apply List.append_eq_nil_iff.mp at lf_is
    specialize g1_ih lf_is.2 g_is
    specialize g2_ih lf_is.1 g1_ih.1
    rw [PartialGrid.length]
    aesop

theorem empty_rm_pg_len (h : PartialGrid a b c d e) : remove_ones a = [] → remove_ones b =  [] →
    h.length = 0 := by
  have H := helper_pg_empty h
  aesop

theorem to_up_len : (to_up a).length > 0 := by
  match a with
  | [] => simp [to_up]
  | a1 :: a2 => simp [to_up]

theorem to_over_len : (to_over b).length > 0 := by
  match b with
  | [] => simp [to_over]
  | b1 :: b2 => simp [to_over]

theorem to_up_plain_append : to_up_plain (a ++ b) = to_up_plain b ++ to_up_plain a := by simp [to_up_plain]
theorem to_over_plain_append : to_over_plain (a ++ b) = to_over_plain a ++ to_over_plain b := by simp [to_over_plain]
theorem remove_ones_len(a : List (Option α × Bool))  : (remove_ones a).length ≤ a.length := by
  induction a with
  | nil => simp [remove_ones]
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [remove_ones] at ih
      simp [remove_ones, ih]
      omega
    | (some a, true) =>
      simp [remove_ones] at ih
      simp [remove_ones, ih]
    | (some a, false) =>
      simp [remove_ones] at ih
      simp [remove_ones, ih]

theorem remove_ones_eq_append (h : remove_ones a = b ++ c) (hb : b.length > 0) (hc : c.length > 0):
    ∃ a1 a2, a=a1++a2 ∧ remove_ones a1 = b ∧ remove_ones a2 = c := by
  induction a generalizing b c with
  | nil =>
    simp [remove_ones] at h
    aesop
  | cons head tail ih =>
    match head with
    | (none, b) =>
      simp [remove_ones] at h
      specialize ih h hb hc
      rcases ih with ⟨a1, a2, a_is, b_is, c_is⟩
      use (none, b) :: a1, a2
      simp_all [remove_ones]
    | (some d, e) =>
      match b with
      | [] => aesop
      | b1 :: b2 =>
        simp [remove_ones] at h
        match b2 with
        | [] =>
          use [(some d, e)], tail
          simp_all [remove_ones]
        | b21 :: b22 =>
          specialize ih h.2 (by simp) hc
          rcases ih with ⟨a1, a2, a_is, b_is, c_is⟩
          use (some d, e) :: a1, a2
          simp_all [remove_ones]

theorem remove_ones_eq_to_up_plain_prod (h : remove_ones a = to_up_plain (m ++ q)) :
   m = [] ∨ q = [] ∨ ∃ a1 a2, a1.length > 0 ∧ a2.length > 0 ∧
        a = a1 ++ a2 ∧ remove_ones a1 = to_up_plain q ∧ remove_ones a2 = to_up_plain m  := by
  induction m generalizing a q with
  | nil => exact Or.inl rfl
  | cons m1 m2 ih =>
    right
    match q with
    | [] => exact Or.inl rfl
    | q1 :: q2 =>
      right
      rw [to_up_plain_append] at h
      rcases remove_ones_eq_append h (by simp [to_up_plain]) (by simp [to_up_plain]) with
        ⟨a1, a2, a_is, a1s, a2s⟩
      use a1, a2
      have a1l := remove_ones_len a1
      have a2l := remove_ones_len a2
      have a1le := congr_arg List.length a1s
      have a2le := congr_arg List.length a2s
      simp [to_up_plain] at a1le
      simp [to_up_plain] at a2le
      have a1_len : a1.length > 0 := by
        omega
      have a2_len : a2.length > 0 := by omega
      aesop

theorem List.suffix_of_append {a b c : List α} (h : a <:+ b ++ c) : a <:+ c ∨ ∃ a1, a1.length > 0 ∧
     a = a1 ++ c ∧ a1 <:+ b := by
  rcases h with ⟨r, hr⟩
  rcases List.append_eq_append_iff.mp hr with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · match tm with
    | [] => aesop
    | t1 :: t2 =>
      right
      use t1 :: t2
      constructor
      · simp
      constructor
      · exact s2
      simp [s1]
  match fm with
  | [] => aesop
  | f1 :: f2 =>
    left
    rw [s2]
    exact suffix_append ([f1] ++ f2) a

theorem helper_bajillion (ha : remove_ones a <:+ to_up_plain q ++ to_up_plain (m1 :: m2)) :
    remove_ones a <:+ to_up_plain (m1 :: m2) ∨
    ∃ a1 a2, a1.length > 0 ∧ a = a1 ++ a2 ∧ remove_ones a2 = to_up_plain (m1 :: m2) ∧ remove_ones a1 <:+ to_up_plain q := by
  rcases List.suffix_of_append ha with one | two
  · left
    exact one
  rcases two with ⟨a1, a1_len, a_is, a1_suff⟩
  right
  have H := remove_ones_eq_append a_is a1_len (by simp [to_up_plain])
  rcases H with ⟨a3, a4, a_is, a3a1, m4⟩
  use a3, a4
  constructor
  · have H := remove_ones_len a3
    rw [a3a1] at H
    omega
  constructor
  · assumption
  constructor
  · exact m4
  rw [a3a1]
  assumption

theorem frontier_options_from_vertical (h1 : PartialGrid a b mid d2 e2)
    (i1 : PartialGrid a2 b mid4 e5 d5) (i2 : PartialGrid a1 mid4 mid d4 e4)
    (hf : d4 ++ e4 ++ e5 ++ d5 = d2 ++ e2) :
    (d2 = d4 ++ e4 ++ e5 ∧ d5 = e2) ∨ (d2 = d4 ∧ e5 = [] ∧ e2 = e4 ++ d5) := by
  rcases middle_frontier_nil_or_caps i1 with ⟨⟨e5_nil⟩⟩ | ⟨fronte5, mide5, caboosee5, ⟨spece5⟩⟩
  · right
    rw [e5_nil, List.append_nil] at hf
    rcases middle_frontier_nil_or_caps h1 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, middled2, caboosed2, ⟨specd2⟩⟩
    · rw [d2_nil, List.nil_append] at hf
      rcases middle_frontier_nil_or_caps i2 with ⟨⟨d4_nil⟩⟩ | ⟨frontd4, middled4, caboosed4, ⟨specd4⟩⟩
      · rw [d4_nil, List.nil_append] at hf
        aesop
      rw [specd4] at hf
      have H : is_false e2 := h1.right_frontier_is_false
      rw [← hf] at H
      specialize H (caboosed4, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    rw [specd2] at hf
    have H : is_false (e4 ++ d5) := by
        apply is_false_of_false_false
        · exact i2.right_frontier_is_false
        exact i1.right_frontier_is_false
    rcases middle_frontier_nil_or_caps i2 with ⟨⟨d4_nil⟩⟩ | ⟨frontd4, middled4, caboosed4, ⟨specd4⟩⟩
    · rw [d4_nil, List.nil_append] at hf
      rw [hf] at H
      specialize H (caboosed2, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    rw [specd4] at hf
    simp at hf
    have to_split : (middled4 ++ [(caboosed4, true)]) ++ (e4 ++ d5) =
        (middled2 ++ [(caboosed2, true)]) ++ e2 := by
      simp [hf.2]
    rcases List.append_eq_append_iff.mp to_split with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
    · cases tm using List.reverseRecOn with
      | nil => aesop
      | append_singleton t1 t2 =>
        exfalso
        rw [← List.append_assoc] at s1
        have t2_is : t2 = (caboosed2, true) := by
          apply congr_arg List.getLast? at s1
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
          exact s1.symm
        rw [s2, t2_is] at H
        specialize H (caboosed2, true) ⟨by simp⟩
        simp at H
        exact H.1.elim
    cases fm using List.reverseRecOn with
    | nil => aesop
    | append_singleton f1 f2 =>
      exfalso
      have H : is_false e2 := h1.right_frontier_is_false
      rw [s2] at H
      have f2_is : f2 = (caboosed4, true) := by
        apply congr_arg List.getLast? at s1
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
        exact s1.symm
      rw [f2_is] at H
      specialize H (caboosed4, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
  left
  rw [spece5] at hf
  rcases List.append_eq_append_iff.mp hf with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · cases tm using List.reverseRecOn with
    | nil => aesop
    | append_singleton t1 t2 =>
      exfalso
      rcases middle_frontier_nil_or_caps h1 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, midd2, caboosed2, ⟨specd2⟩⟩
      · simp [d2_nil] at s1
      rw [specd2] at s1
      have H : t2 = (caboosed2, true) := by
        apply congr_arg List.getLast? at s1
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
        exact s1.symm
      have H1 : is_false d5 := i1.right_frontier_is_false
      rw [s2, H] at H1
      specialize H1 (caboosed2, true) ⟨by simp⟩
      simp at H1
      exact H1.1.elim
  cases fm using List.reverseRecOn with
  | nil => aesop
  | append_singleton f1 f2 =>
    have H : f2 = (caboosee5, true) := by
      apply congr_arg List.getLast? at s1
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
      exact s1.symm
    have H1 : is_false e2 := by exact h1.right_frontier_is_false
    rw [s2, H] at H1
    specialize H1 (caboosee5, true) ⟨by simp⟩
    simp at H1
    exact H1.1.elim

theorem partial_grid_rm_empty_helper (h : PartialGrid a b c d e) : remove_ones a = [] → remove_ones b = [] →
    (remove_ones c = [] ∧ remove_ones d = [] ∧ remove_ones e = []) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all
    | sides i => simp_all
    | top_left i => simp_all [to_up, remove_ones]
    | adjacent i k h => simp_all [to_up, remove_ones]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih => simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all
  | vertical_append g1 g2 h g1_ih g2_ih => simp_all

theorem partial_grid_rm_top_helper (h : PartialGrid a b c d e) : remove_ones a = [] → remove_ones b = [(i, true)] →
    (remove_ones c = [(i, true)] ∧ remove_ones d = [] ∧ remove_ones e = []) ∨
    (remove_ones c = [] ∧ remove_ones d = [(i, true)] ∧ remove_ones e = []) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all
    | sides i => simp_all
    | top_left i => simp_all [to_up, remove_ones]
    | adjacent i k h => simp_all [to_up, remove_ones]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    intro j_is kn_is
    rw [remove_ones_append] at kn_is
    rcases List.append_eq_singleton_iff.mp kn_is with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_empty_helper g1 j_is k_is
      simp_all
    simp_all only [remove_ones_nil, true_and, List.ne_cons_self, false_and, and_false, or_false,
      forall_const, IsEmpty.forall_iff, imp_self, List.append_nil, remove_ones_append,
      List.cons_append, List.nil_append, List.cons.injEq]
    have H := partial_grid_rm_empty_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    intro j_is ko_is
    rw [remove_ones_append] at ko_is
    rcases List.append_eq_singleton_iff.mp ko_is with
      ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_empty_helper g1 j_is k_is
      simp_all
      rcases g2_ih with h1 | h2
      · simp_all
      simp_all
    have hn : remove_ones n = [] := by aesop
    have H := partial_grid_rm_empty_helper g2 hn o_is
    simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    intro oj_is k_is
    rw [remove_ones_append] at oj_is
    simp at oj_is
    specialize g1_ih oj_is.2 k_is
    rcases g1_ih with h1 | h2
    · specialize g2_ih oj_is.1 h1.1
      rcases g2_ih with h3 | h4
      · simp_all
      simp_all
    have H := partial_grid_rm_empty_helper g2 oj_is.1 h2.1
    simp_all

theorem partial_grid_rm_side_helper (h : PartialGrid a b c d e)
    (h1 : remove_ones a = [(i, false)]) (h2 : remove_ones b = []) :
    (remove_ones c = [] ∧ remove_ones d = [(i, false)] ∧ remove_ones e = []) ∨
    (remove_ones c = [] ∧ remove_ones d = [] ∧ remove_ones e = [(i, false)]) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp_all [remove_ones]
    | top_bottom i => simp_all [remove_ones]
    | sides i => simp_all [remove_ones]
    | top_left i => simp_all [to_up, remove_ones]
    | adjacent i k h => simp_all [to_up, remove_ones]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    simp [remove_ones_append] at h2
    simp_all
    rcases g1_ih with h3 | h4
    · simp_all
      have H := partial_grid_rm_empty_helper g2 h3.2.2 h2.2
      simp_all
    simp_all
    rcases g2_ih with h5 | h6
    · simp_all
    simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · simp_all
      have H := partial_grid_rm_empty_helper g2 n_is g1_ih.1
      simp_all
    have H := partial_grid_rm_empty_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · simp_all
      have l_is : remove_ones l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 o_is l_is
      simp_all
    have H := partial_grid_rm_empty_helper g1 j_is h2
    simp_all
    rcases g2_ih with h3 | h4
    · simp_all
    simp_all

theorem partial_grid_rm_top_left_helper (h : PartialGrid a b c d e) (h1 : remove_ones a = [(i, false)])
  (h2 : remove_ones b = [(i, true)]) : (remove_ones c = [] ∧ remove_ones d = [] ∧ remove_ones e = []) ∨
  (remove_ones c = [] ∧ remove_ones d = [(i, false), (i, true)] ∧ remove_ones e = []) := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [remove_ones]
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_empty_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    have n_is : remove_ones n = [] := by aesop
    have H := partial_grid_rm_empty_helper g2 n_is o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : remove_ones l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 n_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : remove_ones l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 o_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
    rcases H with h3 | h4
    · aesop
    have H := partial_grid_rm_side_helper g2 o_is h4.1
    aesop

theorem partial_grid_rm_adjacent_helper (h : PartialGrid a b c d e) (h1 : remove_ones a = [(i, false)])
  (h2 : remove_ones b = [(j, true)]) (hij : i.dist j = 1): (remove_ones c = [] ∧ remove_ones d = [(i, false), (j, true)] ∧ remove_ones e = []) ∨
  (remove_ones c = [] ∧ remove_ones d = [(j, true), (i, true), (j, false), (i, false)] ∧ remove_ones e = [])  ∨
  (remove_ones c = [(j, true), (i, true)] ∧ remove_ones d = [(j, false), (i, false)] ∧ remove_ones e = []) ∨ := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [remove_ones]
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_empty_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    have n_is : remove_ones n = [] := by aesop
    have H := partial_grid_rm_empty_helper g2 n_is o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : remove_ones l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 n_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : remove_ones l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 o_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
    rcases H with h3 | h4
    · aesop
    have H := partial_grid_rm_side_helper g2 o_is h4.1
    aesop

theorem suffix_of_singleton (h : l <:+ [a]) : l = [] ∨ l = [a] := by
  rcases h with ⟨r, hr⟩
  match r with
  | [] => aesop
  | r1 :: r2 => aesop

theorem prefix_of_singleton (h : l <+: [a]) : l = [] ∨ l = [a] := by
  rcases h with ⟨r, hr⟩
  match r with
  | [] => aesop
  | r1 :: r2 =>
    apply congr_arg List.length at hr
    simp at hr
    have H : l.length = 0 := by omega
    aesop

--theorem foo (ha : is_false a) (h : remover a = to_over_plain (m ++ q)) : False := by sorry
theorem same_time (h : gridt i j k l) (h1 : PartialGrid a b mid d2 e2)
  : (remove_ones a = to_up_plain i → remove_ones b <+: to_over_plain j → remove_ones mid <+: to_over_plain l)
  ∧ (remove_ones b = to_over_plain j → remove_ones a <:+ to_up_plain i → remove_ones e2 <:+ to_up_plain k) := by
  induction h generalizing a b mid d2 e2 with
  | empty =>
    constructor
    · intro a_is b_is
      change _ <+: [] at b_is
      simp at b_is
      have H := partial_grid_rm_empty_helper h1 a_is b_is
      aesop
    intro b_is a_is
    change _ <:+ [] at a_is
    simp at a_is
    have H := partial_grid_rm_empty_helper h1 a_is b_is
    aesop
  | top_bottom i =>
    constructor
    · intro a_is b_is
      rcases prefix_of_singleton b_is with h3 | h4
      · have H2 := partial_grid_rm_empty_helper h1 a_is h3
        aesop
      have H := partial_grid_rm_top_helper h1 a_is h4
      aesop
    intro b_is a_is
    change _ <:+ [] at a_is
    simp at a_is
    have H := partial_grid_rm_top_helper h1 a_is b_is
    aesop
  | sides i =>
    constructor
    · intro a_is b_is
      change _ <+: [] at b_is
      simp at b_is
      have H := partial_grid_rm_side_helper h1 a_is b_is
      aesop
    intro b_is a_is
    rcases suffix_of_singleton a_is with h3 | h4
    · have H := partial_grid_rm_empty_helper h1 h3 b_is
      aesop
    have H := partial_grid_rm_side_helper h1 h4 b_is
    aesop
  | top_left i =>
    constructor
    · intro a_is b_is
      rcases prefix_of_singleton b_is with h3 | h4
      · have H := partial_grid_rm_side_helper h1 a_is h3
        aesop
      have H := partial_grid_rm_top_left_helper h1 a_is h4
      aesop
    intro b_is a_is
    rcases suffix_of_singleton a_is with h3 | h4
    · have H := partial_grid_rm_top_helper h1 h3 b_is
      aesop
    have H := partial_grid_rm_top_left_helper h1 h4 b_is
    aesop
  | adjacent i k h =>
    constructor
    · intro a_is b_is
      sorry
    intro b_is a_is
    sorry
  | separated i j h => sorry
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    constructor
    · intro ha hb
      have ha1 : m = [] ∨ q = [] ∨ ∃ a1 a2, a1.length > 0 ∧ a2.length > 0 ∧
          a = a1 ++ a2 ∧ remove_ones a1 = to_up_plain q ∧ remove_ones a2 = to_up_plain m :=
        remove_ones_eq_to_up_plain_prod ha
      rcases ha1 with m_nil | q_nil | ⟨a1, a2, a1_len, a2_len, ha1, a1q, a2m⟩
      · have H : remove_ones a = to_up_plain q := by
          rw [m_nil] at ha
          convert ha
        have on : o = [] ∧ p = n := word_side_side_t _ _ _ t m_nil
        specialize h2_ih h1
        have new_h2_ih := h2_ih.1 H
        rw [on.2] at new_h2_ih
        exact new_h2_ih hb
      · have H : remove_ones a = to_up_plain m := by
          rw [q_nil] at ha
          convert ha
          simp; rfl
        have rs : r = [] ∧ s = p := word_side_side_t _ _ _ h2 q_nil
        specialize h1_ih h1
        have new_h2_ih := h1_ih.1 H hb
        rw [rs.2]
        exact new_h2_ih
      rcases splittable_horizontally_of_pg h1 _ _ ha1 a2_len a1_len
        with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
      · specialize h1_ih i1
        have new_h1_ih := h1_ih.1 a2m hb
        exact (h2_ih i2).1 a1q new_h1_ih
      rcases baaad with ⟨_, _, _, _, _, _, ⟨mid_nil⟩, _⟩
      aesop
    intro hb ha
    have ha1 : remove_ones a <:+ to_up_plain q ++ to_up_plain m := by
      have H : to_up_plain q ++ to_up_plain m = to_up_plain (m.toList ++ q.toList) := by
        simp [to_up_plain_append]
        congr
      rw [H]
      convert ha
    have H : to_up_plain (o * r) = to_up_plain r ++ to_up_plain o := by
      have H1 : to_up_plain (o.toList ++ r.toList) = to_up_plain r ++ to_up_plain o := by
        simp [to_up_plain]
        rfl
      rw [← H1]
      congr
    rw [H]
    match m with
    | [] =>
      nth_rewrite 2 [to_up_plain] at ha1
      simp at ha1
      specialize h2_ih h1
      have on : o = [] ∧ p = n := word_side_side_t _ _ _ t rfl
      rw [← on.2] at hb
      have h_new := h2_ih.2 hb ha1
      rw [on.1]
      nth_rewrite 2 [to_up_plain]
      simp
      exact h_new
    | m1 :: m2 =>
      have H : remove_ones a <:+ to_up_plain (m1 :: m2) ∨
        ∃ a1 a2, a1.length > 0 ∧ a = a1 ++ a2 ∧
        remove_ones a2 = to_up_plain  (m1 :: m2) ∧ remove_ones a1 <:+ to_up_plain q := by
        exact helper_bajillion ha1
      rcases H with ha1 | ⟨a1, a2, a1_len, a1_is, ha11⟩
      · have H2 : remove_ones e2 <:+ to_up_plain o := (h1_ih h1).2 hb ha1
        exact suffix_of_append H2
      have a2_len : a2.length > 0 := by
        have H := remove_ones_len a2
        rw [ha11.1] at H
        simp [to_up_plain] at H
        omega
      rcases splittable_horizontally_of_pg h1 _ _ a1_is a2_len a1_len
          with ⟨mid4, d4, e4, e5, d5, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
      · have H : (d2 = d4 ++ e4 ++ e5 ∧ d5 = e2) ∨ (d2 = d4 ∧ e5 = [] ∧ e2 = e4 ++ d5) := by
          exact frontier_options_from_vertical h1 i1 i2 hf
        rcases H with bb | fb
        · specialize h1_ih i1
          have one := h1_ih.1 ha11.1 (by rw [hb])
          have two := h1_ih.2 hb (by rw [ha11.1])
          rw [← bb.2]
          exact suffix_of_append two
        rw [fb.2.1] at i1
        have H := unique_g_pg_c_ones_okay i1 ha11.1.symm hb.symm t
        rw [fb.2.2, remove_ones_append, H.1]
        refine List.suffix_append_right ?_
        exact (h2_ih i2).2 H.2.symm ha11.2
      rcases baaad with ⟨db, c11, drest, h3, ⟨d2_is⟩, ⟨a1_is⟩, ⟨mid_nil⟩, len3⟩
      specialize h1_ih h3
      have H2 := h1_ih.2 hb (by rw [ha11.1])
      exact suffix_of_append H2
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    constructor
    intro ha hb
    have H : to_over_plain (n * q) = to_over_plain n ++ to_over_plain q := by
      simp [to_over_plain]
      sorry
    rw [H] at hb
    have H : ∃ b1 b2, b = b1 ++ b2 ∧
      remove_ones b1 = to_over_plain n ∧ remove_ones b2 = to_over_plain q := by sorry
    rcases H with ⟨b1, b2, b_is, b1_is, b2_is⟩
    rcases splittable_vertically_of_pg' h1 _ _ b_is (by sorry) (by sorry)
      with ⟨d4, e4, d5, e3, mid4, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · specialize h1_ih i1
      have new_h1_ih := h1_ih.1 ha (by rw [b1_is])
      specialize h2_ih i2
      have new_h2_ih := h2_ih.2
      match d4 with
      | [] => sorry
      | d41 :: d42 =>
        sorry
    sorry
    sorry

theorem prefix_of_bottom' (h : gridt i j k l) (h1 : PartialGrid a b mid d2 e2)
  (ha : a = to_up i) (hbj : remove_ones b <+: to_over_plain j) : remove_ones mid <+: to_over_plain l := by
  induction h generalizing a b mid d2 e2 with
  | empty =>
    sorry
  | top_bottom i => sorry
  | sides i => sorry
  | top_left i => sorry
  | adjacent i k h => sorry
  | separated i j h => sorry
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    have ha1 : m = [] ∨ q = [] ∨ a = to_up q ++ to_up m := by sorry
    rcases ha1 with m_nil | q_nil | ha1
    · have H : a = to_up q := by
        rw [m_nil] at ha
        sorry
      have on : o = [] ∧ p = n := word_side_side_t _ _ _ t m_nil
      specialize h2_ih h1 H
      rw [on.2] at h2_ih
      exact h2_ih hbj
    · have H : a = to_up m := by
        rw [q_nil] at ha
        sorry
      have rs : r = [] ∧ s = p := word_side_side_t _ _ _ h2 q_nil
      specialize h1_ih h1 H hbj
      rw [rs.2]
      exact h1_ih
    rcases splittable_horizontally_of_pg h1 _ _ ha1 to_up_len to_up_len
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
      specialize h2_ih i2
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
