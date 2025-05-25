import BraidProject.Gridt_length

theorem all_ones_length_pg (h : PartialGrid a b c d e) : a = [(none, false)] → b = [(none, true)] → h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i =>
      intro h1
      simp [to_up] at h1
    | adjacent i k h =>
      intro h1
      simp [to_up] at h1
    | separated i j h =>
      intro h1
      simp [to_up] at h1
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem top_bottom_length_pg (h : PartialGrid a b c d e) : a = [(none, false)] → b = [(some i, true)] → h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i =>  simp [PartialGrid.length]
    | sides i =>  simp [PartialGrid.length]
    | top_left i =>
      intro ha
      simp [to_up] at ha
    | adjacent i k h =>
      intro ha
      simp [to_up] at ha
    | separated i j h =>
      intro ha
      simp [to_up] at ha
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem side_side_length_pg {a b c d e i} (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(none, true)] → h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i =>  simp [PartialGrid.length]
    | sides i =>  simp [PartialGrid.length]
    | top_left i =>
      intro ha hb
      simp [to_over] at hb
    | adjacent i k h =>
      intro ha hb
      simp [to_over] at hb
    | separated i j h =>
      intro ha hb
      simp [to_over] at hb
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem top_left_length_pg {a b c d e i} (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some i, true)] →
  remove_ones (c ++ d ++ e) = [] → h.length = 1 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h =>simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro ha hb rm
    rw [ha, hb] at rm
    simp [remove_ones] at rm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem adjacent_length_pg (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some j, true)] →
    remove_ones (c ++ d ++ e) = [(j, true), (i, true), (j, false), (i, false)] → i.dist j = 1 → h.length = 1 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h => simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro a_is b_is rm
    simp [a_is, b_is, remove_ones] at rm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem separated_length_pg (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some k, true)] →
    remove_ones (c ++ d ++ e) = [(k, true), (i, false)] → i.dist k > 1 → h.length = 1 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h => simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro a_is b_is rm
    simp [a_is, b_is, remove_ones] at rm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

def split_vertically_pg' (h : PartialGrid a b c d e)  := ∀ b₁ b₂, b = b₁ ++ b₂ →
  b₁.length > 0 → b₂.length > 0 →
  (Σ mid c1 d1 c2 d2,
  (h1 : PartialGrid a b₁ c1 d1 mid) × (h2 : PartialGrid mid b₂ c2 d2 e) ×
  PLift (c ++ d = c1 ++ d1 ++ c2 ++ d2) ×
  PLift (h.length = h1.length + h2.length)) ⊕
  (Σ d1 d2, (h1 : PartialGrid a b₁ c d1 []) × PLift (h.length = h1.length) ×
    PLift (e = []) × PLift (d = d1 ++ d2) × PLift (b₂ = d2))

def split_vertically_pg_1 (h : PartialGrid a b c d e)  := ∀ b₁ b₂, b = b₁ ++ b₂ →
  b₁.length > 0 → b₂.length > 0 →
  (Σ mid c1 d1 c2 d2,
  (h1 : PartialGrid a b₁ c1 d1 mid) × (h2 : PartialGrid mid b₂ c2 d2 e) ×
  PLift (c ++ d = c1 ++ d1 ++ c2 ++ d2) ×
  PLift (h.length = h1.length + h2.length) ×
    (∀ {c3 m3 c4 d4}, PartialGrid a b₁ c3 [] m3 → PartialGrid m3 b₂ c4 d4 e →
      PLift (c3 ++ c4 = c → d4 = d → c1 = c3 ∧ mid = m3 ∧ d1 = [] ∧ c2 = c4 ∧ d2 = d4))) ⊕
  (Σ d1 d2, (h1 : PartialGrid a b₁ c d1 []) × PLift (h.length = h1.length) ×
    PLift (e = []) × PLift (d = d1 ++ d2) × PLift (b₂ = d2))

def List.append_eq_singleton_C (h : a ++ b = [c]) : PLift (a = [] ∧ b = [c]) ⊕ PLift (a = [c] ∧ b = []) := by
  induction a with
  | nil =>
    simp [List.append_eq_singleton_iff] at h
    exact Sum.inl ⟨rfl, h⟩
  | cons x xs ih =>
    simp at h
    right
    constructor
    simp [h]

def List.append_eq_append' {a b c d : List α} (h : a ++ b = c ++ d) :
    (Σ from_middle, PLift (c = a ++ from_middle) × PLift (b = from_middle ++ d)) ⊕
    (Σ to_middle, PLift (a = c ++ to_middle) × PLift (d = to_middle ++ b)) :=
  FreeMonoid.prod_eq_prod' h

def List.cases_C (a : List α) : PLift (a = []) ⊕ PLift (a.length > 0) :=
  match ha : a.length with
  | 0 => Sum.inl ⟨List.length_eq_zero_iff.mp ha⟩
  | Nat.succ n => Sum.inr ⟨by simp⟩

theorem not_both_empty : PartialGrid a b c d e → d = [] → e = [] → False := by
  intro h
  induction h with
  | single_gridt h =>
    intro ha hb
    simp [to_up] at hb
    rename_i c _
    match c with
    | [] => simp at hb
    | c1 :: c2 => simp at hb
  | empty a b ha ha1 hb hb1 =>
    intro h1
    apply congr_arg List.length at h1
    simp [List.length] at h1
    rw [h1.1] at ha
    simp at ha
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    exact g2_ih
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro h1
    apply g2_ih
    simp at h1
    exact h1.2.2
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro h1 h2
    simp at h2
    apply g2_ih h1
    exact h2.1
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro h1 h2
    simp at h1
    apply g1_ih h1.2.2 h2

theorem not_both_empty_early : PartialGrid a b c d e → c = [] → d = [] → False := by
  intro h
  induction h with
  | single_gridt h =>
    intro ha hb
    simp [to_over] at ha
    rename_i c
    match c with
    | [] => simp at ha
    | c1 :: c2 => simp at ha
  | empty a b ha ha1 hb hb1 =>
    intro _ h1
    apply congr_arg List.length at h1
    simp [List.length] at h1
    rw [h1.1] at ha
    simp at ha
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro h1 h2
    simp at h1
    exact g1_ih h1.1 rfl
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro h1 h2
    simp at h2
    exact g2_ih h2.2.1 h2.2.2
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    exact g2_ih
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro h1 h2
    simp at h2
    exact g2_ih h1 h2.1

theorem pg_not_mid_right_empty : PartialGrid a b c [] [] → False := fun h => not_both_empty h rfl rfl

noncomputable def PartialGrid.extend_bottom_w_len (h : PartialGrid a b c d e) (a2) (h2 : is_false a2) (h3 : a2 ≠ []) :
    (h1 : PartialGrid (a2 ++ a) b [] (a2 ++ c ++ d) e) × PLift (h.length = h1.length):= by
  induction h with
  | single_gridt h =>
    cases a2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i d
      rw [List.append_nil]
      have H := PartialGrid.vertical_append_one (PartialGrid.single_gridt h)
        (PartialGrid.empty (head :: tail) (to_over d) (by simp) h2 to_over_len_pos is_true_over)
      use PartialGrid.vertical_append_one (PartialGrid.single_gridt h)
        (PartialGrid.empty (head :: tail) (to_over d) (by simp) h2 to_over_len_pos is_true_over)
      constructor
      simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, ← List.append_assoc]
    use PartialGrid.empty (a2 ++ a) b (by rw [List.length_append]; omega) (is_false_of_false_false h2 ha1) (by assumption) hb
    simp [PartialGrid.length]
    exact ⟨trivial⟩
  | horizontal_append_one g1 g2 ih1 ih2 =>
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    have H : a2 ++ bot1 ++ [] ++ bot2 ++ mid2 = a2 ++ (bot1 ++ bot2) ++ mid2 := by simp
    rw [← H]
    use PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos_iff.mpr h3)) ih1.1 g2
    simp [PartialGrid.length]
    exact ih1.2
  | horizontal_append h g1 g2 ih1 ih2 =>
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    rw [← List.append_assoc, ← List.append_assoc]
    use PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos_iff.mpr h3)) ih1.1 g2
    simp [PartialGrid.length]
    exact ih1.2
  | vertical_append_one g1 g2 ih1 ih2 =>
    rw [← List.append_assoc]
    use PartialGrid.vertical_append_one g1 ih2.1
    simp [PartialGrid.length]
    exact ih2.2
  | vertical_append g1 g2 h ih1 ih2 =>
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    use PartialGrid.vertical_append g1 ih2.1 h
    simp [PartialGrid.length]
    exact ih2.2

-- noncomputable def splittable_vertically_of_pg1 (h : PartialGrid a b c d e) : split_vertically_pg_1 h := by
--   induction h with
--   | single_gridt h =>
--     cases h with
--     | empty =>
--       intro b₁ b₂ b_is b₁_len b₂_len
--       simp only [to_over] at b_is
--       apply congr_arg List.length at b_is
--       simp only [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
--       omega
--     | top_bottom i =>
--       intro b₁ b₂ b_is b₁_len b₂_len
--       simp only [to_over] at b_is
--       apply congr_arg List.length at b_is
--       simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
--       omega
--     | sides i =>
--       intro b₁ b₂ b_is b₁_len b₂_len
--       simp only [to_over] at b_is
--       apply congr_arg List.length at b_is
--       simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
--       omega
--     | top_left i =>
--       intro b₁ b₂ b_is b₁_len b₂_len
--       simp only [to_over] at b_is
--       apply congr_arg List.length at b_is
--       simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
--       omega
--     | adjacent i k h =>
--       intro b₁ b₂ b_is b₁_len b₂_len
--       simp only [to_over] at b_is
--       apply congr_arg List.length at b_is
--       simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
--       omega
--     | separated i j h =>
--       intro b₁ b₂ b_is b₁_len b₂_len
--       simp only [to_over] at b_is
--       apply congr_arg List.length at b_is
--       simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
--       omega
--   | empty a b ha ha1 hb hb1 =>
--     intro b₁ b₂ b_is b₁_len b₂_len
--     right
--     use a ++ b₁
--     have itb₁ : is_true b₁ := by
--       rw [b_is] at hb1
--       exact (is_true_append hb1).1
--     use b₂
--     use PartialGrid.empty a b₁ ha ha1 b₁_len itb₁
--     constructor
--     · exact ⟨by simp [PartialGrid.length]⟩
--     constructor
--     · exact ⟨rfl⟩
--     constructor
--     · constructor
--       rw [b_is]
--       simp
--     exact ⟨rfl⟩
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
--     intro b₃ b₄ b_is b₃_len b₄_len
--     rcases List.append_eq_append' b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
--     · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
--       · left
--         rw [silly, List.append_nil] at one
--         rw [silly, List.nil_append] at two
--         rw [one.1, ← two.1]
--         use up1, bot1, [], bot2, mid2
--         use g1, g2
--         simp [one.1, two.1, PartialGrid.length]
--         constructor
--         · exact ⟨trivial⟩
--         constructor
--         · exact ⟨trivial⟩
--         intro c3 m3 c4 d4 h1 h2
--         constructor
--         have bot1c3 : bot1 = c3 := by sorry
--         have up1m3 : up1=m3 := by sorry
--         simp [bot1c3, up1m3]
--         intro c4_is d4_is
--         exact ⟨c4_is.symm, d4_is.symm⟩
--       rcases g2_ih _ _ two.1 fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩, rest⟩ | bad
--       · left
--         rw [one.1]
--         use mid, (bot1 ++ c1), d1, c2, d2
--         use PartialGrid.horizontal_append_one g1 h1
--         use h2
--         constructor
--         · constructor
--           rw [List.append_assoc, long, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
--         constructor
--         · constructor
--           simp [PartialGrid.length, h_len, ← add_assoc]
--         intro c3 m3 c4 d4 j1 j2
--         constructor
--         intro c4_is d4_is
--         sorry

--       right
--       rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
--       rw [one.1]
--       use d1, d2
--       use PartialGrid.horizontal_append_one g1 h3
--       constructor
--       · exact ⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩
--       exact end_is
--     rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
--     · left
--       rw [silly, List.append_nil] at one
--       rw [silly, List.nil_append] at two
--       rw [← one.1, two.1]
--       use up1, bot1, [], bot2, mid2, g1, g2
--       simp [one.1, two.1, PartialGrid.length]
--       exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
--     rcases g1_ih _ _ one.1 b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
--     · left
--       rw [two.1]
--       use mid, c1, d1
--       match d2 with
--       | [] =>
--         use c2 ++ bot2, mid2
--         use h1
--         use PartialGrid.horizontal_append_one h2 g2
--         rw [List.append_nil, List.append_nil] at long
--         constructor
--         · rw [long]
--           exact ⟨by simp⟩
--         exact ⟨by simp [PartialGrid.length, h_len, ← add_assoc]⟩
--       | d21 :: d22 =>
--         use c2, d21 :: d22 ++ bot2 ++ mid2
--         use h1
--         use PartialGrid.horizontal_append (by simp) h2 g2
--         repeat rw [List.append_nil] at long
--         simp [long, h_len, PartialGrid.length, ← add_assoc]
--         exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
--     right
--     rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
--     have H := PartialGrid.left_length_pos g2
--     rw [end_is.1.1] at H
--     simp at H
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     rename_i a1 b1 bot1 mid1 up1 b2 bot2 mid2 up2
--     intro b₃ b₄ b_is b₃_len b₄_len
--     rcases List.append_eq_append' b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
--     · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
--       · left
--         rw [silly, List.append_nil] at one
--         rw [silly, List.nil_append] at two
--         rw [one.1, ← two.1]
--         use up1, bot1, mid1, bot2, mid2
--         use g1, g2
--         simp [one.1, two.1, PartialGrid.length]
--         exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
--       rcases g2_ih _ _ two.1 fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
--       · left
--         rw [one.1]
--         use mid, bot1, (mid1 ++ c1 ++ d1), c2, d2
--         use PartialGrid.horizontal_append h g1 h1
--         use h2
--         constructor
--         · constructor
--           rw [List.append_assoc, long]
--           simp
--         constructor
--         simp [PartialGrid.length, h_len, ← add_assoc]
--       right
--       rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
--       rw [one.1]
--       use (mid1 ++ bot2 ++ d1), d2
--       use PartialGrid.horizontal_append h g1 h3
--       constructor
--       · exact ⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩
--       constructor
--       · exact end_is.1
--       constructor
--       · rw [end_is.2.1.1]
--         simp
--         exact ⟨trivial⟩
--       exact end_is.2.2
--     rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
--     · left
--       rw [silly, List.append_nil] at one
--       rw [silly, List.nil_append] at two
--       rw [← one.1, two.1]
--       use up1, bot1, mid1, bot2, mid2, g1, g2
--       simp [one.1, two.1, PartialGrid.length]
--       exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
--     rcases g1_ih _ _ one.1 b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
--     · left
--       rw [two.1]
--       use mid, c1, d1
--       match d2 with
--       | [] =>
--         use c2 ++ bot2, mid2
--         use h1
--         use PartialGrid.horizontal_append_one h2 g2
--         rw [List.append_nil] at long
--         constructor
--         · rw [← List.append_assoc,← List.append_assoc, long]
--           exact ⟨by simp⟩
--         exact ⟨by simp [PartialGrid.length, h_len, ← add_assoc]⟩
--       | d21 :: d22 =>
--         use c2, d21 :: d22 ++ bot2 ++ mid2
--         use h1
--         use PartialGrid.horizontal_append (by simp) h2 g2
--         simp [← List.append_assoc, long, h_len, PartialGrid.length, ← add_assoc]
--         exact ⟨⟨by simp⟩, ⟨trivial⟩⟩
--     right
--     rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
--     have H := PartialGrid.left_length_pos g2
--     rw [end_is.1.1] at H
--     simp at H
--   | vertical_append_one g1 g2 g1_ih g2_ih =>
--     rename_i a1 b1 bot1 up1 a2 bot2 mid2 up2
--     intro a₃ a₄ a_is a₃_len a₄_len
--     rcases g1_ih _ _ a_is a₃_len a₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨len⟩⟩ | bad
--     · match d1 with
--       | [] =>
--         match d2 with
--         | [] =>
--           left
--           rw [List.append_nil, List.append_nil, List.append_nil] at long
--           have hc1 : c1.length > 0 := by
--             match c1 with
--             | [] =>
--               exact (not_both_empty_early h1 rfl rfl).elim
--             | co :: ct => simp
--           have hc2 : c2.length > 0 := by
--              match c2 with
--             | [] =>
--               exact (not_both_empty_early h2 rfl rfl).elim
--             | co :: ct => simp
--           rcases g2_ih _ _ long hc1 hc2 with ⟨mid2, c3, d3, c4, d4, i1, i2, long1, len1⟩ | bad
--           · use mid2 ++ mid, c3, d3, c4, d4
--             use PartialGrid.vertical_append_one h1 i1
--             use PartialGrid.vertical_append_one h2 i2
--             constructor
--             · exact long1
--             constructor
--             simp [PartialGrid.length, len1.1, len]
--             omega
--           rcases bad with ⟨d1, d2, h3, len1⟩
--           match up2 with
--           | [] =>
--             use mid, bot2, d1, c2, []
--             use PartialGrid.vertical_append_one h1 h3
--             use h2
--             constructor
--             · constructor
--               rw [List.append_assoc, List.append_assoc]
--               apply (List.append_right_inj bot2).mpr
--               rw [List.append_nil, len1.2.2.1.1]
--               simp
--               exact len1.2.2.2.1.symm
--             constructor
--             simp [PartialGrid.length, len, ← len1.1.1]
--             omega
--           | d21 :: d22 =>
--             exfalso
--             simp at len1
--             exact len1.2.1.1
--         | d21 :: d22 =>
--           have H : is_true bot1 := by exact g2.top_frontier_is_true
--           simp at long
--           rw [long] at H
--           have H2 := middle_frontier_nil_or_caps h2
--           rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
--           · simp at H2
--             exact H2.1.elim
--           rw [spec.1] at H
--           specialize H (front, false)
--           simp [is_true] at H
--           exact (H ⟨trivial⟩).1.elim
--       | d11 :: d12 =>
--         have H : is_true bot1 := by exact g2.top_frontier_is_true
--         simp only [List.append_nil, List.append_assoc] at long
--         rw [long] at H
--         have H2 := middle_frontier_nil_or_caps h1
--         rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
--         · simp at H2
--           exact H2.1.elim
--         rw [spec.1] at H
--         specialize H (front, false)
--         simp [is_true] at H
--         exact (H ⟨trivial⟩).1.elim
--     rcases bad with ⟨d1, d2, h3, ⟨len⟩, up1_is, ⟨d1h2_empty⟩, ⟨a2h4⟩⟩
--     rw [up1_is.1] at g1
--     right
--     exact (pg_not_mid_right_empty g1).elim
--   | vertical_append g1 g2 h g1_ih g2_ih =>
--     rename_i a1 b1 bot1 mid1 up1 a2 bot2 mid2 up2
--     intro a₃ a₄ a_is a₃_len a₄_len
--     rcases g1_ih _ _ a_is a₃_len a₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨len⟩⟩ | bad
--     · match d1 with
--       | [] =>
--         have both_c : is_true (c1 ++ c2) :=
--             is_true_of_true_true h1.bottom_frontier_is_true h2.bottom_frontier_is_true
--         have bot1_is : bot1 = c1 ++ c2 := by
--           rw [List.append_nil] at long
--           rcases middle_frontier_nil_or_caps g1 with H | ⟨front, mid, caboose, spec⟩
--           · rw [H.1] at h
--             simp at h
--           rw [spec.1] at long
--           rcases middle_frontier_nil_or_caps h2 with H | ⟨front1, mid1, caboose1, spec1⟩
--           · simp [H.1] at long
--             rw [← long] at both_c
--             specialize both_c (front, false)
--             simp [is_true] at both_c
--             exact (both_c ⟨trivial⟩).1.elim
--           rw [spec1.1] at long
--           rcases list_splits_somewhere long with ⟨h1⟩ | ⟨tm, one, two⟩ | ⟨fm, one, two⟩
--           · exact h1.1
--           · match tm with
--             | [] =>
--               simp at one
--               exact one
--             | (a, true) :: a1 =>
--               simp at two
--             | (a, false) :: a1 =>
--               have H : is_true bot1 := g2.top_frontier_is_true
--               rw [one] at H
--               specialize H (a, false)
--               simp at H
--               exact (H ⟨trivial⟩).1.elim
--           match fm with
--           | [] =>
--             rw [List.append_nil] at one
--             exact one
--           | (a, true) :: a1 =>
--             simp at two
--           | (a, false) :: a1 =>
--             rw [← one] at both_c
--             specialize both_c (a, false)
--             simp at both_c
--             exact (both_c ⟨trivial⟩).1.elim
--         have mid_is : mid1 = d2 := by
--           simp [bot1_is] at long
--           exact long
--         have c1_len : c1.length > 0 := by
--           match c1 with
--           | [] =>
--             exact (not_both_empty_early h1 rfl rfl).elim
--           | c11 :: c12 => simp
--         match c2 with
--         | [] =>
--           left
--           use up2 ++ mid, bot2, mid2, [], up2++ [] ++ d2
--           rw [List.append_nil] at bot1_is
--           subst bot1_is
--           use PartialGrid.vertical_append_one h1 g2
--           match up2 with
--           | [] =>
--             use h2
--             constructor
--             · constructor
--               simp [mid_is]
--             simp [PartialGrid.length, len]
--             exact ⟨by omega⟩
--           | up21 :: up22 =>
--             use (PartialGrid.extend_bottom_w_len h2 (up21 :: up22) (PartialGrid.right_frontier_is_false g2) (by simp)).1
--             constructor
--             · constructor
--               simp [mid_is]
--             constructor
--             simp [PartialGrid.length, len,
--               (PartialGrid.extend_bottom_w_len h2 (up21 :: up22) (PartialGrid.right_frontier_is_false g2) (by simp)).2.1]
--             omega
--         | c21 :: c22 =>
--           left
--           rcases g2_ih _ _  bot1_is c1_len (by simp) with
--               ⟨mid3, c3, d3, c4, d4, i1, i2, long1, len1⟩ | ⟨d1, d2', h3, ⟨len1⟩, rest⟩
--           · use mid3 ++ mid, c3, d3, c4
--             match d2 with
--             | [] =>
--               exfalso
--               rw [mid_is] at h
--               simp at h
--             | d21 :: d22 =>
--               use d4 ++ up2 ++ d21 :: d22
--               use PartialGrid.vertical_append_one h1 i1
--               use PartialGrid.vertical_append h2 i2 (by simp)
--               constructor
--               · constructor
--                 rw [← List.append_assoc, ← List.append_assoc, long1.1, mid_is]
--                 simp
--               constructor
--               simp [PartialGrid.length, len1.1, len]
--               omega
--           use mid, bot2, d1, c21::c22, d2
--           use PartialGrid.vertical_append_one h1 h3
--           use h2
--           constructor
--           · constructor
--             rw [rest.2.1.1, mid_is, rest.1.1, rest.2.2.1]
--             simp
--           simp [PartialGrid.length, len1, len]
--           exact ⟨by omega⟩
--       | d11 :: d12 =>
--         have H0 : is_true bot1 := by exact g2.top_frontier_is_true
--         have bot1_is : bot1 = c1 := by
--           rcases middle_frontier_nil_or_caps h1 with H | ⟨front, mid, caboose, spec⟩
--           · simp at H
--             exact H.1.elim
--           rw [spec.1] at long
--           rcases middle_frontier_nil_or_caps g1 with H | ⟨front1, mid1, caboose1, spec1⟩
--           · simp [H.1] at long
--             rw [long] at H0
--             specialize H0 (front, false)
--             simp [is_true] at H0
--             specialize H0 ⟨trivial⟩
--             exact H0.1.elim
--           rw [spec1.1] at long
--           simp at long
--           rcases list_splits_somewhere long with ⟨h1⟩ | ⟨tm, one, two⟩ | ⟨fm, one, two⟩
--           · exact h1.1
--           · match tm with
--             | [] =>
--               simp at one
--               exact one
--             | (a, true) :: a1 =>
--               simp at two
--             | (a, false) :: a1 =>
--               rw [one] at H0
--               specialize H0 (a, false)
--               simp at H0
--               exact (H0 ⟨trivial⟩).1.elim
--           match fm with
--           | [] =>
--             rw [List.append_nil] at one
--             exact one
--           | (a, true) :: a1 =>
--             simp at two
--           | (a, false) :: a1 =>
--             have H36 : is_true c1 := h1.bottom_frontier_is_true
--             rw [← one] at H36
--             specialize H36 (a, false)
--             simp at H36
--             exact (H36 ⟨trivial⟩).1.elim
--         simp [bot1_is] at long
--         match c1 with
--         | [] =>
--           rw [bot1_is] at g2
--           exfalso
--           have H := PartialGrid.top_length_pos g2
--           simp at H
--         | c11 :: c12 =>
--           left
--           use mid, bot2, mid2 ++ up2 ++ (d11 :: d12), c2, d2
--           subst bot1_is
--           use PartialGrid.vertical_append h1 g2 (by simp)
--           use h2
--           constructor
--           · constructor
--             simp [long]
--           simp [PartialGrid.length, len]
--           exact ⟨by omega⟩
--     rcases bad with ⟨d1, d2, h3, ⟨len⟩, ⟨up1_nil⟩, ⟨mid1_is⟩, ⟨a4d2⟩⟩
--     right
--     use mid2++ up2 ++d1, d2
--     have H : d1.length > 0 := by
--       match d1 with
--       | [] =>
--         exfalso
--         apply not_both_empty h3 rfl rfl
--       | d11 :: d12 => simp
--     use PartialGrid.vertical_append h3 g2 H
--     constructor
--     · simp [PartialGrid.length, len]
--       exact ⟨trivial⟩
--     constructor
--     · exact ⟨up1_nil⟩
--     constructor
--     · constructor
--       simp [mid1_is]
--     exact ⟨a4d2⟩


noncomputable def splittable_vertically_of_pg' (h : PartialGrid a b c d e) : split_vertically_pg' h := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp only [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | top_bottom i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | sides i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | top_left i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | adjacent i k h =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | separated i j h =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
  | empty a b ha ha1 hb hb1 =>
    intro b₁ b₂ b_is b₁_len b₂_len
    right
    use a ++ b₁
    have itb₁ : is_true b₁ := by
      rw [b_is] at hb1
      exact (is_true_append hb1).1
    use b₂
    use PartialGrid.empty a b₁ ha ha1 b₁_len itb₁
    constructor
    · exact ⟨by simp [PartialGrid.length]⟩
    constructor
    · exact ⟨rfl⟩
    constructor
    · constructor
      rw [b_is]
      simp
    exact ⟨rfl⟩
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    intro b₃ b₄ b_is b₃_len b₄_len
    rcases List.append_eq_append' b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
    · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
      · left
        rw [silly, List.append_nil] at one
        rw [silly, List.nil_append] at two
        rw [one.1, ← two.1]
        use up1, bot1, [], bot2, mid2
        use g1, g2
        simp [one.1, two.1, PartialGrid.length]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
      rcases g2_ih _ _ two.1 fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
      · left
        rw [one.1]
        use mid, (bot1 ++ c1), d1, c2, d2
        use PartialGrid.horizontal_append_one g1 h1
        use h2
        constructor
        · constructor
          rw [List.append_assoc, long, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
        constructor
        simp [PartialGrid.length, h_len, ← add_assoc]
      right
      rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
      rw [one.1]
      use d1, d2
      use PartialGrid.horizontal_append_one g1 h3
      constructor
      · exact ⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩
      exact end_is
    rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
    · left
      rw [silly, List.append_nil] at one
      rw [silly, List.nil_append] at two
      rw [← one.1, two.1]
      use up1, bot1, [], bot2, mid2, g1, g2
      simp [one.1, two.1, PartialGrid.length]
      exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    rcases g1_ih _ _ one.1 b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
    · left
      rw [two.1]
      use mid, c1, d1
      match d2 with
      | [] =>
        use c2 ++ bot2, mid2
        use h1
        use PartialGrid.horizontal_append_one h2 g2
        rw [List.append_nil, List.append_nil] at long
        constructor
        · rw [long]
          exact ⟨by simp⟩
        exact ⟨by simp [PartialGrid.length, h_len, ← add_assoc]⟩
      | d21 :: d22 =>
        use c2, d21 :: d22 ++ bot2 ++ mid2
        use h1
        use PartialGrid.horizontal_append (by simp) h2 g2
        repeat rw [List.append_nil] at long
        simp [long, h_len, PartialGrid.length, ← add_assoc]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    right
    rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
    have H := PartialGrid.left_length_pos g2
    rw [end_is.1.1] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 b2 bot2 mid2 up2
    intro b₃ b₄ b_is b₃_len b₄_len
    rcases List.append_eq_append' b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
    · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
      · left
        rw [silly, List.append_nil] at one
        rw [silly, List.nil_append] at two
        rw [one.1, ← two.1]
        use up1, bot1, mid1, bot2, mid2
        use g1, g2
        simp [one.1, two.1, PartialGrid.length]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
      rcases g2_ih _ _ two.1 fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
      · left
        rw [one.1]
        use mid, bot1, (mid1 ++ c1 ++ d1), c2, d2
        use PartialGrid.horizontal_append h g1 h1
        use h2
        constructor
        · constructor
          rw [List.append_assoc, long]
          simp
        constructor
        simp [PartialGrid.length, h_len, ← add_assoc]
      right
      rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
      rw [one.1]
      use (mid1 ++ bot2 ++ d1), d2
      use PartialGrid.horizontal_append h g1 h3
      constructor
      · exact ⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩
      constructor
      · exact end_is.1
      constructor
      · rw [end_is.2.1.1]
        simp
        exact ⟨trivial⟩
      exact end_is.2.2
    rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
    · left
      rw [silly, List.append_nil] at one
      rw [silly, List.nil_append] at two
      rw [← one.1, two.1]
      use up1, bot1, mid1, bot2, mid2, g1, g2
      simp [one.1, two.1, PartialGrid.length]
      exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    rcases g1_ih _ _ one.1 b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
    · left
      rw [two.1]
      use mid, c1, d1
      match d2 with
      | [] =>
        use c2 ++ bot2, mid2
        use h1
        use PartialGrid.horizontal_append_one h2 g2
        rw [List.append_nil] at long
        constructor
        · rw [← List.append_assoc,← List.append_assoc, long]
          exact ⟨by simp⟩
        exact ⟨by simp [PartialGrid.length, h_len, ← add_assoc]⟩
      | d21 :: d22 =>
        use c2, d21 :: d22 ++ bot2 ++ mid2
        use h1
        use PartialGrid.horizontal_append (by simp) h2 g2
        simp [← List.append_assoc, long, h_len, PartialGrid.length, ← add_assoc]
        exact ⟨⟨by simp⟩, ⟨trivial⟩⟩
    right
    rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
    have H := PartialGrid.left_length_pos g2
    rw [end_is.1.1] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 up1 a2 bot2 mid2 up2
    intro a₃ a₄ a_is a₃_len a₄_len
    rcases g1_ih _ _ a_is a₃_len a₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨len⟩⟩ | bad
    · match d1 with
      | [] =>
        match d2 with
        | [] =>
          left
          rw [List.append_nil, List.append_nil, List.append_nil] at long
          have hc1 : c1.length > 0 := by
            match c1 with
            | [] =>
              exact (not_both_empty_early h1 rfl rfl).elim
            | co :: ct => simp
          have hc2 : c2.length > 0 := by
             match c2 with
            | [] =>
              exact (not_both_empty_early h2 rfl rfl).elim
            | co :: ct => simp
          rcases g2_ih _ _ long hc1 hc2 with ⟨mid2, c3, d3, c4, d4, i1, i2, long1, len1⟩ | bad
          · use mid2 ++ mid, c3, d3, c4, d4
            use PartialGrid.vertical_append_one h1 i1
            use PartialGrid.vertical_append_one h2 i2
            constructor
            · exact long1
            constructor
            simp [PartialGrid.length, len1.1, len]
            omega
          rcases bad with ⟨d1, d2, h3, len1⟩
          match up2 with
          | [] =>
            use mid, bot2, d1, c2, []
            use PartialGrid.vertical_append_one h1 h3
            use h2
            constructor
            · constructor
              rw [List.append_assoc, List.append_assoc]
              apply (List.append_right_inj bot2).mpr
              rw [List.append_nil, len1.2.2.1.1]
              simp
              exact len1.2.2.2.1.symm
            constructor
            simp [PartialGrid.length, len, ← len1.1.1]
            omega
          | d21 :: d22 =>
            exfalso
            simp at len1
            exact len1.2.1.1
        | d21 :: d22 =>
          have H : is_true bot1 := by exact g2.top_frontier_is_true
          simp at long
          rw [long] at H
          have H2 := middle_frontier_nil_or_caps h2
          rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
          · simp at H2
            exact H2.1.elim
          rw [spec.1] at H
          specialize H (front, false)
          simp [is_true] at H
          exact (H ⟨trivial⟩).1.elim
      | d11 :: d12 =>
        have H : is_true bot1 := by exact g2.top_frontier_is_true
        simp only [List.append_nil, List.append_assoc] at long
        rw [long] at H
        have H2 := middle_frontier_nil_or_caps h1
        rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
        · simp at H2
          exact H2.1.elim
        rw [spec.1] at H
        specialize H (front, false)
        simp [is_true] at H
        exact (H ⟨trivial⟩).1.elim
    rcases bad with ⟨d1, d2, h3, ⟨len⟩, up1_is, ⟨d1h2_empty⟩, ⟨a2h4⟩⟩
    rw [up1_is.1] at g1
    right
    exact (pg_not_mid_right_empty g1).elim
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 a2 bot2 mid2 up2
    intro a₃ a₄ a_is a₃_len a₄_len
    rcases g1_ih _ _ a_is a₃_len a₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨len⟩⟩ | bad
    · match d1 with
      | [] =>
        have both_c : is_true (c1 ++ c2) :=
            is_true_of_true_true h1.bottom_frontier_is_true h2.bottom_frontier_is_true
        have bot1_is : bot1 = c1 ++ c2 := by
          rw [List.append_nil] at long
          rcases middle_frontier_nil_or_caps g1 with H | ⟨front, mid, caboose, spec⟩
          · rw [H.1] at h
            simp at h
          rw [spec.1] at long
          rcases middle_frontier_nil_or_caps h2 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp [H.1] at long
            rw [← long] at both_c
            specialize both_c (front, false)
            simp [is_true] at both_c
            exact (both_c ⟨trivial⟩).1.elim
          rw [spec1.1] at long
          rcases list_splits_somewhere long with ⟨h1⟩ | ⟨tm, one, two⟩ | ⟨fm, one, two⟩
          · exact h1.1
          · match tm with
            | [] =>
              simp at one
              exact one
            | (a, true) :: a1 =>
              simp at two
            | (a, false) :: a1 =>
              have H : is_true bot1 := g2.top_frontier_is_true
              rw [one] at H
              specialize H (a, false)
              simp at H
              exact (H ⟨trivial⟩).1.elim
          match fm with
          | [] =>
            rw [List.append_nil] at one
            exact one
          | (a, true) :: a1 =>
            simp at two
          | (a, false) :: a1 =>
            rw [← one] at both_c
            specialize both_c (a, false)
            simp at both_c
            exact (both_c ⟨trivial⟩).1.elim
        have mid_is : mid1 = d2 := by
          simp [bot1_is] at long
          exact long
        have c1_len : c1.length > 0 := by
          match c1 with
          | [] =>
            exact (not_both_empty_early h1 rfl rfl).elim
          | c11 :: c12 => simp
        match c2 with
        | [] =>
          left
          use up2 ++ mid, bot2, mid2, [], up2++ [] ++ d2
          rw [List.append_nil] at bot1_is
          subst bot1_is
          use PartialGrid.vertical_append_one h1 g2
          match up2 with
          | [] =>
            use h2
            constructor
            · constructor
              simp [mid_is]
            simp [PartialGrid.length, len]
            exact ⟨by omega⟩
          | up21 :: up22 =>
            use (PartialGrid.extend_bottom_w_len h2 (up21 :: up22) (PartialGrid.right_frontier_is_false g2) (by simp)).1
            constructor
            · constructor
              simp [mid_is]
            constructor
            simp [PartialGrid.length, len,
              (PartialGrid.extend_bottom_w_len h2 (up21 :: up22) (PartialGrid.right_frontier_is_false g2) (by simp)).2.1]
            omega
        | c21 :: c22 =>
          left
          rcases g2_ih _ _  bot1_is c1_len (by simp) with
              ⟨mid3, c3, d3, c4, d4, i1, i2, long1, len1⟩ | ⟨d1, d2', h3, ⟨len1⟩, rest⟩
          · use mid3 ++ mid, c3, d3, c4
            match d2 with
            | [] =>
              exfalso
              rw [mid_is] at h
              simp at h
            | d21 :: d22 =>
              use d4 ++ up2 ++ d21 :: d22
              use PartialGrid.vertical_append_one h1 i1
              use PartialGrid.vertical_append h2 i2 (by simp)
              constructor
              · constructor
                rw [← List.append_assoc, ← List.append_assoc, long1.1, mid_is]
                simp
              constructor
              simp [PartialGrid.length, len1.1, len]
              omega
          use mid, bot2, d1, c21::c22, d2
          use PartialGrid.vertical_append_one h1 h3
          use h2
          constructor
          · constructor
            rw [rest.2.1.1, mid_is, rest.1.1, rest.2.2.1]
            simp
          simp [PartialGrid.length, len1, len]
          exact ⟨by omega⟩
      | d11 :: d12 =>
        have H0 : is_true bot1 := by exact g2.top_frontier_is_true
        have bot1_is : bot1 = c1 := by
          rcases middle_frontier_nil_or_caps h1 with H | ⟨front, mid, caboose, spec⟩
          · simp at H
            exact H.1.elim
          rw [spec.1] at long
          rcases middle_frontier_nil_or_caps g1 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp [H.1] at long
            rw [long] at H0
            specialize H0 (front, false)
            simp [is_true] at H0
            specialize H0 ⟨trivial⟩
            exact H0.1.elim
          rw [spec1.1] at long
          simp at long
          rcases list_splits_somewhere long with ⟨h1⟩ | ⟨tm, one, two⟩ | ⟨fm, one, two⟩
          · exact h1.1
          · match tm with
            | [] =>
              simp at one
              exact one
            | (a, true) :: a1 =>
              simp at two
            | (a, false) :: a1 =>
              rw [one] at H0
              specialize H0 (a, false)
              simp at H0
              exact (H0 ⟨trivial⟩).1.elim
          match fm with
          | [] =>
            rw [List.append_nil] at one
            exact one
          | (a, true) :: a1 =>
            simp at two
          | (a, false) :: a1 =>
            have H36 : is_true c1 := h1.bottom_frontier_is_true
            rw [← one] at H36
            specialize H36 (a, false)
            simp at H36
            exact (H36 ⟨trivial⟩).1.elim
        simp [bot1_is] at long
        match c1 with
        | [] =>
          rw [bot1_is] at g2
          exfalso
          have H := PartialGrid.top_length_pos g2
          simp at H
        | c11 :: c12 =>
          left
          use mid, bot2, mid2 ++ up2 ++ (d11 :: d12), c2, d2
          subst bot1_is
          use PartialGrid.vertical_append h1 g2 (by simp)
          use h2
          constructor
          · constructor
            simp [long]
          simp [PartialGrid.length, len]
          exact ⟨by omega⟩
    rcases bad with ⟨d1, d2, h3, ⟨len⟩, ⟨up1_nil⟩, ⟨mid1_is⟩, ⟨a4d2⟩⟩
    right
    use mid2++ up2 ++d1, d2
    have H : d1.length > 0 := by
      match d1 with
      | [] =>
        exfalso
        apply not_both_empty h3 rfl rfl
      | d11 :: d12 => simp
    use PartialGrid.vertical_append h3 g2 H
    constructor
    · simp [PartialGrid.length, len]
      exact ⟨trivial⟩
    constructor
    · exact ⟨up1_nil⟩
    constructor
    · constructor
      simp [mid1_is]
    exact ⟨a4d2⟩

noncomputable def split_horizontally_pg (h : PartialGrid a b c d e) := ∀ a1 a2,
  a = a2 ++ a1 → a1.length > 0 → a2.length > 0 → (Σ mid d1 e1 d2 e2,
  (h1 : PartialGrid a1 b mid d2 e2) × (h2 : PartialGrid a2 mid c d1 e1) ×
  PLift (d1 ++ e1 ++ d2 ++e2 = d ++ e) × PLift (h.length = h1.length + h2.length)) ⊕
  (Σ db c1 drest, (h1 : PartialGrid a1 b c1 drest e) × PLift (d = db ++ c1 ++ drest) ×
  PLift (a2 = db) × PLift (c = []) × PLift (h.length = h1.length))

def bool_swap (a : List (α × Bool)) : List (α × Bool) := List.map (fun x => (x.1, !x.2)) a.reverse

theorem bool_swap_to_over : bool_swap (to_over a) = to_up a := by
  induction a with
  | nil => simp [to_over, to_up, bool_swap]
  | cons head tail ih =>
    simp [bool_swap, to_over, ih, to_up]

theorem bool_swap_to_up : bool_swap (to_up a) = to_over a := by
  induction a with
  | nil => simp [to_over, to_up, bool_swap]
  | cons head tail ih =>
    simp [bool_swap, to_up, ih, to_over]

theorem bool_swap_idem : bool_swap (bool_swap a) = a := by
  induction a with
  | nil => simp [bool_swap]
  | cons head tail ih =>
    simp [bool_swap]
    simp [bool_swap] at ih
    exact ih

theorem bool_swap_nil : bool_swap ([] : List (α × Bool)) = [] := by simp [bool_swap]

theorem bool_swap_append : bool_swap (a ++ b) = bool_swap b ++ bool_swap a := by
  simp [bool_swap]

theorem bool_swap_length : (bool_swap a).length = a.length := by
  simp [bool_swap]

def bool_swap_true (h : is_true a) : is_false (bool_swap a) := by
  simp [is_false, bool_swap]
  intro a1 a1_in
  constructor
  simp at a1_in
  rcases a1_in.1 with ⟨w, h4 | h5⟩
  · specialize h (w, false) ⟨h4.1⟩
    simp at h
    exact h.1.elim
  rw [← h5.2]

def bool_swap_false (h : is_false a) : is_true (bool_swap a) := by
  simp [is_true, bool_swap]
  intro a1 a1_in
  constructor
  simp at a1_in
  rcases a1_in.1 with ⟨w, h4 | h5⟩
  · rw [← h4.2]
  specialize h (w, true) ⟨h5.1⟩
  simp at h
  exact h.1.elim

theorem nil_of_bool_swap_eq_nil (h : bool_swap a = []) : a = [] := by
  apply congr_arg bool_swap at h
  rw [bool_swap_idem, bool_swap_nil] at h
  exact h

noncomputable def reflect (h : PartialGrid a b c d e) :
    (h1 : PartialGrid (bool_swap b) (bool_swap a) (bool_swap e) (bool_swap d) (bool_swap c)) ×
    PLift (h.length = h1.length) := by
  induction h with
  | single_gridt h =>
    rw [bool_swap_to_up, bool_swap_to_over, bool_swap_to_up, bool_swap_to_over, bool_swap_nil]
    cases h with
    | empty =>
      use PartialGrid.single_gridt (cell.empty)
      exact ⟨rfl⟩
    | top_bottom i =>
      use PartialGrid.single_gridt (cell.sides i)
      exact ⟨rfl⟩
    | sides i =>
      use PartialGrid.single_gridt (cell.top_bottom i)
      exact ⟨rfl⟩
    | top_left i =>
      use PartialGrid.single_gridt (cell.top_left i)
      exact ⟨rfl⟩
    | adjacent i k h =>
      use PartialGrid.single_gridt (cell.adjacent k i (by rw [Nat.dist_comm] at h; exact h))
      exact ⟨rfl⟩
    | separated i j h =>
      use PartialGrid.single_gridt (cell.separated j i (by rw [Or.comm] at h; exact h))
      exact ⟨rfl⟩
  | empty a b ha ha1 hb hb1 =>
    rw [bool_swap_append]
    rw [← bool_swap_length] at ha
    rw [← bool_swap_length] at hb
    use PartialGrid.empty (bool_swap b) (bool_swap a) hb (bool_swap_true hb1) ha (bool_swap_false ha1)
    simp [PartialGrid.length]
    exact ⟨trivial⟩
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [bool_swap_append, bool_swap_append]
    rcases g1_ih with ⟨h3, len3⟩
    rcases g2_ih with ⟨h4, len4⟩
    use PartialGrid.vertical_append_one h3 h4
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]⟩
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rw [bool_swap_append, bool_swap_append, bool_swap_append, ← List.append_assoc]
    rcases g1_ih with ⟨h3, len3⟩
    rcases g2_ih with ⟨h4, len4⟩
    rw [← bool_swap_length] at h
    use PartialGrid.vertical_append h3 h4 h
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]⟩
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [bool_swap_append, bool_swap_append]
    rcases g1_ih with ⟨h3, len3⟩
    rcases g2_ih with ⟨h4, len4⟩
    use PartialGrid.horizontal_append_one h3 h4
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]⟩
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [bool_swap_append, bool_swap_append, bool_swap_append, ← List.append_assoc]
    rcases g1_ih with ⟨h3, len3⟩
    rcases g2_ih with ⟨h4, len4⟩
    rw [← bool_swap_length] at h
    use PartialGrid.horizontal_append h h3 h4
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]⟩

noncomputable def reflect_one_two (h : PartialGrid a1 b1 c d e) : a1 = bool_swap a → b1 = bool_swap b →
  (h1 : PartialGrid b a (bool_swap e) (bool_swap d) (bool_swap c)) × PLift (h.length = h1.length) := by
  intro a_eq b_eq
  apply congr_arg bool_swap at a_eq
  rw [bool_swap_idem] at a_eq
  rw [← a_eq]
  apply congr_arg bool_swap at b_eq
  rw [bool_swap_idem] at b_eq
  rw [← b_eq]
  apply reflect h

noncomputable def reflect_two_five (h : PartialGrid a b1 c d e1) : b1 = bool_swap b → e1 = bool_swap e →
  (h1 : PartialGrid b (bool_swap a) e (bool_swap d) (bool_swap c)) × PLift (h.length = h1.length) := by
  intro b_eq e_eq
  apply congr_arg bool_swap at b_eq
  rw [bool_swap_idem] at b_eq
  rw [← b_eq]
  apply congr_arg bool_swap at e_eq
  rw [bool_swap_idem] at e_eq
  rw [← e_eq]
  apply reflect h

noncomputable def reflect_one_two_three (c e) (h : PartialGrid a1 b1 c1 d e) :
    a1 = bool_swap a → b1 = bool_swap b → c1 = bool_swap c →
    (h1 : PartialGrid b a (bool_swap e) (bool_swap d) c) × PLift (h.length = h1.length) := by
  intro a_eq b_eq c_eq
  apply congr_arg bool_swap at a_eq
  rw [bool_swap_idem] at a_eq
  rw [← a_eq]
  apply congr_arg bool_swap at b_eq
  rw [bool_swap_idem] at b_eq
  rw [← b_eq]
  apply congr_arg bool_swap at c_eq
  rw [bool_swap_idem] at c_eq
  rw [← c_eq]
  apply reflect h

noncomputable def splittable_horizontally_of_pg (h : PartialGrid a b c d e) :
    split_horizontally_pg h := by
  intro a1 a2 a_is a1_len a2_len
  have H := reflect h
  have splitter := splittable_vertically_of_pg' H.1
  have split_a : bool_swap a = bool_swap a1 ++ bool_swap a2 := by
    rw [a_is, bool_swap_append]
  have splitter := splittable_vertically_of_pg' H.1 _ _ split_a
  rw [bool_swap_length, bool_swap_length] at splitter
  specialize splitter a1_len a2_len
  rcases splitter with ⟨mid, d1, e1, d2, e2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
  · left
    use bool_swap mid, bool_swap e2, bool_swap d2, bool_swap e1, bool_swap d1
    use (reflect_one_two h1 rfl rfl).1
    use (reflect_two_five h2 rfl rfl).1
    constructor
    · constructor
      apply congr_arg bool_swap at long
      simp [bool_swap_append, bool_swap_idem] at long
      simp
      exact long.symm
    constructor
    simp [H.2.1, h_len, (reflect_one_two h1 rfl rfl).2.1, (reflect_two_five h2 rfl rfl).2.1]
  rcases bad with ⟨d1, d2, h3, len, c_is, d_is, a2_is⟩
  right
  have c_nil : c = [] := nil_of_bool_swap_eq_nil c_is.1
  use bool_swap d2, [], bool_swap d1
  subst c_nil
  have H0 := reflect_one_two_three e ([] : List (Option ℕ × Bool)) h3 rfl rfl rfl
  use H0.1
  constructor
  · constructor
    simp [← bool_swap_append]
    have H := congr_arg bool_swap d_is.1
    rw [bool_swap_idem] at H
    exact H
  constructor
  · have H := congr_arg bool_swap a2_is.1
    rw [bool_swap_idem] at H
    exact ⟨H⟩
  constructor
  · exact ⟨rfl⟩
  constructor
  rw [H.2.1, ← H0.2.1, ← len.1]

theorem pg_empty {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(none, false)]) (hb : b = [(none, true)]) (hd : d = []) :
  c = [(none, true)] ∧ e = [(none, false)] := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [to_over, to_up]
    | top_bottom i => simp [to_over] at hb
    | sides i => simp [to_up] at ha
    | top_left i => simp [to_over] at hb
    | adjacent i k h => simp [to_over] at hb
    | separated i j h => simp [to_over] at hb
  | empty a b ha ha1 hb hb =>
    rw [ha] at hd
    simp at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H

theorem pg_top_bottom {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(none, false)]) (hb : b = [(some i, true)]) (hd : d = []) :
  c = [(some i, true)] ∧ e = [(none, false)] := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [to_over] at hb
    | top_bottom i => simp [ha, hb]
    | sides i => simp [to_over] at hb
    | top_left i => simp [to_up] at ha
    | adjacent i k h => simp [to_up] at ha
    | separated i j h => simp [to_up] at ha
  | empty a b ha ha1 hb hb =>
    rw [ha] at hd
    simp at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H

theorem pg_side_side {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(some i, false)]) (hb : b = [(none, true)]) (hd : d = []) :
  c = [(none, true)] ∧ e = [(some i, false)] := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [to_up] at ha
    | top_bottom i => simp [ha, hb]
    | sides i => simp [ha, hb]
    | top_left i => simp [to_over] at hb
    | adjacent i k h => simp [to_over] at hb
    | separated i j h => simp [to_over] at hb
  | empty a b ha ha1 hb hb =>
    rw [ha] at hd
    simp at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H

theorem pg_top_left {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(some i, false)]) (hb : b = [(some i, true)]) (hd : d = []) :
  c = [(none, true)] ∧ e = [(none, false)] := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [to_up] at ha
    | top_bottom i => simp [to_up] at ha
    | sides i => simp [to_over] at hb
    | top_left i => simp [ha, hb]
    | adjacent i k h =>
      simp [to_up] at ha
      simp [to_over] at hb
      rw [ha, hb] at h
      aesop
    | separated i j h =>
      simp [to_up] at ha
      simp [to_over] at hb
      rw [ha, hb] at h
      aesop
  | empty a b ha ha1 hb hb =>
    rw [ha] at hd
    simp at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H

theorem pg_adjacent {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(some i, false)]) (hb : b = [(some j, true)]) (hd : d = []) (hij : i.dist j = 1):
  c = [(some j, true), (some i, true)] ∧ e = [(some j, false), (some i, false)] := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [to_up] at ha
    | top_bottom i => simp [to_up] at ha
    | sides i => simp [to_over] at hb
    | top_left i =>
      simp [to_up] at ha
      simp [to_over] at hb
      aesop
    | adjacent i k h =>
      simp [to_up] at ha
      simp [to_over] at hb
      rw [ha, hb] at h
      simp [to_up, to_over, ha, hb]
    | separated i j h =>
      simp [to_up] at ha
      simp [to_over] at hb
      apply or_dist_iff.mpr at h
      aesop
  | empty a b ha ha1 hb hb =>
    rw [ha] at hd
    simp at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H

theorem pg_separated {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(some i, false)]) (hb : b = [(some j, true)]) (hd : d = []) (hij : i.dist j > 1):
  c = [(some j, true)] ∧ e = [(some i, false)] := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [to_up] at ha
    | top_bottom i => simp [to_up] at ha
    | sides i => simp [to_over] at hb
    | top_left i =>
      simp [to_up] at ha
      simp [to_over] at hb
      aesop
    | adjacent i k h =>
      simp [to_up] at ha
      simp [to_over] at hb
      aesop
    | separated i j h =>
      simp [to_up] at ha
      simp [to_over] at hb
      aesop
  | empty a b ha ha1 hb hb =>
    rw [ha] at hd
    simp at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.top_length_pos g1
      rw [hb] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨hb, hb2⟩ | ⟨hb, hb2⟩
    · have H := PartialGrid.left_length_pos g2
      rw [hb] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb2] at H
    simp at H

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

-- noncomputable def PartialGrid.extend_side_w_len  (h : PartialGrid a b c d e) (b2) (h2 : is_true b2) (h3 : b2 ≠ []) :
--     (h1 : PartialGrid a (b ++ b2) c (d ++ e ++ b2) []) × PLift  (h.length = h1.length) := by
--   induction h with
--   | single_gridt h =>
--     cases b2 with
--     | nil => simp at h3
--     | cons head tail =>
--       rename_i c d
--       have H : [] ++ to_over d = to_over d ++ [] := by simp
--       rw [List.nil_append]
--       have H1 := PartialGrid.horizontal_append_one (PartialGrid.single_gridt h)
--           (PartialGrid.empty (to_up c) (head :: tail) to_up_len_pos is_false_up (by simp) h2)
--       rw [← H] at H1
--       use H1
--       sorry
--   | empty a b ha ha1 hb hb =>
--     rw [List.append_nil, List.append_assoc]
--     use PartialGrid.empty a (b ++ b2) ha ha1 (by rw [List.length_append]; omega) (is_true_of_true_true hb h2)
--     simp [PartialGrid.length]
--     exact ⟨trivial⟩
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     rw [List.append_assoc]
--     use PartialGrid.horizontal_append_one g1 g2_ih.1
--     simp [PartialGrid.length]
--     exact g2_ih.2
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     rename_i a1 b1 bot1 mid1 up1 b3 bot3 mid3 up3
--     have H1 : mid1 ++ bot3 ++ (mid3 ++ up3 ++ b2) = mid1 ++ bot3 ++ mid3 ++ up3 ++ b2 := by simp
--     rw [List.append_assoc, ← H1]
--     use PartialGrid.horizontal_append h g1 g2_ih.1
--     simp [PartialGrid.length]
--     exact g2_ih.2
--   | vertical_append_one g1 g2 g1_ih g2_ih =>
--     rename_i a1 b1 bot1 up1 a3 bot3 mid3 up3
--     have H : mid3 ++ (up3 ++ up1) ++ b2 = mid3 ++ up3 ++ ([] ++ up1 ++ b2) := by simp
--     rw [H]
--     use PartialGrid.vertical_append g1_ih.1 g2 (by simp; exact Or.inr (List.length_pos_iff.mpr h3))
--     simp [PartialGrid.length]
--     exact g1_ih.2
--   | vertical_append g1 g2 h g1_ih g2_ih =>
--     rename_i a1 b1 bot1 mid1 up1 a3 bot3 mid3 up3
--     have H : mid3 ++ up3 ++ mid1 ++ up1 ++ b2 = mid3 ++ up3 ++ (mid1 ++ up1 ++ b2) := by simp
--     rw [H]
--     use PartialGrid.vertical_append g1_ih.1 g2 (by simp; exact Or.inr (Or.inr (List.length_pos_iff.mpr h3)))
--     simp [PartialGrid.length]
--     exact g1_ih.2

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
    exact empty_helper _ c_is d_is e_is
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


theorem straight_pg_sm_g (h : PartialGrid a b c d e) (h1 : gridt a1 b1 f g)
    : a <:+ to_up a1 → b <+: to_over b1 → h.length ≤ h1.length := by
  induction h generalizing a1 b1 f g with
  | single_gridt h =>
    intro ha hb
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i =>
      simp [PartialGrid.length]
      rcases ha with ⟨ra, hra⟩
      rcases hb with ⟨rb, hrb⟩
      have H1 : ∃ rra, a1 = .of i * rra := by sorry
      have H2 : ∃ rrb, b1 = .of i * rrb := split_it_helper hrb
      rcases H1 with ⟨rra, dsa⟩
      rcases H2 with ⟨rrb, dsb⟩
      rcases splittable_horizontally_of_gridn h1 _ _ dsa with ⟨rest, c1, c2, g1, g2, ⟨c_is⟩, ⟨len1⟩⟩
      rcases splittable_vertically_of_gridn g1 _ _ dsb with ⟨rest2, d1, d2, g3, g4, ⟨d_is⟩, ⟨len2⟩⟩
      rw [len1, len2, gridt_length_top_left g3 rfl rfl]
      omega
      -- rw [PartialGrid.length, gridt_length_top_left h1 _ (to_over_inj hb)]
    | adjacent i k h =>
      simp [PartialGrid.length]
      rcases ha with ⟨ra, hra⟩
      rcases hb with ⟨rb, hrb⟩
      have H1 : ∃ rra, a1 = .of i * rra := by sorry
      have H2 : ∃ rrb, b1 = .of k * rrb := split_it_helper hrb
      rcases H1 with ⟨rra, dsa⟩
      rcases H2 with ⟨rrb, dsb⟩
      rcases splittable_horizontally_of_gridn h1 _ _ dsa with ⟨rest, c1, c2, g1, g2, ⟨c_is⟩, ⟨len1⟩⟩
      rcases splittable_vertically_of_gridn g1 _ _ dsb with ⟨rest2, d1, d2, g3, g4, ⟨d_is⟩, ⟨len2⟩⟩
      rw [len1, len2, gridt_length_adjacent g3 rfl rfl h]
      omega
    | separated i j h =>
      simp [PartialGrid.length]
      rcases ha with ⟨ra, hra⟩
      rcases hb with ⟨rb, hrb⟩
      have H1 : ∃ rra, a1 = .of i * rra := by sorry
      have H2 : ∃ rrb, b1 = .of j * rrb := split_it_helper hrb
      rcases H1 with ⟨rra, dsa⟩
      rcases H2 with ⟨rrb, dsb⟩
      rcases splittable_horizontally_of_gridn h1 _ _ dsa with ⟨rest, c1, c2, g1, g2, ⟨c_is⟩, ⟨len1⟩⟩
      rcases splittable_vertically_of_gridn g1 _ _ dsb with ⟨rest2, d1, d2, g3, g4, ⟨d_is⟩, ⟨len2⟩⟩
      rw [len1, len2, gridt_length_separated g3 _ rfl (or_dist_iff.mpr h)]
      omega
      rfl
      --rw [PartialGrid.length, gridt_length_separated h1 (to_up_inj ha) (to_over_inj hb) (or_dist_iff.mpr h)]
  | empty a b ha ha1 hb hb =>
    simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    intro ha hb
    have b2_ne_nil : b2 ≠ [] := by
      intro hb2
      rw [hb2] at g1
      have H := PartialGrid.top_length_pos g1
      simp at H
    have b3_neq_nil : b3 ≠ [] := by
      intro hb3
      rw [hb3] at g2
      have H := PartialGrid.top_length_pos g2
      simp at H
    have H : ∃ b4 b5, to_over b5 = b3 ∧ to_over b4 = b2 ∧ ((b4 ++ b5) <+: b1) := by
      sorry
    rcases H with ⟨b4, b5, b5_is, b4_is, H⟩
    rcases H with ⟨rest, hr⟩
    rcases splittable_vertically_of_gridn h1 _ _ hr.symm with ⟨b6, b7, b8, b9, gt, ⟨g_is⟩, ⟨len⟩⟩
    specialize g1_ih b9 ha
    rw [len]
    have b45_ne_nil : b4 ++ b5 ≠ [] := by
      intro hb45
      have hb4 : b4 = [] ∧ b5 = [] := List.append_eq_nil_iff.mp hb45
      rw [hb4.1] at b4_is
      rw [hb4.2] at b5_is
      simp [to_over] at b4_is
      simp [to_over] at b5_is
      rw [← b4_is, ← b5_is] at hb
      cases b1 with
      | h0 =>
        change _ <+: [(none, true)] at hb
        simp [List.cons_prefix_cons, List.prefix_nil, List.cons_ne_self, and_false] at hb
      | ih x xs =>
        change _ <+: (some x, true) :: List.map (fun x ↦ (some x, true)) xs at hb
        simp at hb
    have nonsense : b2 <+: to_over (Append.append b4 b5)  := by
      have h1 : b2 <+: to_over b4 := by
        rw [b4_is]
      simp [b45_ne_nil, to_over]
      cases h : Append.append b4 b5
      · apply (b45_ne_nil h).elim
      rename_i head tail
      simp only
      rw [← h]
      change b2 <+: List.map (fun x ↦ (some x, true)) (b4 ++ b5)
      rw [List.map_append]
      refine List.prefix_of_append ?_
      sorry


    specialize g1_ih nonsense
    simp [PartialGrid.length]
    apply Nat.add_le_add g1_ih
    apply g2_ih
    --have hb6 : to_up b6 = up2 := (unique_g_pg_c g1 ha b4_is b9).1
    sorry
    sorry
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a3 b3 bot3 mid3 up3 b4 bot4 mid4 up4
    intro ha hb
    have b3_ne_nil : b3 ≠ [] := by
      intro hb3
      rw [hb3] at g1
      have H := PartialGrid.top_length_pos g1
      simp at H
    have b4_neq_nil : b4 ≠ [] := by
      intro hb4
      rw [hb4] at g2
      have H := PartialGrid.top_length_pos g2
      simp at H
    have H : ∃ b5 b6, to_over b6 = b4 ∧ to_over b5 = b3 ∧ b1 = b5 ++ b6 := by
      sorry
    rcases H with ⟨b5, b6, b6_is, b5_is, H⟩
    rcases splittable_vertically_of_gridn h1 b5 b6 H with ⟨b7, b8, b9, b10, gt, ⟨g_is⟩, ⟨len⟩⟩
    specialize g1_ih b10 ha
    rw [len]
    specialize g1_ih b5_is
    simp [PartialGrid.length]
    apply Nat.add_le_add g1_ih
    have hb7 : to_up b7 = up3 := by sorry
    apply g2_ih _ hb7 b6_is
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry
