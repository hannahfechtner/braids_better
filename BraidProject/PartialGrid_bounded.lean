import BraidProject.PartialGrid_prefix_suffix

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

theorem partial_grid_rm_top_bottom_length (h : PartialGrid a b c d e) (ha : remove_ones a = []) (hb : remove_ones b = [(i, true)]) :
    remove_ones c <+: [(i, true)] ∧ remove_ones e = [] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, remove_ones]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := helper_pg_empty g1 ha b1_is
      simp_all [PartialGrid.length]
    simp_all
    have H := helper_pg_empty g2 g1_ih.2.1 b2_is
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := helper_pg_empty g1 ha b1_is
      simp_all [PartialGrid.length]
    simp_all
    have H := helper_pg_empty g2 g1_ih.2.1 b2_is
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    simp at ha
    specialize g1_ih ha.2 hb
    rcases prefix_of_singleton g1_ih.1 with one | two
    · have H := helper_pg_empty g2 ha.1 one
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    simp at ha
    specialize g1_ih ha.2 hb
    rcases prefix_of_singleton g1_ih.1 with one | two
    · have H := helper_pg_empty g2 ha.1 one
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
theorem suffix_of_pair (h : a <:+ [b, c]) : a = [] ∨ a = [c] ∨ a = [b, c] := by
  rcases h with ⟨r, hr⟩
  match r with
  | [] => aesop
  | r1 :: r2 =>
    match r2 with
    | [] => aesop
    | r3 :: r4 => aesop

theorem prefix_of_pair (h : a <+: [b, c]) : a = [] ∨ a = [b] ∨ a = [b, c] := by
  rcases h with ⟨r, hr⟩
  match r with
  | [] => aesop
  | r1 :: r2 =>
    match r2 with
    | [] =>
      change _ = [b] ++ [c] at hr
      have H := List.append_singleton_eq_append_singleton hr
      aesop
    | r3 :: r4 =>
      apply congr_arg List.length at hr
      simp at hr
      have H : a.length = 0 := by omega
      aesop

theorem partial_grid_rm_top_bottom_length_w (h : PartialGrid a b c d e)
  (ha : remove_ones a = []) (hb : remove_ones b = [(i1, true), (i2, true)]) :
    remove_ones c <+: [(i1, true), (i2, true)] ∧ remove_ones e = [] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, remove_ones]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rename_i i j k l m n o p
    match hn : remove_ones j with
    | [] =>
      rw [hn, List.nil_append] at hb
      simp_all
      have H := helper_pg_empty g1 ha hn
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match hi : remove_ones m with
      | [] =>
        rw [hi, List.append_nil] at hb
        simp_all
        have H := helper_pg_empty g2 g1_ih.2.1 hi
        simp_all [PartialGrid.length]
      | i3 :: i4 =>
        rw [hn, hi] at hb
        have H := List.append_eq_len_two (by simp) (by simp) hb
        simp at H
        simp [H] at hn hi
        simp_all
        have H := partial_grid_rm_top_bottom_length g1 ha hn
        have H1 := partial_grid_rm_top_bottom_length g2 H.2.1 hi
        simp_all [PartialGrid.length]
        change _ <+: [(i1, true)] ++ [(i2, true)]
        have H : remove_ones k = [(i1, true)] := by
          have H := partial_grid_rm_top_helper g1 ha hn
          simp at H
          exact H.1
        rw [H]
        exact (List.prefix_append_right_inj [(i1, true)]).mpr H1.1
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rename_i i j k l m n o p
    match hn : remove_ones i with
    | [] =>
      rw [hn, List.nil_append] at hb
      simp_all
      have H := helper_pg_empty g1 ha hn
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match hi : remove_ones m with
      | [] =>
        rw [hi, List.append_nil] at hb
        simp_all
        have H := helper_pg_empty g2 g1_ih.2.1 hi
        simp_all [PartialGrid.length]
      | i3 :: i4 =>
        rw [hn, hi] at hb
        have H := List.append_eq_len_two (by simp) (by simp) hb
        simp at H
        simp [H] at hn hi
        simp_all
        have H := partial_grid_rm_top_bottom_length g1 ha hn
        have H1 := partial_grid_rm_top_bottom_length g2 H.2.1 hi
        simp_all [PartialGrid.length]
        change _ <+: [(i1, true)] ++ [(i2, true)]
        refine List.prefix_of_append H.1
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    simp at ha
    simp_all
    rcases prefix_of_pair g1_ih.1 with one | two | three
    · have H := helper_pg_empty g2 ha.1 one
      simp_all [PartialGrid.length]
    · have H := partial_grid_rm_top_bottom_length g2 ha.1 two
      simp_all [PartialGrid.length]
      change _ <+: [(i1, true)] ++ [(i2, true)]
      apply List.prefix_of_append H.1
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    simp at ha
    simp_all
    rcases prefix_of_pair g1_ih.1 with one | two | three
    · have H := helper_pg_empty g2 ha.1 one
      simp_all [PartialGrid.length]
    · have H := partial_grid_rm_top_bottom_length g2 ha.1 two
      simp_all [PartialGrid.length]
      change _ <+: [(i1, true)] ++ [(i2, true)]
      apply List.prefix_of_append H.1
    simp_all [PartialGrid.length]

theorem partial_grid_rm_side_length (h : PartialGrid a b c d e) (ha : remove_ones a = [(i, false)]) (hb : remove_ones b = []) :
    remove_ones c = [] ∧ remove_ones e <:+ [(i, false)] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, remove_ones]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp [remove_ones_append] at hb
    simp_all
    rcases suffix_of_singleton g1_ih.2.1
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    simp [remove_ones_append] at hb
    simp_all
    rcases suffix_of_singleton g1_ih.2.1
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      have H := helper_pg_empty g2 a1_is g1_ih.1
      simp_all [PartialGrid.length]
    have H := helper_pg_empty g1 a2_is hb
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      have H := helper_pg_empty g2 a1_is g1_ih.1
      simp_all [PartialGrid.length]
    have H := helper_pg_empty g1 a2_is hb
    simp_all [PartialGrid.length]

theorem partial_grid_rm_side_length_w (h : PartialGrid a b c d e)
    (ha : remove_ones a = [(i1, false), (i2, false)]) (hb : remove_ones b = []) :
    remove_ones c = [] ∧ remove_ones e <:+ [(i1, false), (i2, false)] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, remove_ones]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp [remove_ones_append] at hb
    simp_all
    rcases suffix_of_pair g1_ih.2.1 with one | two | three
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    · have H := partial_grid_rm_side_length g2 two hb.2
      simp_all [PartialGrid.length]
      change _ <:+ [(i1, false)] ++ [(i2, false)]
      apply suffix_of_append H.2.1
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    simp [remove_ones_append] at hb
    simp_all
    rcases suffix_of_pair g1_ih.2.1 with one | two | three
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    · have H := partial_grid_rm_side_length g2 two hb.2
      simp_all [PartialGrid.length]
      change _ <:+ [(i1, false)] ++ [(i2, false)]
      apply suffix_of_append H.2.1
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rename_i i j k l m n o p q
    match hn : remove_ones n with
    | [] =>
      rw [hn, List.nil_append] at ha
      simp_all
      have H := helper_pg_empty g2 hn g1_ih.1
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match hi : remove_ones i with
      | [] =>
        rw [hi, List.append_nil] at ha
        simp_all
        have H := helper_pg_empty g1 hi hb
        simp_all [PartialGrid.length]
      | i3 :: i4 =>
        rw [hn, hi] at ha
        have H := List.append_eq_len_two (by simp) (by simp) ha
        simp at H
        simp [H] at hn hi
        simp_all
        have H := partial_grid_rm_side_length g1 hi hb
        have H1 := partial_grid_rm_side_length g2 hn H.1
        simp_all [PartialGrid.length]
        change _ <:+ [(i1, false)] ++ [(i2, false)]
        exact suffix_of_append H.2.1
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rename_i i j k l m n o p
    match hn : remove_ones m with
    | [] =>
      rw [hn, List.nil_append] at ha
      simp_all
      have H := helper_pg_empty g2 hn g1_ih.1
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match hi : remove_ones i with
      | [] =>
        rw [hi, List.append_nil] at ha
        simp_all
        have H := helper_pg_empty g1 hi hb
        simp_all [PartialGrid.length]
      | i3 :: i4 =>
        rw [hn, hi] at ha
        have H := List.append_eq_len_two (by simp) (by simp) ha
        simp at H
        simp [H] at hn hi
        simp_all
        have H := partial_grid_rm_side_length g1 hi hb
        have H1 := partial_grid_rm_side_length g2 hn H.1
        simp_all [PartialGrid.length]
        change _ <:+ [(i1, false)] ++ [(i2, false)]
        have H : remove_ones l = [(i2, false)] := by
          have H := partial_grid_rm_side_helper g1 hi hb
          simp at H
          exact H.2
        rw [H]
        exact List.suffix_append_right H1.2.1

theorem partial_grid_rm_top_left_length (h : PartialGrid a b c d e) (ha : remove_ones a = [(i, false)]) (hb : remove_ones b = [(i, true)]) :
    remove_ones c <+: [(i, true)] ∧ remove_ones e <:+ [(i, false)] ∧ h.length ≤ 1 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, remove_ones]
    aesop
  | empty a b ha ha1 hb hb =>
    simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := partial_grid_rm_side_length g1 ha b1_is
      rcases suffix_of_singleton H.2.1 with one | two
      · have H2 := partial_grid_rm_top_bottom_length g2 one b2_is
        simp_all [PartialGrid.length]
      simp_all [PartialGrid.length]
    simp_all
    rcases suffix_of_singleton g1_ih.2.1 with one | two
    · have H := helper_pg_empty g2 one b2_is
      simp_all [PartialGrid.length]
    have H := partial_grid_rm_side_length g2 two b2_is
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := partial_grid_rm_side_length g1 ha b1_is
      rcases suffix_of_singleton H.2.1 with one | two
      · have H2 := partial_grid_rm_top_bottom_length g2 one b2_is
        simp_all [PartialGrid.length]
      simp_all [PartialGrid.length]
    simp_all
    rcases suffix_of_singleton g1_ih.2.1 with one | two
    · have H := helper_pg_empty g2 one b2_is
      simp_all [PartialGrid.length]
    have H := partial_grid_rm_side_length g2 two b2_is
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      rcases prefix_of_singleton g1_ih.1 with one | two
      · have H := helper_pg_empty g2 a1_is one
        simp_all [PartialGrid.length]
      have H := partial_grid_rm_top_bottom_length g2 a1_is two
      simp_all [PartialGrid.length]
    have H := partial_grid_rm_top_bottom_length g1 a2_is hb
    simp_all
    rcases prefix_of_singleton H.1 with one | two
    · have H2 := partial_grid_rm_side_length g2 a1_is one
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      rcases prefix_of_singleton g1_ih.1 with one | two
      · have H := helper_pg_empty g2 a1_is one
        simp_all [PartialGrid.length]
      have H := partial_grid_rm_top_bottom_length g2 a1_is two
      simp_all [PartialGrid.length]
    have H := partial_grid_rm_top_bottom_length g1 a2_is hb
    simp_all
    rcases prefix_of_singleton H.1 with one | two
    · have H2 := partial_grid_rm_side_length g2 a1_is one
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]

theorem partial_grid_rm_adjacent_length (h : PartialGrid a b c d e)
    (ha : remove_ones a = [(i, false)]) (hb : remove_ones b = [(k, true)]) :
    remove_ones c <+: [(k, true), (i, true)] ∧ remove_ones e <:+ [(k, false), (i, false)] ∧ h.length ≤ 1 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, remove_ones]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := partial_grid_rm_side_length g1 ha b1_is
      rcases suffix_of_singleton H.2.1 with one | two
      · have H2 := partial_grid_rm_top_bottom_length g2 one b2_is
        simp_all [PartialGrid.length]
        change _ <+: [(k, true)] ++ [(i, true)]
        refine List.prefix_concat_iff.mpr ?_
        aesop
      simp_all [PartialGrid.length]
    simp_all
    rcases suffix_of_pair g1_ih.2.1 with one | two | three
    · have H := helper_pg_empty g2 (by assumption) b2_is
      simp_all [PartialGrid.length]
    · have H := partial_grid_rm_side_length g2 two b2_is
      simp_all [PartialGrid.length]
      change _ <:+ [(k, false)] ++ [(i, false)]
      apply suffix_of_append H.2.1
    have H := partial_grid_rm_side_length_w g2 three b2_is
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := partial_grid_rm_side_length g1 ha b1_is
      rcases suffix_of_singleton H.2.1 with one | two
      · have H2 := partial_grid_rm_top_bottom_length g2 one b2_is
        simp_all [PartialGrid.length]
      simp_all [PartialGrid.length]
    simp_all
    rcases suffix_of_pair g1_ih.2.1 with one | two | three
    · have H := helper_pg_empty g2 (by assumption) b2_is
      simp_all [PartialGrid.length]
    · have H := partial_grid_rm_side_length g2 two b2_is
      simp_all [PartialGrid.length]
      change _ <:+ [(k, false)] ++ [(i, false)]
      apply suffix_of_append H.2.1
    have H := partial_grid_rm_side_length_w g2 three b2_is
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      rcases prefix_of_pair g1_ih.1 with one | two | three
      · have H := helper_pg_empty g2 a1_is one
        simp_all [PartialGrid.length]
      · have H := partial_grid_rm_top_bottom_length g2 a1_is two
        simp_all [PartialGrid.length]
        change _ <+: [(k, true)] ++ [(i, true)]
        apply List.prefix_of_append H.1
      have H := partial_grid_rm_top_bottom_length_w g2 a1_is three
      simp_all [PartialGrid.length]
    have H1 := partial_grid_rm_top_helper g1 a2_is hb
    have H := partial_grid_rm_top_bottom_length g1 a2_is hb
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      rcases prefix_of_pair g1_ih.1 with one | two | three
      · have H := helper_pg_empty g2 a1_is one
        simp_all [PartialGrid.length]
      · have H := partial_grid_rm_top_bottom_length g2 a1_is two
        simp_all [PartialGrid.length]
        change _ <+: [(k, true)] ++ [(i, true)]
        apply List.prefix_of_append H.1
      have H := partial_grid_rm_top_bottom_length_w g2 a1_is three
      simp_all [PartialGrid.length]
    have H := partial_grid_rm_top_bottom_length g1 a2_is hb
    simp_all [PartialGrid.length]
    rcases prefix_of_singleton H.1 with one | two
    · have H2 := partial_grid_rm_side_length g2 a1_is one
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]

theorem partial_grid_rm_separated_length (h : PartialGrid a b c d e)
    (ha : remove_ones a = [(i, false)]) (hb : remove_ones b = [(j, true)]) (hd : i.dist j > 1) :
    remove_ones c <+: [(j, true)] ∧ remove_ones e <:+ [(i, false)] ∧ h.length ≤ 1 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, remove_ones]
    aesop
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := partial_grid_rm_side_length g1 ha b1_is
      rcases suffix_of_singleton H.2.1 with one | two
      · have H2 := partial_grid_rm_top_bottom_length g2 one b2_is
        simp_all [PartialGrid.length]
      simp_all [PartialGrid.length]
    simp_all
    rcases suffix_of_singleton g1_ih.2.1 with one | two
    · have H := helper_pg_empty g2 one b2_is
      simp_all [PartialGrid.length]
    have H := partial_grid_rm_side_length g2 two b2_is
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := partial_grid_rm_side_length g1 ha b1_is
      rcases suffix_of_singleton H.2.1 with one | two
      · have H2 := partial_grid_rm_top_bottom_length g2 one b2_is
        simp_all [PartialGrid.length]
      simp_all [PartialGrid.length]
    simp_all
    rcases suffix_of_singleton g1_ih.2.1 with one | two
    · have H := helper_pg_empty g2 one b2_is
      simp_all [PartialGrid.length]
    have H := partial_grid_rm_side_length g2 two b2_is
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      rcases prefix_of_singleton g1_ih.1 with one | two
      · have H := helper_pg_empty g2 a1_is one
        simp_all [PartialGrid.length]
      have H := partial_grid_rm_top_bottom_length g2 a1_is two
      simp_all [PartialGrid.length]
    have H := partial_grid_rm_top_bottom_length g1 a2_is hb
    simp_all
    rcases prefix_of_singleton H.1 with one | two
    · have H2 := partial_grid_rm_side_length g2 a1_is one
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [remove_ones_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      rcases prefix_of_singleton g1_ih.1 with one | two
      · have H := helper_pg_empty g2 a1_is one
        simp_all [PartialGrid.length]
      have H := partial_grid_rm_top_bottom_length g2 a1_is two
      simp_all [PartialGrid.length]
    have H := partial_grid_rm_top_bottom_length g1 a2_is hb
    simp_all
    rcases prefix_of_singleton H.1 with one | two
    · have H2 := partial_grid_rm_side_length g2 a1_is one
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]

def is_true_map_to_some {r : List (ℕ × Bool)} (h : is_true r) : is_true (List.map (fun x => (some x.1, x.2)) r) := by
  induction r with
  | nil =>
    simp [is_true_nil]
    exact is_true_nil
  | cons head tail ih =>
    simp
    change is_true ([(some head.1, head.2)] ++ _)
    apply is_true_of_true_true
    · have H := (is_true_split h).1
      intro a ha
      simp at ha
      specialize H head ⟨by simp⟩
      rw [ha.1]
      exact H
    exact ih (is_true_split h).2

def is_false_map_to_some {r : List (ℕ × Bool)} (h : is_false r) :
    is_false (List.map (fun x => (some x.1, x.2)) r) := by
  induction r with
  | nil =>
    simp [is_false_nil]
    exact is_false_nil
  | cons head tail ih =>
    simp
    change is_false ([(some head.1, head.2)] ++ _)
    apply is_false_of_false_false
    · have H := (is_false_split h).1
      intro a ha
      simp at ha
      specialize H head ⟨by simp⟩
      rw [ha.1]
      exact H
    exact ih (is_false_split h).2

def to_over_plain_true : is_true (to_over_plain l) := by
  induction l with
  | nil =>
    simp [to_over_plain]
    exact is_true_nil
  | cons head tail ih =>
    simp [to_over_plain]
    change is_true ([(head, true)] ++ _)
    apply is_true_of_true_true
    · intro a ha
      simp at ha
      rw [ha.1]
      exact ⟨by simp⟩
    exact ih

def to_up_plain_false : is_false (to_up_plain l) := by
  induction l with
  | nil =>
    simp [to_up_plain]
    exact is_false_nil
  | cons head tail ih =>
    simp [to_up_plain]
    apply is_false_of_false_false
    · intro a ha
      simp at ha
      constructor
      rcases ha.1 with ⟨a1, ha1, a_is⟩
      simp [← a_is]
    intro a ha
    simp at ha
    rw [ha.1]
    exact ⟨by simp⟩

theorem remove_ones_add_some_is_self {r2 : List (α × Bool)} : remove_ones (List.map (fun x ↦ (some x.1, x.2)) r2) = r2 := by
  induction r2 with
  | nil => simp [remove_ones]
  | cons head tail ih =>
    simp [remove_ones, ih]

theorem pg_sm_g_eq1 (h : PartialGrid a b c d e) (h1 : gridt a1 b1 f g)
    : remove_ones a = to_up_plain a1 → remove_ones b = to_over_plain b1 → h.length ≤ h1.length := by
  induction h1 generalizing a b c d e with
  | empty =>
    intro ha hb
    simp [empty_rm_pg_len h ha hb]
  | top_bottom i =>
    intro ha hb
    simp [partial_grid_rm_top_bottom_length h ha hb]
  | sides i =>
    intro ha hb
    simp [partial_grid_rm_side_length h ha hb]
  | top_left i =>
    intro ha hb
    simp [partial_grid_rm_top_left_length h ha hb, gridt.length]
  | adjacent i k hd =>
    intro ha hb
    simp [partial_grid_rm_adjacent_length h ha hb, gridt.length]
  | separated i j hd =>
    intro ha hb
    simp [gridt.length]
    simp [partial_grid_rm_separated_length h ha hb hd, gridt.length]
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i i j k l m n o
    intro a_is b_is
    rcases remove_ones_eq_to_up_plain_prod a_is with one | two | splits
    · have nonsense : to_up_plain i = [] := by
        have H : to_up_plain [] = [] :=  rfl
        convert H
      rw [to_up_plain_prod, nonsense, List.append_nil] at a_is
      specialize h2_ih h a_is
      have i_one : i = 1 := by
        convert one
      have H := word_side_side_t _ _ _ h1 i_one
      have H : h1.length = 0 := by exact gridt_length_top_bottom_word i j k l h1 one
      simp [H, gridt.length]
      apply h2_ih
      convert b_is
      aesop
    · have nonsense : to_up_plain m = [] := by
        have H : to_up_plain [] = [] :=  rfl
        convert H
      rw [to_up_plain_prod, nonsense, List.nil_append] at a_is
      specialize h1_ih h a_is
      have i_one : m = 1 := by
        convert two
      have H := word_side_side_t _ _ _ h2 i_one
      have H : h2.length = 0 := by exact gridt_length_top_bottom_word _ _ _ _ h2 two
      simp [H, gridt.length]
      apply h1_ih
      exact b_is
    rcases splits with ⟨a1, a2, a1_len, a2_len, H, a1m, a2i⟩
    rcases splittable_horizontally_of_pg h _ _ H a2_len a1_len
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl]
      have hi1 := h1_ih i1 a2i b_is
      have hi2 : i2.length ≤ h2.length := by
        have H : remove_ones mid <+: to_over_plain l :=
          (same_time h1 i1).1 a2i (by rw [b_is])
        rcases H with ⟨r, hr⟩
        have rt : is_true r := by
          have H : is_true (to_over_plain l) := to_over_plain_true
          rw [← hr] at H
          exact (is_true_append H).2
        match r_is : r with
        | [] =>
          rw [List.append_nil] at hr
          exact h2_ih i2 (a1m) hr
        | r1 :: r2 =>
          have i3 := PartialGrid.extend_side_w_len i2 (List.map (fun x => (some x.1, x.2)) (r1 :: r2))
            (is_true_map_to_some rt) (by simp)
          specialize h2_ih i3.1 (a1m)
          rw [← hr] at h2_ih
          simp [remove_ones] at h2_ih
          rw [i3.2.1]
          exact h2_ih remove_ones_add_some_is_self
      simp [gridt.length]
      omega
    rcases baaad with ⟨ db, c1, drest, i1, ⟨long⟩, ⟨db_is⟩, ⟨c_nil⟩, ⟨len⟩⟩
    specialize h1_ih i1 a2i b_is
    simp [gridt.length]
    omega
  | horizontal h1 h2 h1_ih h2_ih =>
    intro a_is b_is
    rename_i i j k l m n o
    rcases remove_ones_eq_to_over_plain_prod b_is with one | two | splits
    · have nonsense : to_over_plain j = [] := by
        have H : to_over_plain [] = [] :=  rfl
        convert H
      rw [to_over_plain_prod, nonsense, List.nil_append] at b_is
      have i_one : j = 1 := by
        convert one
      have H := word_top_bottom_t _ _ _ h1 i_one
      rw [← H.1] at a_is
      specialize h2_ih h a_is b_is
      have H : h1.length = 0 := gridt_length_side_side_word i j k l h1 one
      simp [H, gridt.length, h2_ih]
    · have nonsense : to_over_plain m = [] := by
        have H : to_over_plain [] = [] :=  rfl
        convert H
      rw [to_over_plain_prod, nonsense, List.append_nil] at b_is
      have i_one : m = 1 := by
        convert two
      have H := word_top_bottom_t _ _ _ h2 i_one
      specialize h1_ih h a_is b_is
      have H : h2.length = 0 := gridt_length_side_side_word _ _ _ _ h2 two
      simp [H, gridt.length, h1_ih]
    rcases splits with ⟨b1, b2, b1_len, b2_len, bb1b2, b1j, b2m⟩
    rcases splittable_vertically_of_pg' h _ _ bb1b2 b1_len b2_len
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl, gridt.length]
      have hone := h1_ih i1 a_is b1j
      have two : i2.length ≤ h2.length := by
        have H2 := (same_time h1 i1).2 (by rw [b1j]; rfl) (by rw [a_is])
        rcases H2 with ⟨r, hr⟩
        match r with
        | [] =>
          rw [List.nil_append] at hr
          exact h2_ih i2 hr b2m
        | r1 :: r2 =>
          have rf : is_false (r1 :: r2) := by
            have H : is_false (to_up_plain k) := to_up_plain_false
            rw [← hr] at H
            exact (is_false_append H).1
          have H := PartialGrid.extend_bottom_w_len i2
            (List.map (fun x => (some x.1, x.2)) (r1 :: r2)) (is_false_map_to_some rf) (by simp)
          rcases H with ⟨h3, ⟨len⟩⟩
          rw [len]
          have hk : remove_ones (List.map (fun x ↦ (some x.1, x.2)) (r1 :: r2) ++ mid) = to_up_plain k := by
            rw [remove_ones_append]
            rw [← hr]
            apply (List.append_left_inj (remove_ones mid)).mpr
            simp [remove_ones]
            exact remove_ones_add_some_is_self
          exact h2_ih h3 hk b2m
      omega
    rcases baaad with ⟨db, drest, i1, ⟨len⟩, ⟨e_nil⟩, ⟨d_is⟩, ⟨b2_is⟩⟩
    specialize h1_ih i1 a_is b1j
    simp [gridt.length]
    omega
