import BraidProject.SimplerPG.SimplePG_prefix_suffix
import BraidProject.GridsTwo_C
import BraidProject.Gridt_length
import BraidProject.NewListFacts
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

theorem partial_grid_rm_top_bottom_length (h : PartialGrid a b c d e) (ha : a = []) (hb : b = [(i, true)]) :
    c <+: [(i, true)] ∧ e = [] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, to_up_plain]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := helper_pg_empty g1 ha b1_is
      simp_all [PartialGrid.length]
    simp_all
    have H := helper_pg_empty g2 g1_ih.2.1 b2_is
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := helper_pg_empty g1 ha b1_is
      simp_all [PartialGrid.length]
    simp_all
    have H := helper_pg_empty g2 g1_ih.2.1 b2_is
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    simp at ha
    specialize g1_ih ha.2 hb
    rcases prefix_of_singleton g1_ih.1 with one | two
    · have H := helper_pg_empty g2 ha.1 one
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
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

theorem List.prefix_of_singleton (h : L <:+ [a]) : L = [] ∨ L = [a] := by
  exact
  suffix_of_singleton h

theorem List.prefix_of_append' (h : L <+: a) : L <+: a ++ b := by
  refine (List.isPrefix_append_of_length ?_).mpr h
  refine List.IsPrefix.length_le h

theorem partial_grid_rm_top_bottom_length_w (h : PartialGrid a b c d e)
  (ha : a = []) (hb : b = [(i1, true), (i2, true)]) :
    c <+: [(i1, true), (i2, true)] ∧ e = [] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, to_up_plain]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i i j k l m n o p
    match  j with
    | [] =>
      rw [List.nil_append] at hb
      simp_all
      have H := helper_pg_empty g1 ha
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match m with
      | [] =>
        rw [List.append_nil] at hb
        simp_all
        have H := helper_pg_empty g2 g1_ih.2.1
        simp_all [PartialGrid.length]
      | i3 :: i4 =>
        have H' := List.append_eq_len_two (by simp) (by simp) hb
        simp at H'
        --simp [H] at hb
        simp_all
        have H := @partial_grid_rm_top_bottom_length _ _ _ _ _ i1 g1 ha (by simp [H'])
        have H1 := @partial_grid_rm_top_bottom_length _ _ _ _ _ i3.1 g2 H.2.1 (by simp [H'])
        simp_all [PartialGrid.length]
        change _ <+: [(i1, true)] ++ [(i2, true)]
        rcases prefix_of_singleton H.1
        · have H := @partial_grid_rm_top_helper _ _ _ _ _ i1 g1 ha
          aesop
        rename_i k_is
        rw [k_is]
        exact (List.prefix_append_right_inj [(i1, true)]).mpr H1.1
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i i j k l m n o p
    match i with
    | [] =>
      rw [List.nil_append] at hb
      simp_all
      have H := helper_pg_empty g1 ha
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match m with
      | [] =>
        rw [List.append_nil] at hb
        simp_all
        have H := helper_pg_empty g2 g1_ih.2.1
        simp_all [PartialGrid.length]
      | i3 :: i4 =>
        -- have H := List.append_eq_len_two (by simp) (by simp) hb
        -- simp at H
        -- simp [H] at hn hi
        -- simp_all
        have h : n2.length = 0 := by
          apply congr_arg List.length at hb
          simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil,
            zero_add, Nat.reduceAdd, Nat.reduceEqDiff] at hb
          linarith
        have hi4 : i4.length = 0 := by
          apply congr_arg List.length at hb
          simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil,
            zero_add, Nat.reduceAdd, Nat.reduceEqDiff] at hb
          linarith
        have i3_is : i3 = (i2, true) := by
          rw [List.length_eq_zero_iff.mp hi4, List.length_eq_zero_iff.mp h] at hb
          simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at hb
          exact hb.2
        have H := @partial_grid_rm_top_bottom_length _ _ _ _ _ i1 g1 ha
        simp_all only [List.cons.injEq, and_imp, forall_const, List.cons_append,
          List.length_eq_zero_iff, List.ne_cons_self, and_self, and_true, IsEmpty.forall_iff,
          imp_self, List.nil_append, Prod.mk.injEq, implies_true, true_and]
        simp_all [PartialGrid.length]
        have H1 := @partial_grid_rm_top_bottom_length _ _ _ _ _ i2 g2 H.2.1
        simp_all [PartialGrid.length]
        change _ <+: [(i1, true)] ++ [(i2, true)]
        refine List.prefix_of_append H.1
  | vertical_append_one g1 g2 g1_ih g2_ih =>
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

theorem partial_grid_rm_side_length (h : PartialGrid a b c d e)
    (ha : a = [(i, false)]) (hb : b = []) :
    c = [] ∧ e <:+ [(i, false)] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, to_up_plain, to_over_plain]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp only [List.append_eq_nil_iff] at hb
    specialize g1_ih ha hb.1
    rcases suffix_of_singleton g1_ih.2.1
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    simp only [List.append_eq_nil_iff] at hb
    specialize g1_ih ha hb.1
    rcases suffix_of_singleton g1_ih.2.1
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      have H := helper_pg_empty g2 a1_is g1_ih.1
      simp_all [PartialGrid.length]
    have H := helper_pg_empty g1 a2_is hb
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      have H := helper_pg_empty g2 a1_is g1_ih.1
      simp_all [PartialGrid.length]
    have H := helper_pg_empty g1 a2_is hb
    simp_all [PartialGrid.length]

theorem List.suffix_of_append_mine (h1 : a <:+ b) : a <:+ c ++ b := by
  refine reverse_prefix.mp ?_
  simp
  refine prefix_of_append' ?_
  exact reverse_prefix.mpr h1

theorem partial_grid_rm_side_length_w (h : PartialGrid a b c d e)
    (ha : a = [(i1, false), (i2, false)]) (hb : b = []) :
     c = [] ∧  e <:+ [(i1, false), (i2, false)] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, to_up_plain]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp only [List.append_eq_nil_iff] at hb
    simp_all only [forall_const, List.nil_append]
    rcases suffix_of_pair g1_ih.2.1 with one | two | three
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    · have H := partial_grid_rm_side_length g2 two hb.2
      simp_all [PartialGrid.length]
      change _ <:+ [(i1, false)] ++ [(i2, false)]
      apply List.suffix_of_append_mine H.2.1
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    simp only [List.append_eq_nil_iff] at hb
    simp_all
    rcases suffix_of_pair g1_ih.2.1 with one | two | three
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    · have H := partial_grid_rm_side_length g2 two hb.2
      simp_all [PartialGrid.length]
      change _ <:+ [(i1, false)] ++ [(i2, false)]
      apply List.suffix_of_append_mine H.2.1
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i i j k l m n o p q
    match hn : n with
    | [] =>
      rw [List.nil_append] at ha
      simp_all
      have H := helper_pg_empty g2 rfl g1_ih.1
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match hi : i with
      | [] =>
        rw [List.append_nil] at ha
        simp_all
        have H := helper_pg_empty g1 rfl hb
        simp_all [PartialGrid.length]
      | i3 :: i4 =>
        have H := List.append_eq_len_two (by simp) (by simp) ha
        simp at H
        simp [H] at hn hi
        simp_all
        have H' := @partial_grid_rm_side_length _ _ _ _ _ i2 g1 (by simp [H.2]) hb
        have H1 := @partial_grid_rm_side_length _ _ _ _ _ i1 g2 (by simp [H.1]) H'.1
        simp_all [PartialGrid.length]
        change _ <:+ [(i1, false)] ++ [(i2, false)]
        exact List.suffix_of_append_mine H'.2.1
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i i j k l m n o p
    match  m with
    | [] =>
      rw [List.nil_append] at ha
      simp_all
      have H := helper_pg_empty g2 rfl g1_ih.1
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match i with
      | [] =>
        rw [List.append_nil] at ha
        simp_all
        have H := helper_pg_empty g1 rfl hb
        simp_all [PartialGrid.length]
      | i3 :: i4 =>
        have H := List.append_eq_len_two (by simp) (by simp) ha
        simp at H
        simp_all
        have H' := @partial_grid_rm_side_length _ _ _ _ _ i2 g1 (by simp [H.2]) hb
        have H1 := @partial_grid_rm_side_length _ _ _ _ _ i1 g2 (by simp [H.1]) H'.1
        simp_all [PartialGrid.length]
        change _ <:+ [(i1, false)] ++ [(i2, false)]
        have H : l = [(i2, false)] := by
          have H := @partial_grid_rm_side_helper _ _ _ _ _ i2 g1 (by simp [H.2]) hb
          simp at H
          exact H.2
        rw [H]
        exact List.suffix_append_right H1.2.1

theorem partial_grid_rm_top_left_length (h : PartialGrid a b c d e) (ha : a = [(i, false)]) (hb : b = [(i, true)]) :
    c <+: [(i, true)] ∧ e <:+ [(i, false)] ∧ h.length ≤ 1 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, to_up_plain, to_over_plain]
    aesop
  | empty a b ha ha1 hb hb =>
    simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
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
    (ha : a = [(i, false)]) (hb : b = [(k, true)]) :
   c <+: [(k, true), (i, true)] ∧ e <:+ [(k, false), (i, false)] ∧ h.length ≤ 1 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, to_up_plain, to_over_plain]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
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
      apply List.suffix_of_append_mine H.2.1
    have H := partial_grid_rm_side_length_w g2 three b2_is
    simp_all [PartialGrid.length]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
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
      apply List.suffix_of_append_mine H.2.1
    have H := partial_grid_rm_side_length_w g2 three b2_is
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
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
    (ha : a = [(i, false)]) (hb : b = [(j, true)]) (hd : i.dist j > 1) :
   c <+: [(j, true)] ∧  e <:+ [(i, false)] ∧ h.length ≤ 1 := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [PartialGrid.length, to_up_plain, to_over_plain]
    aesop
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
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

theorem to_up_plain_mul {a b : FreeMonoid ℕ} :
  to_up_plain (a * b) = to_up_plain b ++ to_up_plain a := by
  rw [← to_up_plain_append]
  rfl

theorem to_over_plain_mul {a b : FreeMonoid α} :
  to_over_plain (a * b) = to_over_plain a ++ to_over_plain b := by
  rw [← to_over_plain_append]
  rfl

theorem pg_sm_g_eq1 (h : PartialGrid a b c d e) (h1 : gridt a1 b1 f g)
    : a = to_up_plain a1 → b = to_over_plain b1 → h.length ≤ h1.length := by
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
    rw [to_up_plain_mul] at a_is
    match hi : to_up_plain i with
    | [] =>
      rw [hi, List.append_nil] at a_is
      specialize h2_ih h a_is
      have i_one : i = 1 := by
        simp [to_up_plain] at hi
        convert hi
      have H := word_side_side_t _ _ _ h1 i_one
      have H : h1.length = 0 := by
        apply gridt_length_top_bottom_word i j k l h1
        exact i_one
      simp [H, gridt.length]
      apply h2_ih
      convert b_is
      aesop
    | il1 :: il2 =>
      match hm : m with
      | [] =>
        rw [to_up_plain, List.reverse_nil, List.map_nil, List.nil_append] at a_is
        specialize h1_ih h a_is
        have i_one : m = 1 := by
          convert hm
        have H := word_side_side_t _ _ _ h2 rfl
        have H : h2.length = 0 := by exact gridt_length_top_bottom_word _ _ _ _ h2 rfl
        simp [H, gridt.length]
        apply h1_ih
        exact b_is
      | m1 :: m2 =>
        rcases splittable_horizontally_of_pg h _ _ a_is (by simp [hi]) (by simp [to_up_plain])
          with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
        · rw [hl]
          have hi1 := h1_ih i1 rfl b_is
          have hi2 : i2.length ≤ h2.length := by
            have H : mid <+: to_over_plain l :=
              (same_time h1 i1).1 rfl (by rw [b_is])
            rcases H with ⟨r, hr⟩
            have rt : is_true r := by
              have H : is_true (to_over_plain l) := to_over_plain_true
              rw [← hr] at H
              exact (is_true_append H).2
            match r_is : r with
            | [] =>
              rw [List.append_nil] at hr
              exact h2_ih i2 rfl hr
            | r1 :: r2 =>
              have i3 := PartialGrid.extend_side_w_len i2 (r1 :: r2)
                rt (by simp)
              specialize h2_ih i3.1 rfl
              rw [← hr] at h2_ih
              simp [] at h2_ih
              rw [i3.2.1]
              apply h2_ih
          simp [gridt.length]
          omega
        rcases baaad with ⟨ db, c1, drest, i1, ⟨long⟩, ⟨db_is⟩, ⟨c_nil⟩, ⟨len⟩⟩
        specialize h1_ih i1 rfl b_is
        simp [gridt.length]
        omega
  | horizontal h1 h2 h1_ih h2_ih =>
    intro a_is b_is
    rename_i i j k l m n o
    match hj : j with
    | [] =>
      rw [to_over_plain_prod, to_over_plain_nil, List.nil_append] at b_is
      have H := word_top_bottom_t _ _ _ h1 rfl
      rw [← H.1] at a_is
      specialize h2_ih h a_is b_is
      have H : h1.length = 0 := gridt_length_side_side_word i [] k l h1 rfl
      simp [H, gridt.length, h2_ih]
    | j1 :: j2 =>
      match hm : m with
      | [] =>
        rw [to_over_plain_mul, to_over_plain_nil, List.append_nil] at b_is
        have H := word_top_bottom_t _ _ _ h2 rfl
        specialize h1_ih h a_is b_is
        have H : h2.length = 0 := gridt_length_side_side_word _ _ _ _ h2 rfl
        simp [H, gridt.length, h1_ih]
      | m1 :: m2 =>
        rw [to_over_plain_prod] at b_is
        rcases splittable_vertically_of_pg' h _ _ b_is (by simp [to_over_plain]) (by simp [to_over_plain])
          with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
        · rw [hl, gridt.length]
          have hone := h1_ih i1 a_is rfl
          have two : i2.length ≤ h2.length := by
            have H2 := (same_time h1 i1).2 rfl (by rw [a_is])
            rcases H2 with ⟨r, hr⟩
            match r with
            | [] =>
              rw [List.nil_append] at hr
              exact h2_ih i2 hr rfl
            | r1 :: r2 =>
              have rf : is_false (r1 :: r2) := by
                have H : is_false (to_up_plain k) := to_up_plain_false
                rw [← hr] at H
                exact (is_false_append H).1
              have H := PartialGrid.extend_bottom_w_len i2
                (r1 :: r2) rf (by simp)
              rcases H with ⟨h3, ⟨len⟩⟩
              rw [len]
              exact h2_ih h3 hr rfl
          omega
        rcases baaad with ⟨db, drest, i1, ⟨len⟩, ⟨e_nil⟩, ⟨d_is⟩, ⟨b2_is⟩⟩
        specialize h1_ih i1 a_is rfl
        simp [gridt.length]
        omega
