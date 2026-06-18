import BraidProject.PartialGrid.ToGrid
import BraidProject.PartialGrid.FrontierPossibilities

namespace Braid

open SignedOptionList
theorem pg_sm_g_eq1 (h : PartialGrid a b c d e) (h1 : GridData a1 b1 g f)
    : toList (FreeGroup.invRev a) = a1 → toList b = b1 →
    h.length ≤ GridData.length h1 := by
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
    simp [partial_grid_rm_top_left_length h ha hb, GridData.length]
  | adjacent i k hd =>
    intro ha hb
    simp [partial_grid_rm_adjacent_length h ha hb, GridData.length]
  | separated i j hd =>
    intro ha hb
    simp [GridData.length]
    simp [partial_grid_rm_separated_length h ha hb hd]
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i i j k l m n o
    intro a_is b_is
    rcases SignedOptionList.toSignedList_eq_to_vertical_edge_plain_prod a_is with one | two | splits
    · have nonsense : to_vertical_edge_plain i = [] := by
        have H : to_vertical_edge_plain ([] : List ℕ) = [] :=  rfl
        convert H
      rw [to_vertical_edge_plain_prod, nonsense, List.append_nil] at a_is
      specialize h2_ih h a_is
      have i_one : i = 1 := by
        convert one
      have H := DeterminativeSpine.one_word h1 i_one
      have H : GridData.length h1 = 0 := by exact DeterminativeSpineLength.one_word h1 one
      simp [H, GridData.length]
      apply h2_ih
      convert b_is
      aesop
    · have nonsense : to_vertical_edge_plain m = [] := by
        have H : to_vertical_edge_plain ([] : List ℕ) = [] :=  rfl
        convert H
      rw [to_vertical_edge_plain_prod, nonsense, List.nil_append] at a_is
      specialize h1_ih h a_is
      have i_one : m = 1 := by
        convert two
      have H := DeterminativeSpine.one_word h2 i_one
      have H : GridData.length h2 = 0 := by exact DeterminativeSpineLength.one_word h2 two
      simp [H, GridData.length]
      apply h1_ih
      exact b_is
    rcases splits with ⟨a1, a2, a1_len, a2_len, H, a1m, a2i⟩
    rcases splittable_horizontally h _ _ H a2_len a1_len
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl]
      have hi1 := h1_ih i1 a2i b_is
      have hi2 : i2.length ≤ GridData.length h2 := by
        have H : SignedOptionList.toSignedList mid <+: to_horizontal_edge_plain k :=
          (same_time h1 i1).1 a2i (by rw [b_is])
        rcases H with ⟨r, hr⟩
        have rt : is_true r := by
          have H : is_true (to_horizontal_edge_plain k) := to_horizontal_edge_plain_true
          rw [← hr] at H
          exact (is_true_of_append H).2
        match r_is : r with
        | [] =>
          rw [List.append_nil] at hr
          exact h2_ih i2 (a1m) hr
        | r1 :: r2 =>
          have i3 := PartialGrid.extend_top_side_w_length i2 (List.map (fun x => (some x.1, x.2)) (r1 :: r2))
            (is_true_map_to_some rt) (by simp)
          specialize h2_ih i3.1 (a1m)
          rw [← hr] at h2_ih
          simp [SignedOptionList.toSignedList] at h2_ih
          rw [i3.2.1]
          exact h2_ih SignedOptionList.toSignedList_add_some_is_self
      simp [GridData.length]
      omega
    rcases baaad with ⟨ db, c1, drest, i1, ⟨long⟩, ⟨db_is⟩, ⟨c_nil⟩, ⟨len⟩⟩
    specialize h1_ih i1 a2i b_is
    simp [GridData.length]
    omega
  | horizontal h1 h2 h1_ih h2_ih =>
    intro a_is b_is
    rename_i i j k l m n o
    rcases SignedOptionList.toSignedList_eq_to_horizontal_edge_plain_prod b_is with one | two | splits
    · have nonsense : to_horizontal_edge_plain j = [] := by
        have H : to_horizontal_edge_plain ([] : List ℕ) = [] :=  rfl
        convert H
      rw [to_horizontal_edge_plain_prod, nonsense, List.nil_append] at b_is
      have i_one : j = 1 := by
        convert one
      have H := DeterminativeSpine.word_one h1 i_one
      rw [← H.2] at a_is
      specialize h2_ih h a_is b_is
      have H : GridData.length h1 = 0 := DeterminativeSpineLength.word_one h1 one
      simp [H, GridData.length, h2_ih]
    · have nonsense : to_horizontal_edge_plain m = [] := by
        have H : to_horizontal_edge_plain ([] : List ℕ) = [] :=  rfl
        convert H
      rw [to_horizontal_edge_plain_prod, nonsense, List.append_nil] at b_is
      have i_one : m = 1 := by
        convert two
      have H := DeterminativeSpine.word_one h2 i_one
      specialize h1_ih h a_is b_is
      have H : GridData.length h2 = 0 := DeterminativeSpineLength.word_one h2 two
      simp [H, GridData.length, h1_ih]
    rcases splits with ⟨b1, b2, b1_len, b2_len, bb1b2, b1j, b2m⟩
    rcases splittable_vertically h _ _ bb1b2 b1_len b2_len
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl, GridData.length]
      have hone := h1_ih i1 a_is b1j
      have two : i2.length ≤ GridData.length h2 := by
        have H2 := (same_time h1 i1).2 (by rw [b1j]; rfl) (by rw [a_is])
        rcases H2 with ⟨r, hr⟩
        match r with
        | [] =>
          rw [List.nil_append] at hr
          exact h2_ih i2 hr b2m
        | r1 :: r2 =>
          have rf : is_false (r1 :: r2) := by
            have H : is_false (to_vertical_edge_plain l) := to_vertical_edge_plain_false
            rw [← hr] at H
            exact (is_false_of_append H).1
          have H := PartialGrid.extend_left_side_w_length i2
            (List.map (fun x => (some x.1, x.2)) (r1 :: r2)) (is_false_map_to_some rf) (by simp)
          rcases H with ⟨h3, ⟨len⟩⟩
          rw [len]
          have hk : SignedOptionList.toSignedList (List.map (fun x ↦ (some x.1, x.2)) (r1 :: r2) ++ mid) = to_vertical_edge_plain l := by
            rw [SignedOptionList.toSignedList_append]
            rw [← hr]
            apply (List.append_left_inj (SignedOptionList.toSignedList mid)).mpr
            simp [SignedOptionList.toSignedList]
            exact SignedOptionList.toSignedList_add_some_is_self
          exact h2_ih h3 hk b2m
      omega
    rcases baaad with ⟨db, drest, i1, ⟨len⟩, ⟨e_nil⟩, ⟨d_is⟩, ⟨b2_is⟩⟩
    specialize h1_ih i1 a_is b1j
    simp [GridData.length]
    omega

-- theorem split_it_helper (h : to_horizontal_edge [i] ++ ra = to_horizontal_edge a1) : ∃ rra, a1 = FreeMonoid.of i * rra := by
--   induction a1  with
--   | nil => simp at h
--   | cons head tail ih =>
--     simp only [to_horizontal_edge, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
--       List.cons.injEq, Prod.mk.injEq, Option.some.injEq, and_true] at h
--     use tail
--     rw [h.1]
--     rfl

theorem helper_pg_empty (h : PartialGrid a b c d e) : SignedOptionList.toSignedList a = [] → SignedOptionList.toSignedList b =  [] →
    SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList e = [] ∧ h.length = 0 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [PartialGrid.length, SignedOptionList.toSignedList]
    | top_bottom i => simp [PartialGrid.length, SignedOptionList.toSignedList]
    | sides i => simp [PartialGrid.length, SignedOptionList.toSignedList]
    | top_left i =>
      intro ha
      simp [SignedOptionList.toSignedList, to_vertical_edge] at ha
    | adjacent i k h =>
      intro ha
      simp [SignedOptionList.toSignedList, to_vertical_edge] at ha
    | separated i j h =>
      intro ha
      simp [SignedOptionList.toSignedList, to_vertical_edge] at ha
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i f g h i j k l m
    intro f_is gj_is
    rw [SignedOptionList.toSignedList_append] at gj_is
    apply List.append_eq_nil_iff.mp at gj_is
    specialize g1_ih f_is gj_is.1
    specialize g2_ih g1_ih.2.1 gj_is.2
    rw [SignedOptionList.toSignedList_append, PartialGrid.length]
    aesop
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rename_i f g i j k l m n o
    intro f_is gl_is
    rw [SignedOptionList.toSignedList_append] at gl_is
    apply List.append_eq_nil_iff.mp at gl_is
    specialize g1_ih f_is gl_is.1
    specialize g2_ih g1_ih.2.1 gl_is.2
    rw [PartialGrid.length]
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i f g h i j k l m
    intro jf_is g_is
    rw [SignedOptionList.toSignedList_append] at jf_is
    apply List.append_eq_nil_iff.mp at jf_is
    specialize g1_ih jf_is.2 g_is
    specialize g2_ih jf_is.1 g1_ih.1
    rw [SignedOptionList.toSignedList_append, PartialGrid.length]
    aesop
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i f g i j k l m n o
    intro lf_is g_is
    rw [SignedOptionList.toSignedList_append] at lf_is
    apply List.append_eq_nil_iff.mp at lf_is
    specialize g1_ih lf_is.2 g_is
    specialize g2_ih lf_is.1 g1_ih.1
    rw [PartialGrid.length]
    aesop

theorem empty_rm_pg_len (h : PartialGrid a b c d e) : SignedOptionList.toSignedList a = [] → SignedOptionList.toSignedList b =  [] →
    h.length = 0 := by
  have H := helper_pg_empty h
  aesop

open SignedList SignedOptionList PartialGrid FrontierPossibilitiesEpsilonRemoved
theorem partial_grid_rm_top_bottom_length (h : PartialGrid a b c d e) (ha : SignedOptionList.toSignedList a = []) (hb : SignedOptionList.toSignedList b = [(i, true)]) :
    SignedOptionList.toSignedList c <+: [(i, true)] ∧ SignedOptionList.toSignedList e = [] ∧ h.length = 0 := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [PartialGrid.length, SignedOptionList.toSignedList]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := helper_pg_empty g1 ha b1_is
      simp_all [PartialGrid.length]
    simp_all
    have H := helper_pg_empty g2 g1_ih.2.1 b2_is
    simp_all [PartialGrid.length]
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨b1_is, b2_is⟩ | ⟨b1_is, b2_is⟩
    · have H := helper_pg_empty g1 ha b1_is
      simp_all [PartialGrid.length]
    simp_all
    have H := helper_pg_empty g2 g1_ih.2.1 b2_is
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at ha
    simp at ha
    specialize g1_ih ha.2 hb
    rcases prefix_of_singleton g1_ih.1 with one | two
    · have H := helper_pg_empty g2 ha.1 one
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at ha
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
  (ha : SignedOptionList.toSignedList a = []) (hb : SignedOptionList.toSignedList b = [(i1, true), (i2, true)]) :
    SignedOptionList.toSignedList c <+: [(i1, true), (i2, true)] ∧ SignedOptionList.toSignedList e = [] ∧ h.length = 0 := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [SignedOptionList.toSignedList]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
    rename_i i j k l m n o p
    match hn : SignedOptionList.toSignedList j with
    | [] =>
      rw [hn, List.nil_append] at hb
      simp_all
      have H := helper_pg_empty g1 ha hn
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match hi : SignedOptionList.toSignedList m with
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
        have H : SignedOptionList.toSignedList k = [(i1, true)] := by
          have H := empty_generator g1 ha hn
          simp at H
          exact H.1
        rw [H]
        exact (List.prefix_append_right_inj [(i1, true)]).mpr H1.1
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
    rename_i i j k l m n o p
    match hn : SignedOptionList.toSignedList i with
    | [] =>
      rw [hn, List.nil_append] at hb
      simp_all
      have H := helper_pg_empty g1 ha hn
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match hi : SignedOptionList.toSignedList m with
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
    rw [SignedOptionList.toSignedList_append] at ha
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
    rw [SignedOptionList.toSignedList_append] at ha
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

theorem partial_grid_rm_side_length (h : PartialGrid a b c d e) (ha : SignedOptionList.toSignedList a = [(i, false)]) (hb : SignedOptionList.toSignedList b = []) :
    SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList e <:+ [(i, false)] ∧ h.length = 0 := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [PartialGrid.length, SignedOptionList.toSignedList]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp [SignedOptionList.toSignedList_append] at hb
    simp_all
    rcases suffix_of_singleton g1_ih.2.1
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    simp [SignedOptionList.toSignedList_append] at hb
    simp_all
    rcases suffix_of_singleton g1_ih.2.1
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      have H := helper_pg_empty g2 a1_is g1_ih.1
      simp_all [PartialGrid.length]
    have H := helper_pg_empty g1 a2_is hb
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at ha
    rcases List.append_eq_singleton_iff.mp ha with ⟨a1_is, a2_is⟩ | ⟨a1_is, a2_is⟩
    · simp_all
      have H := helper_pg_empty g2 a1_is g1_ih.1
      simp_all [PartialGrid.length]
    have H := helper_pg_empty g1 a2_is hb
    simp_all [PartialGrid.length]

theorem partial_grid_rm_side_length_w (h : PartialGrid a b c d e)
    (ha : SignedOptionList.toSignedList a = [(i1, false), (i2, false)]) (hb : SignedOptionList.toSignedList b = []) :
    SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList e <:+ [(i1, false), (i2, false)] ∧ h.length = 0 := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [SignedOptionList.toSignedList]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp [SignedOptionList.toSignedList_append] at hb
    simp_all
    rcases suffix_of_pair g1_ih.2.1 with one | two | three
    · have H := helper_pg_empty g2 (by assumption) hb.2
      simp_all [PartialGrid.length]
    · have H := partial_grid_rm_side_length g2 two hb.2
      simp_all [PartialGrid.length]
      change _ <:+ [(i1, false)] ++ [(i2, false)]
      apply suffix_of_append H.2.1
    simp_all [PartialGrid.length]
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    simp [SignedOptionList.toSignedList_append] at hb
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
    rw [SignedOptionList.toSignedList_append] at ha
    rename_i i j k l m n o p q
    match hn : SignedOptionList.toSignedList n with
    | [] =>
      rw [hn, List.nil_append] at ha
      simp_all
      have H := helper_pg_empty g2 hn g1_ih.1
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match hi : SignedOptionList.toSignedList i with
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
    rw [SignedOptionList.toSignedList_append] at ha
    rename_i i j k l m n o p
    match hn : SignedOptionList.toSignedList m with
    | [] =>
      rw [hn, List.nil_append] at ha
      simp_all
      have H := helper_pg_empty g2 hn g1_ih.1
      simp_all [PartialGrid.length]
    | n1 :: n2 =>
      match hi : SignedOptionList.toSignedList i with
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
        have H : SignedOptionList.toSignedList l = [(i2, false)] := by
          have H := generator_empty g1 hb hi
          simp at H
          exact H.2
        rw [H]
        exact List.suffix_append_right H1.2.1

theorem partial_grid_rm_top_left_length (h : PartialGrid a b c d e) (ha : SignedOptionList.toSignedList a = [(i, false)]) (hb : SignedOptionList.toSignedList b = [(i, true)]) :
    SignedOptionList.toSignedList c <+: [(i, true)] ∧ SignedOptionList.toSignedList e <:+ [(i, false)] ∧ h.length ≤ 1 := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [PartialGrid.length, SignedOptionList.toSignedList]
    aesop
  | empty a b ha ha1 hb hb =>
    simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
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
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
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
    rw [SignedOptionList.toSignedList_append] at ha
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
    rw [SignedOptionList.toSignedList_append] at ha
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
    (ha : SignedOptionList.toSignedList a = [(i, false)]) (hb : SignedOptionList.toSignedList b = [(k, true)]) :
    SignedOptionList.toSignedList c <+: [(k, true), (i, true)] ∧ SignedOptionList.toSignedList e <:+ [(k, false), (i, false)] ∧ h.length ≤ 1 := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [PartialGrid.length, SignedOptionList.toSignedList]
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
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
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
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
    rw [SignedOptionList.toSignedList_append] at ha
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
    have H1 := empty_generator g1 a2_is hb
    have H := partial_grid_rm_top_bottom_length g1 a2_is hb
    simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at ha
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
      simp_all
    simp_all

theorem partial_grid_rm_separated_length (h : PartialGrid a b c d e)
    (ha : SignedOptionList.toSignedList a = [(i, false)]) (hb : SignedOptionList.toSignedList b = [(j, true)]) (hd : i.dist j > 1) :
    SignedOptionList.toSignedList c <+: [(j, true)] ∧ SignedOptionList.toSignedList e <:+ [(i, false)] ∧ h.length ≤ 1 := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [PartialGrid.length, SignedOptionList.toSignedList]
    aesop
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
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
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rw [SignedOptionList.toSignedList_append] at hb
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
    rw [SignedOptionList.toSignedList_append] at ha
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
    rw [SignedOptionList.toSignedList_append] at ha
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
  | cons head tail ih =>
    simp
    change is_true ([(some head.1, head.2)] ++ _)
    apply is_true_append
    · have H := (is_true_of_cons h).1
      intro a ha
      simp at ha
      specialize H head (by simp)
      aesop
    exact ih (is_true_of_cons h).2

def is_false_map_to_some {r : List (ℕ × Bool)} (h : is_false r) :
    is_false (List.map (fun x => (some x.1, x.2)) r) := by
  induction r with
  | nil =>
    simp [is_false_nil]
  | cons head tail ih =>
    simp
    change is_false ([(some head.1, head.2)] ++ _)
    apply is_false_append
    · have H := (is_false_of_cons h).1
      intro a ha
      simp at ha
      specialize H head (by simp)
      aesop
    exact ih (is_false_of_cons h).2

def to_horizontal_edge_plain_true : is_true (to_horizontal_edge_plain l) := by
  induction l with
  | nil =>
    simp [to_horizontal_edge_plain]
  | cons head tail ih =>
    simp [to_horizontal_edge_plain]
    change is_true ([(head, true)] ++ _)
    apply is_true_append
    · intro a ha
      simp at ha
      aesop
    exact ih

def to_vertical_edge_plain_false : is_false (to_vertical_edge_plain l) := by
  induction l with
  | nil =>
    simp [to_vertical_edge_plain]
  | cons head tail ih =>
    simp [to_vertical_edge_plain]
    apply is_false_append
    · intro a ha
      simp at ha
      rcases ha with ⟨a1, ha1, a_is⟩
      simp [← a_is]
    intro a ha
    simp at ha
    aesop

theorem SignedOptionList.toSignedList_add_some_is_self {r2 : List (α × Bool)} : SignedOptionList.toSignedList (List.map (fun x ↦ (some x.1, x.2)) r2) = r2 := by
  induction r2 with
  | nil => simp
  | cons head tail ih =>
    simp [SignedOptionList.toSignedList, ih]

open GridData in
theorem pg_sm_g_eq1 (h : PartialGrid a b c d e) (h1 : GridData a1 b1 g f)
    : SignedOptionList.toSignedList a = to_vertical_edge_plain a1 → SignedOptionList.toSignedList b = to_horizontal_edge_plain b1 → h.length ≤ GridData.length h1 := by
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
    simp [partial_grid_rm_top_left_length h ha hb, GridData.length]
  | adjacent i k hd =>
    intro ha hb
    simp [partial_grid_rm_adjacent_length h ha hb, GridData.length]
  | separated i j hd =>
    intro ha hb
    simp [GridData.length]
    simp [partial_grid_rm_separated_length h ha hb hd]
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i i j k l m n o
    intro a_is b_is
    rcases SignedOptionList.toSignedList_eq_to_vertical_edge_plain_prod a_is with one | two | splits
    · have nonsense : to_vertical_edge_plain i = [] := by
        have H : to_vertical_edge_plain ([] : List ℕ) = [] :=  rfl
        convert H
      rw [to_vertical_edge_plain_prod, nonsense, List.append_nil] at a_is
      specialize h2_ih h a_is
      have i_one : i = 1 := by
        convert one
      have H := DeterminativeSpine.one_word h1 i_one
      have H : GridData.length h1 = 0 := by exact DeterminativeSpineLength.one_word h1 one
      simp [H, GridData.length]
      apply h2_ih
      convert b_is
      aesop
    · have nonsense : to_vertical_edge_plain m = [] := by
        have H : to_vertical_edge_plain ([] : List ℕ) = [] :=  rfl
        convert H
      rw [to_vertical_edge_plain_prod, nonsense, List.nil_append] at a_is
      specialize h1_ih h a_is
      have i_one : m = 1 := by
        convert two
      have H := DeterminativeSpine.one_word h2 i_one
      have H : GridData.length h2 = 0 := by exact DeterminativeSpineLength.one_word h2 two
      simp [H, GridData.length]
      apply h1_ih
      exact b_is
    rcases splits with ⟨a1, a2, a1_len, a2_len, H, a1m, a2i⟩
    rcases splittable_horizontally h _ _ H a2_len a1_len
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl]
      have hi1 := h1_ih i1 a2i b_is
      have hi2 : i2.length ≤ GridData.length h2 := by
        have H : SignedOptionList.toSignedList mid <+: to_horizontal_edge_plain k :=
          (same_time h1 i1).1 a2i (by rw [b_is])
        rcases H with ⟨r, hr⟩
        have rt : is_true r := by
          have H : is_true (to_horizontal_edge_plain k) := to_horizontal_edge_plain_true
          rw [← hr] at H
          exact (is_true_of_append H).2
        match r_is : r with
        | [] =>
          rw [List.append_nil] at hr
          exact h2_ih i2 (a1m) hr
        | r1 :: r2 =>
          have i3 := PartialGrid.extend_top_side_w_length i2 (List.map (fun x => (some x.1, x.2)) (r1 :: r2))
            (is_true_map_to_some rt) (by simp)
          specialize h2_ih i3.1 (a1m)
          rw [← hr] at h2_ih
          simp [SignedOptionList.toSignedList] at h2_ih
          rw [i3.2.1]
          exact h2_ih SignedOptionList.toSignedList_add_some_is_self
      simp [GridData.length]
      omega
    rcases baaad with ⟨ db, c1, drest, i1, ⟨long⟩, ⟨db_is⟩, ⟨c_nil⟩, ⟨len⟩⟩
    specialize h1_ih i1 a2i b_is
    simp [GridData.length]
    omega
  | horizontal h1 h2 h1_ih h2_ih =>
    intro a_is b_is
    rename_i i j k l m n o
    rcases SignedOptionList.toSignedList_eq_to_horizontal_edge_plain_prod b_is with one | two | splits
    · have nonsense : to_horizontal_edge_plain j = [] := by
        have H : to_horizontal_edge_plain ([] : List ℕ) = [] :=  rfl
        convert H
      rw [to_horizontal_edge_plain_prod, nonsense, List.nil_append] at b_is
      have i_one : j = 1 := by
        convert one
      have H := DeterminativeSpine.word_one h1 i_one
      rw [← H.2] at a_is
      specialize h2_ih h a_is b_is
      have H : GridData.length h1 = 0 := DeterminativeSpineLength.word_one h1 one
      simp [H, GridData.length, h2_ih]
    · have nonsense : to_horizontal_edge_plain m = [] := by
        have H : to_horizontal_edge_plain ([] : List ℕ) = [] :=  rfl
        convert H
      rw [to_horizontal_edge_plain_prod, nonsense, List.append_nil] at b_is
      have i_one : m = 1 := by
        convert two
      have H := DeterminativeSpine.word_one h2 i_one
      specialize h1_ih h a_is b_is
      have H : GridData.length h2 = 0 := DeterminativeSpineLength.word_one h2 two
      simp [H, GridData.length, h1_ih]
    rcases splits with ⟨b1, b2, b1_len, b2_len, bb1b2, b1j, b2m⟩
    rcases splittable_vertically h _ _ bb1b2 b1_len b2_len
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl, GridData.length]
      have hone := h1_ih i1 a_is b1j
      have two : i2.length ≤ GridData.length h2 := by
        have H2 := (same_time h1 i1).2 (by rw [b1j]; rfl) (by rw [a_is])
        rcases H2 with ⟨r, hr⟩
        match r with
        | [] =>
          rw [List.nil_append] at hr
          exact h2_ih i2 hr b2m
        | r1 :: r2 =>
          have rf : is_false (r1 :: r2) := by
            have H : is_false (to_vertical_edge_plain l) := to_vertical_edge_plain_false
            rw [← hr] at H
            exact (is_false_of_append H).1
          have H := PartialGrid.extend_left_side_w_length i2
            (List.map (fun x => (some x.1, x.2)) (r1 :: r2)) (is_false_map_to_some rf) (by simp)
          rcases H with ⟨h3, ⟨len⟩⟩
          rw [len]
          have hk : SignedOptionList.toSignedList (List.map (fun x ↦ (some x.1, x.2)) (r1 :: r2) ++ mid) = to_vertical_edge_plain l := by
            rw [SignedOptionList.toSignedList_append]
            rw [← hr]
            apply (List.append_left_inj (SignedOptionList.toSignedList mid)).mpr
            simp [SignedOptionList.toSignedList]
            exact SignedOptionList.toSignedList_add_some_is_self
          exact h2_ih h3 hk b2m
      omega
    rcases baaad with ⟨db, drest, i1, ⟨len⟩, ⟨e_nil⟩, ⟨d_is⟩, ⟨b2_is⟩⟩
    specialize h1_ih i1 a_is b1j
    simp [GridData.length]
    omega
