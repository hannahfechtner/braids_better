import BraidProject.SimplerPG.SimplePG_split
import BraidProject.GridsTwo_C
import BraidProject.Cancellability_C
set_option maxHeartbeats 1000000


theorem to_up_plain_inj (h : to_up_plain a = to_up_plain b) : a = b := by
  simp [to_up_plain] at h
  exact (List.map_inj_right (by simp)).mp h

theorem to_over_plain_inj (h : to_over_plain a = to_over_plain b) : a = b := by
  simp [to_over_plain] at h
  exact (List.map_inj_right (by simp)).mp h

theorem helper_pg_empty (h : PartialGrid a b c d e) : a = [] →  b =  [] →
    c = [] ∧  e = [] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length, to_up_plain]
    | top_bottom i => simp [PartialGrid.length, to_over_plain]
    | sides i => simp [PartialGrid.length, to_up_plain]
    | top_left i =>
      intro ha
      simp [to_up_plain] at ha
    | adjacent i k h =>
      intro ha
      simp [to_up_plain] at ha
    | separated i j h =>
      intro ha
      simp [to_up_plain] at ha
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i f g h i j k l m
    intro f_is gj_is
    apply List.append_eq_nil_iff.mp at gj_is
    specialize g1_ih f_is gj_is.1
    specialize g2_ih g1_ih.2.1 gj_is.2
    rw [PartialGrid.length]
    aesop
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i f g i j k l m n o
    intro f_is gl_is
    apply List.append_eq_nil_iff.mp at gl_is
    specialize g1_ih f_is gl_is.1
    specialize g2_ih g1_ih.2.1 gl_is.2
    rw [PartialGrid.length]
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i f g h i j k l m
    intro jf_is g_is
    apply List.append_eq_nil_iff.mp at jf_is
    specialize g1_ih jf_is.2 g_is
    specialize g2_ih jf_is.1 g1_ih.1
    rw [PartialGrid.length]
    aesop
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i f g i j k l m n o
    intro lf_is g_is
    apply List.append_eq_nil_iff.mp at lf_is
    specialize g1_ih lf_is.2 g_is
    specialize g2_ih lf_is.1 g1_ih.1
    rw [PartialGrid.length]
    aesop

theorem empty_rm_pg_len (h : PartialGrid a b c d e) : a = [] →  b =  [] →
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

theorem List.prefix_of_append_mine {a b c : List α} (h : a <+: b ++ c) : a <+: b ∨ ∃ a2, a2.length > 0 ∧
  a = b ++ a2 ∧ a2 <+: c := by
  rcases h with ⟨r, hr⟩
  rcases List.append_eq_append_iff.mp hr with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · match tm with
    | [] => aesop
    | t1 :: t2 =>
      left
      rw [s1]
      exact prefix_append a (t1 :: t2)
  match fm with
  | [] => aesop
  | f1 :: f2 =>
    right
    use f1 :: f2
    constructor
    · simp
    constructor
    · exact s1
    simp [s2]

theorem helper_bajillion {q m2 : List α}
    (ha :  a <:+ to_up_plain q ++ to_up_plain (m1 :: m2)) :
     a <:+ to_up_plain (m1 :: m2) ∨
    ∃ (a1 a2 : List (α × Bool)), a1.length > 0 ∧ a = a1 ++ a2 ∧
    a2 = to_up_plain (m1 :: m2) ∧  a1 <:+ to_up_plain q := by
  rcases List.suffix_of_append ha with one | two
  · left
    exact one
  rcases two with ⟨a1, a1_len, a_is, a1_suff⟩
  match a1 with
  | [] => left; simp [a_is]
  | a3 :: a4 =>
    right
    use a3 :: a4, to_up_plain (m1 :: m2)

theorem helper_kajillion {α : Type} {n q : List α} {b : List (α × Bool)} (h :  b <+: to_over_plain n ++ to_over_plain q) (hn : n.length > 0):
  b <+: to_over_plain n ∨ ∃ (b₁ b₂ : List (α × Bool)), b₁.length > 0 ∧ b₂.length > 0 ∧ b = b₁ ++ b₂ ∧
    b₁ = to_over_plain n ∧  b₂ <+: to_over_plain q := by
  rcases List.prefix_of_append_mine h with one | two
  · left
    exact one
  rcases two with ⟨b1, b1_len, b_is, b1_pref⟩
  match b1 with
  | [] => left; simp [b_is]
  | b11 :: b12 =>
    right
    use to_over_plain n, b11 :: b12
    constructor
    · simp [hn, to_over_plain]
    aesop

open PartialGrid in
theorem frontier_options_from_vertical
    (h1 : PartialGrid a b mid d2 e2)
    (i1 : PartialGrid a2 b mid4 e5 d5) (i2 : PartialGrid a1 mid4 mid d4 e4)
    (hf : d4 ++ e4 ++ e5 ++ d5 = d2 ++ e2) :
    (d2 = d4 ++ e4 ++ e5 ∧ d5 = e2) ∨ (d2 = d4 ∧ e5 = [] ∧ e2 = e4 ++ d5) := by
  rcases PartialGrid.middle_frontier_nil_or_caps i1 with ⟨⟨e5_nil⟩⟩ | ⟨fronte5, mide5, caboosee5, ⟨spece5⟩⟩
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

open PartialGrid

theorem frontier_options_from_horizontal (h1 : PartialGrid a b mid d2 e2)
    (i1 : PartialGrid a b1 d3 e3 mid1) (i2 : PartialGrid mid1 b2 d4 e4 e2)
    (hf : mid ++ d2 = d3 ++ (e3 ++ (d4 ++ e4))) :
    (mid = d3 ++ e3 ++ d4 ∧ e3 = []) ∨ (mid = d3 ∧ d2 = e3 ++ d4 ++ e4) := by
  have mid_t : is_true mid := h1.bottom_frontier_is_true
  have d3_t : is_true d3 := i1.bottom_frontier_is_true
  have d4_t : is_true d4 := i2.bottom_frontier_is_true
  have mid1_f : is_false mid1 := i2.left_frontier_is_false
  rcases middle_frontier_nil_or_caps h1 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, middled2, caboosed2, ⟨specd2⟩⟩
  · left
    rw [d2_nil, List.append_nil] at hf
    rcases middle_frontier_nil_or_caps i1 with ⟨⟨e3_nil⟩⟩ | ⟨fronte3, middlee3, caboosee3, ⟨spece3⟩⟩
    · rw [e3_nil, List.nil_append] at hf
      rcases middle_frontier_nil_or_caps i2 with ⟨⟨e4_nil⟩⟩ | ⟨fronte4, middlee4, caboosee4, ⟨spece4⟩⟩
      · rw [e4_nil, List.append_nil] at hf
        aesop
      rw [spece4] at hf
      rw [hf] at mid_t
      specialize mid_t (fronte4, false) ⟨(by simp)⟩
      simp at mid_t
      exact mid_t.1.elim
    rw [spece3] at hf
    rw [hf] at mid_t
    specialize mid_t (fronte3, false) ⟨by simp⟩
    simp at mid_t
    exact mid_t.1.elim
  rcases middle_frontier_nil_or_caps i1 with ⟨⟨e3_nil⟩⟩ | ⟨fronte3, middlee3, caboosee3, ⟨spece3⟩⟩
  · left
    rw [e3_nil, List.nil_append] at hf
    simp [e3_nil]
    rw [← List.append_assoc] at hf
    rcases List.append_eq_append_iff.mp hf with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
    · match tm with
      | [] => aesop
      | t1 :: t2 =>
        rw [specd2] at s2
        simp at s2
        have H : is_true (d3 ++ d4) := is_true_of_true_true d3_t d4_t
        rw [s1, ← s2.1] at H
        specialize H (frontd2, false) ⟨by simp⟩
        simp at H
        exact H.1.elim
    match fm with
    | [] => aesop
    | f1 :: f2 =>
      rw [specd2] at s2
      rcases middle_frontier_nil_or_caps i2 with ⟨⟨e4_nil⟩⟩ | ⟨fronte4, middlee4, caboosee4, ⟨spece4⟩⟩
      · aesop
      rw [spece4] at s2
      simp at s2
      rw [← s2.1] at s1
      rw [s1] at mid_t
      specialize mid_t (fronte4, false) ⟨by simp⟩
      simp at mid_t
      exact mid_t.1.elim
  right
  rcases List.append_eq_append_iff.mp hf with
    ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · match tm with
    | [] => aesop
    | t1 :: t2 =>
      rw [specd2] at s2
      simp at s2
      rw [s1, ← s2.1] at d3_t
      specialize d3_t (frontd2, false) ⟨by simp⟩
      simp at d3_t
      exact d3_t.1.elim
  match fm with
  | [] => aesop
  | f1 :: f2 =>
    rw [specd2] at s2
    rcases middle_frontier_nil_or_caps i1 with ⟨⟨e3_nil⟩⟩ | ⟨fronte3, middlee3, caboosee3, ⟨spece3⟩⟩
    · aesop
    rw [spece3] at s2
    simp at s2
    rw [s1, ← s2.1] at mid_t
    specialize mid_t (fronte3, false) ⟨by simp⟩
    simp at mid_t
    exact mid_t.1.elim

theorem partial_grid_rm_empty_helper (h : PartialGrid a b c d e) :  a = [] →  b = [] →
    ( c = [] ∧  d = [] ∧  e = []) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all
    | sides i => simp_all
    | top_left i => simp_all [to_up_plain]
    | adjacent i k h => simp_all [to_up_plain]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih => simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all
  | vertical_append g1 g2 h g1_ih g2_ih => simp_all

theorem partial_grid_rm_top_helper (h : PartialGrid a b c d e) : a = [] → b = [(i, true)] →
    (c = [(i, true)] ∧ d = [] ∧  e = []) ∨
    ( c = [] ∧  d = [(i, true)] ∧  e = []) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all
    | sides i => simp_all
    | top_left i => simp_all [to_up_plain]
    | adjacent i k h => simp_all [to_up_plain]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    intro j_is kn_is
    rcases List.append_eq_singleton_iff.mp kn_is with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_empty_helper g1 j_is k_is
      simp_all
    simp_all only [true_and, List.ne_cons_self, false_and, and_false, or_false,
      forall_const, IsEmpty.forall_iff, imp_self, List.append_nil,
      List.cons_append, List.nil_append, List.cons.injEq]
    have H := partial_grid_rm_empty_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    intro j_is ko_is
    rcases List.append_eq_singleton_iff.mp ko_is with
      ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_empty_helper g1 j_is k_is
      simp_all
    have hn : n = [] := by aesop
    have H := partial_grid_rm_empty_helper g2 hn o_is
    simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    intro oj_is k_is
    simp at oj_is
    specialize g1_ih oj_is.2 k_is
    rcases g1_ih with h1 | h2
    · specialize g2_ih oj_is.1 h1.1
      rcases g2_ih with h3 | h4
      · simp_all
      simp_all
    have H := partial_grid_rm_empty_helper g2 oj_is.1 h2.1
    simp_all

theorem partial_grid_rm_top_helper_w (h : PartialGrid a b c d e)
    (h1 : b = [(i, true), (j, true)]) (h2 : a = []) :
    (c = [] ∧ d = [(i, true), (j, true)] ∧ e = []) ∨
    (c = [(i, true)] ∧ d = [(j, true)] ∧ e = []) ∨
    (c = [(i, true), (j, true)] ∧ d = [] ∧ e = []) := by
  change _ = [(i, true)] ++ [(j, true)] at h1
  rcases splittable_vertically_of_pg' h _ _ h1 (by simp) (by simp) with
    ⟨mid, d1, e1, d2, e2, i1, i2, ⟨long⟩, len⟩ | baaad
  · have H := partial_grid_rm_top_helper i1 h2 rfl
    have hmid : mid = [] := by aesop
    have H2 := partial_grid_rm_top_helper i2 hmid rfl
    have H : [(i, true), (j, true)] = c ++ d := by
      simp at long
      rcases H with h3 | h4
      · rcases H2 with h5 | h6
        · simp [h3, h5] at long
          exact long.symm
        simp [h3, h6] at long
        exact long.symm
      rcases H2 with h7 | h8
      · simp [h4, h7] at long
        exact long.symm
      simp [h4, h8] at long
      exact long.symm
    match hc : c with
    | [] =>
      match hd : d with
      | [] => simp [hc, hd] at H
      | d1 :: d2 => aesop
    | c1 :: c2 =>
      match hd : d with
      | [] =>
        simp_all
        aesop
      | d1 :: d2 =>
        right; left
        have hl := congr_arg List.length H
        simp at hl
        have hc2 : c2.length = 0 := by omega
        aesop
  rcases baaad with ⟨db, c1, i1, ⟨d_is⟩, ⟨db_is⟩, ⟨d_is'⟩, ⟨a_is⟩⟩
  have H := partial_grid_rm_top_helper i1 h2 rfl
  aesop

theorem partial_grid_rm_side_helper (h : PartialGrid a b c d e)
    (h1 : a = [(i, false)]) (h2 : b = []) :
    (c = [] ∧ d = [(i, false)] ∧ e = []) ∨
    (c = [] ∧ d = [] ∧ e = [(i, false)]) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all
    | sides i => simp_all
    | top_left i => simp_all [to_over_plain]
    | adjacent i k h => simp_all [to_over_plain]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    simp at h2
    specialize g1_ih h1 h2.1
    rcases g1_ih with h3 | h4
    · simp_all
      have H := partial_grid_rm_empty_helper g2 h3.2.2 h2.2
      simp_all
    simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · simp_all
      have H := partial_grid_rm_empty_helper g2 n_is g1_ih.1
      simp_all
    have H := partial_grid_rm_empty_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · simp_all
      have l_is : l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 o_is l_is
      simp_all
    have H := partial_grid_rm_empty_helper g1 j_is h2
    simp_all

theorem partial_grid_rm_side_helper_w (h : PartialGrid a b c d e)
    (h1 : a = [(i, false), (j, false)]) (h2 : b = []) :
    (c = [] ∧ d = [(i, false), (j, false)] ∧ e = []) ∨
    (c = [] ∧ d = [(i, false)] ∧ e = [(j, false)]) ∨
    (c = [] ∧ d = [] ∧ e = [(i, false), (j, false)]) := by
  change _ = [(i, false)] ++ [(j, false)] at h1
  rcases splittable_horizontally_of_pg h _ _ h1 (by simp) (by simp) with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨long⟩, len⟩ | baaad
  · have H := partial_grid_rm_side_helper i1 rfl h2
    have hmid : mid = [] := by aesop
    have H2 := partial_grid_rm_side_helper i2 rfl hmid
    have H : [(i, false), (j, false)] = d ++ e := by
      simp at long
      aesop
    match hd : d with
    | [] => aesop
    | d1 :: d2 =>
      match he : e with
      | [] => aesop
      | e1 :: e2 =>
        rcases List.append_eq_len_two (by simp [hd]) (by simp [he]) H.symm
        · rename_i d_is e_is
          rw [d_is, e_is]
          simp
          cases H2
          · rename_i hi
            exact hi.1
          rename_i hi
          exact hi.1
  rcases baaad with ⟨db, c1, drest, i1, ⟨d_is⟩, ⟨db_is⟩, ⟨c_nil⟩, len⟩
  have H := partial_grid_rm_side_helper i1 rfl h2
  aesop

theorem partial_grid_rm_top_left_helper (h : PartialGrid a b c d e) (h1 : a = [(i, false)])
  (h2 : b = [(i, true)]) : (c = [] ∧ d = [] ∧ e = []) ∨
  (c = [] ∧ d = [(i, false), (i, true)] ∧ e = []) := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [to_up_plain, to_over_plain]
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_empty_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    have n_is : n = [] := by aesop
    have H := partial_grid_rm_empty_helper g2 n_is o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 n_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 o_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
    rcases H with h3 | h4
    · aesop
    have H := partial_grid_rm_side_helper g2 o_is h4.1
    aesop

theorem partial_grid_rm_adjacent_helper (h : PartialGrid a b c d e) (h1 : a = [(i, false)])
  (h2 : b = [(j, true)]) (hij : i.dist j = 1): (c = [] ∧ d = [(i, false), (j, true)] ∧ e = []) ∨
  (c = [] ∧ d = [(j, true), (i, true), (j, false), (i, false)] ∧ e = [])  ∨
  (c = [] ∧ d = [(j, true), (i, true), (j, false)] ∧ e = [(i, false)]) ∨
  (c = [] ∧ d = [(j, true), (i, true)] ∧ e = [(j, false), (i, false)]) ∨
  (c = [(j, true)] ∧ d = [(i, true), (j, false), (i, false)] ∧ e = []) ∨
  (c = [(j, true)] ∧ d = [(i, true), (j, false)] ∧ e = [(i, false)]) ∨
  (c = [(j, true)] ∧ d = [(i, true)] ∧ e = [(j, false), (i, false)]) ∨
  (c = [(j, true), (i, true)] ∧ d = [(j, false), (i, false)] ∧ e = []) ∨
  (c = [(j, true), (i, true)] ∧ d = [(j, false)] ∧ e = [(i, false)]) ∨
  (c = [(j, true), (i, true)] ∧ d = [] ∧ e = [(j, false), (i, false)]) := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [to_up_plain, to_over_plain]
    rename_i h
    apply or_dist_iff.mpr at h
    aesop
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_side_helper_w g2 g1_ih.2 n_is
    rcases H with h1 | h2 | h3
    · aesop
    · simp_all
    aesop
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    simp_all
    rename_i j'
    have H :  n = [] ∨  n = [(i, false)] ∨
       n = [(j', false), (i, false)] := by aesop
    rcases H with h3 | h4 | h5
    · have H := partial_grid_rm_empty_helper g2 h3 o_is
      aesop
    · have H := partial_grid_rm_side_helper g2 h4 o_is
      aesop
    have H := partial_grid_rm_side_helper_w g2 h5 o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      simp_all
      have H := partial_grid_rm_top_helper_w g2 g1_ih.1 n_is
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i k l m n o p q r s
    rcases List.append_eq_singleton_iff.mp h1 with ⟨p_is, k_is⟩ | ⟨p_is, k_is⟩
    · specialize g1_ih k_is h2
      have H :  m = [] ∨  m = [(j, true)] ∨  m = [(j, true), (i, true)] := by
        rcases g1_ih with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
        any_goals apply Or.inl h1.1
        any_goals apply Or.inr (Or.inl h1.1)
        any_goals apply Or.inr (Or.inr h1.1)
      rcases H with h1 | h1 | h1
      · have H := partial_grid_rm_empty_helper g2 p_is h1
        simp only [H.1, true_and, H.2.1, H.2.2, List.nil_append]
        simp only [h1, true_and] at g1_ih
        aesop
      · have H := partial_grid_rm_top_helper g2 p_is h1
        aesop
      have H := partial_grid_rm_top_helper_w g2 h1 p_is
      aesop
    have H := partial_grid_rm_top_helper g1 k_is h2
    simp_all
    rcases H with h1 | h1
    · simp_all
    simp_all
    have H := partial_grid_rm_side_helper g2 p_is h1.1
    aesop

theorem partial_grid_rm_separated_helper (h : PartialGrid a b c d e) (h1 : a = [(i, false)])
    (h2 : b = [(j, true)]) (hij : i.dist j > 1): (c = [] ∧ d = [(i, false), (j, true)] ∧ e = []) ∨
    (c = [] ∧ d = [(j, true), (i, false)] ∧ e = [])  ∨
    (c = [] ∧ d = [(j, true)] ∧ e = [(i, false)]) ∨
    (c = [(j, true)] ∧ d = [(i, false)] ∧ e = []) ∨
    (c = [(j, true)] ∧ d = [] ∧ e = [(i, false)]) := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [to_up_plain, to_over_plain]
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_side_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    simp_all
    have n_is : n = [] ∨ n = [(i, false)] := by aesop
    rcases n_is with hn | hn
    · have H := partial_grid_rm_empty_helper g2 hn o_is
      aesop
    have H := partial_grid_rm_side_helper g2 hn o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      rename_i j'
      have l_nil : l = [] ∨ l = [(j', true)]:= by aesop
      rcases l_nil with hl | hl
      · have H := partial_grid_rm_empty_helper g2 n_is hl
        aesop
      have H := partial_grid_rm_top_helper g2 n_is hl
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · specialize g1_ih j_is h2
      rename_i j'
      have l_nil : l = [] ∨ l = [(j', true)]:= by aesop
      rcases l_nil with hl | hl
      · have H := partial_grid_rm_empty_helper g2 o_is hl
        aesop
      have H := partial_grid_rm_top_helper g2 o_is hl
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

def suffix_of_singleton_c (h : List.Suffix' l [a]) : PLift (l = []) ⊕ PLift (l = [a]) := by
  rcases h with ⟨r, ⟨hr⟩⟩
  match r with
  | [] => right; constructor; aesop
  | r1 :: r2 => left; constructor; aesop

theorem prefix_of_singleton (h : l <+: [a]) : l = [] ∨ l = [a] := by
  rcases h with ⟨r, hr⟩
  match r with
  | [] => aesop
  | r1 :: r2 =>
    apply congr_arg List.length at hr
    simp at hr
    have H : l.length = 0 := by omega
    aesop

def prefix_of_singleton_c (h : List.Prefix' l [a]) : PLift (l = []) ⊕ PLift (l = [a]) := by
  rcases h with ⟨r, ⟨hr⟩⟩
  match r with
  | [] => right; constructor; aesop
  | r1 :: r2 =>
    apply congr_arg List.length at hr
    simp at hr
    have H : l.length = 0 := by omega
    left; constructor
    aesop

theorem to_up_plain_remove_bool (h : is_false up2) :
    to_up_plain (remove_bool up2.reverse) = up2 := by
  simp [to_up_plain, remove_bool]
  induction up2 with
  | nil => simp
  | cons a l hl =>
    cases a
    · apply is_false_split at h
      specialize hl h.2
      simp [hl]
      rename_i a b
      cases b
      · rfl
      have nonsense := h.1 (a, true) ⟨List.mem_singleton.mpr rfl⟩
      simp only at nonsense
      exact nonsense.1

theorem to_over_plain_remove_bool (h : is_true bot2) :
    to_over_plain (remove_bool bot2) = bot2 := by
  simp [to_over_plain, remove_bool]
  induction bot2 with
  | nil => simp
  | cons a l hl =>
    cases a
    · apply is_true_split at h
      specialize hl h.2
      simp [hl]
      rename_i a b
      cases b
      · have nonsense := h.1 (a, false) ⟨List.mem_singleton.mpr rfl⟩
        simp only at nonsense
        exact nonsense.1
      rfl

theorem unique_g_pg_c
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_up_plain a1 = a2)
    (b4_is : to_over_plain b4 = b2)
    (b9 : gridt a1 b4 b6 b7) : to_up_plain b6 = up2 ∧ to_over_plain b7 = bot2 := by
    have H := gridt_of_PartialGrid g1
    unfold gridt_option at H
    have H3 := unicity_c b9 H
    rw [← ha, ← b4_is] at H3
    have hb4 : b4 = remove_bool (to_over_plain b4) := by sorry
    specialize H3 (remove_bool_to_up_plain.symm) (remove_bool_to_over_plain.symm)
    rw [← H3.1.1, ← H3.2.1]
    constructor
    · apply to_up_plain_remove_bool
      exact g1.right_frontier_is_false
    apply to_over_plain_remove_bool
    exact g1.bottom_frontier_is_true

theorem unique_g_pg_c_ones_okay
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_up_plain a1 = a2)
    (b4_is : to_over_plain b4 = b2)
    (b9 : gridt a1 b4 b6 b7) : to_up_plain b6 = up2 ∧ to_over_plain b7 = bot2 := by
    have ha1 : a1 = remove_bool a2.reverse := by
      refine to_up_plain_inj ?_
      rw [ha]
      sorry
    have hb4 : b4 = remove_bool b2 := by
      refine to_over_plain_inj ?_
      rw [b4_is]
      refine Eq.symm (to_over_plain_remove_bool ?_)
      apply g1.top_frontier_is_true
    have H := gridt_of_PartialGrid g1
    unfold gridt_option at H
    have H3 := unicity_c b9 H
    specialize H3 ha1 hb4
    rw [← H3.1.1, ← H3.2.1]
    constructor
    · refine to_up_plain_remove_bool ?_
      exact g1.right_frontier_is_false
    refine to_over_plain_remove_bool ?_
    exact g1.bottom_frontier_is_true

theorem to_over_plain_prod (a b : FreeMonoid ℕ) : to_over_plain (a * b) = to_over_plain a ++ to_over_plain b := by
  have H : to_over_plain a ++ to_over_plain b = to_over_plain (a.toList ++ b.toList) := by
    simp [to_over_plain]
    convert
    rfl
  rw [H]
  convert
  rfl

theorem to_up_plain_prod (a b : FreeMonoid ℕ) : to_up_plain (a * b) = to_up_plain b ++ to_up_plain a := by
  have H : to_up_plain b ++ to_up_plain a = to_up_plain (a.toList ++ b.toList) := by
    simp [to_up_plain]
    convert
    rfl
  rw [H]
  convert
  rfl

theorem to_over_plain_nil : to_over_plain ([] : List ℕ) = [] := rfl
theorem to_up_plain_nil : to_up_plain ([] : List ℕ) = [] := rfl
--theorem foo (ha : is_false a) (h : remover a = to_over_plain (m ++ q)) : False := by sorry
theorem same_time (h : gridt i j k l) (h1 : PartialGrid a b mid d2 e2)
  : (a = to_up_plain i → b <+: to_over_plain j → mid <+: to_over_plain l)
  ∧ (b = to_over_plain j → a <:+ to_up_plain i → e2 <:+ to_up_plain k) := by
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
      rcases prefix_of_singleton b_is with h3 | h4
      · have H := partial_grid_rm_side_helper h1 a_is h3
        aesop
      have H := partial_grid_rm_adjacent_helper h1 a_is h4 h
      have H :  mid = [] ∨  mid = [(k, true)] ∨
        mid = [(k, true), (i, true)] := by aesop
      change _ <+: [(k, true), (i, true)]
      rcases H with h1 | h1 | h1
      · rw [h1]
        exact List.nil_prefix
      · rw [h1]
        exact List.prefix_iff_eq_take.mpr rfl
      rw [h1]
    intro b_is a_is
    rcases suffix_of_singleton a_is with h3 | h4
    · have H := partial_grid_rm_top_helper h1 h3 b_is
      aesop
    have H := partial_grid_rm_adjacent_helper h1 h4 b_is h
    have H : e2 = [] ∨ e2 = [(i, false)] ∨
        e2 = [(k, false), (i, false)] := by aesop
    change _ <:+ [(k, false), (i, false)]
    rcases H with h1 | h1 | h1
    · rw [h1]
      exact List.nil_suffix
    · rw [h1]
      exact List.suffix_cons (k, false) [(i, false)]
    rw [h1]
  | separated i j h =>
    constructor
    · intro a_is b_is
      rcases prefix_of_singleton b_is with h3 | h4
      · have H := partial_grid_rm_side_helper h1 a_is h3
        aesop
      have H := partial_grid_rm_separated_helper h1 a_is h4 h
      aesop
    intro b_is a_is
    rcases suffix_of_singleton a_is with h3 | h4
    · have H := partial_grid_rm_top_helper h1 h3 b_is
      aesop
    have H := partial_grid_rm_separated_helper h1 h4 b_is h
    aesop
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    constructor
    · intro a_is b_is
      rw [to_over_plain_prod] at b_is
      match n with
      | [] =>
        have H := word_top_bottom_t _ _ _ t rfl
        specialize h2_ih h1
        simp_all [to_over_plain]
      | n1 :: n2 =>
        rcases helper_kajillion b_is (by simp) with one | two
        · specialize h1_ih h1
          have new_ih := h1_ih.1 a_is one
          rw [to_over_plain_prod]
          exact List.prefix_of_append new_ih
        rcases two with ⟨b1, b2, b1_len, b2_len, b_is, b1_n, b2_q⟩
        rcases splittable_vertically_of_pg' h1 _ _ b_is b1_len b2_len
          with ⟨mid1, d3, e3, d4, e4, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
        · specialize h1_ih i1
          specialize h2_ih i2
          simp_all
          have nonsense : (mid = d3 ++ e3 ++ d4 ∧ e3 = []) ∨ (mid = d3 ∧ d2 = e3 ++ d4 ++ e4) :=
            frontier_options_from_horizontal h1 i1 i2 hf
          rcases nonsense with h_one | h_two
          · rw [h_one.2] at i1
            have H := unique_g_pg_c_ones_okay i1 a_is.symm b1_n.symm t
            rw [h_one.1, h_one.2, List.append_nil, to_over_plain_prod, H.2]
            exact (List.prefix_append_right_inj d3).mpr ((h2_ih).1 H.1.symm)
          have helper := h1_ih.1
          rw [h_two.1, to_over_plain_prod]
          exact List.prefix_of_append helper
        rcases baaad with ⟨db, drest, h3, ⟨d2_is⟩, ⟨a1_is⟩, ⟨mid_nil⟩, len3⟩
        specialize h1_ih h3
        have H2 := h1_ih.1 a_is (by rw [b1_n])
        rw [to_over_plain_prod]
        exact List.prefix_of_append H2
    intro b_is a_is
    rw [to_over_plain_prod] at b_is
    match n with
    | [] =>
      have H : b = to_over_plain q := by
        convert b_is
      have op := word_top_bottom_t _ _ _ t rfl
      specialize h2_ih h1
      have new_h2_ih := h2_ih.2 H
      rw [op.1] at new_h2_ih
      exact new_h2_ih a_is
    | n1 :: n2 =>
      match q with
      | [] =>
        rw [to_over_plain_nil, List.append_nil] at b_is
        have rs := word_top_bottom_t _ _ _ h2 rfl
        specialize h1_ih h1
        have new_h2_ih := h1_ih.2 b_is a_is
        rw [rs.1]
        exact new_h2_ih
      | q1 :: q2 =>
        rcases splittable_vertically_of_pg' h1 _ _ b_is (by simp [to_over_plain]) (by simp [to_over_plain])
            with ⟨mid4, d4, e4, e5, d5, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
        · specialize h1_ih i1
          specialize h2_ih i2
          simp_all
        rcases baaad with ⟨d5, d6, i3, _ , ⟨e2_nil⟩, ⟨d2_is⟩, ⟨b2_is⟩⟩
        aesop
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    constructor
    · intro a_is b_is
      rw [to_up_plain_prod] at a_is
      match m with
      | [] =>
        rw [to_up_plain_nil, List.append_nil] at a_is
        specialize h2_ih h1
        apply h2_ih.1 a_is
        have np := word_side_side_t _ _ _ t rfl
        rw [np.2]
        exact b_is
      | m1 :: m2 =>
        match q with
        | [] =>
          rw [to_up_plain_nil] at a_is
          have np := word_side_side_t _ _ _ h2 rfl
          rw [np.2]
          specialize h1_ih h1
          apply h1_ih.1 a_is b_is
        | q1 :: q2 =>
          rcases splittable_horizontally_of_pg h1 (to_up_plain (m1 :: m2)) (to_up_plain (q1 :: q2))
            a_is (by simp [to_up_plain]) (by simp [to_up_plain])
           with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
          · specialize h1_ih i1
            have new_h1_ih := h1_ih.1 rfl b_is
            exact (h2_ih i2).1 rfl new_h1_ih
          rcases baaad with ⟨_, _, _, _, _, _, ⟨mid_nil⟩, _⟩
          aesop
    intro hb ha
    have ha1 : a <:+ to_up_plain q ++ to_up_plain m := by
      rw [to_up_plain_prod m q] at ha
      exact ha
    rw [to_up_plain_prod o r]
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
      have H :  a <:+ to_up_plain (m1 :: m2) ∨
        ∃ a1 a2, a1.length > 0 ∧ a = a1 ++ a2 ∧
         a2 = to_up_plain  (m1 :: m2) ∧ a1 <:+ to_up_plain q := by
        exact helper_bajillion ha1
      rcases H with ha1 | ⟨a1, a2, a1_len, a1_is, ha11⟩
      · have H2 : e2 <:+ to_up_plain o := (h1_ih h1).2 hb ha1
        exact suffix_of_append H2
      have a2_len : a2.length > 0 := by
        rw [ha11.1]
        simp [to_up_plain]
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
        rw [fb.2.2, H.1]
        refine List.suffix_append_right ?_
        exact (h2_ih i2).2 H.2.symm ha11.2
      rcases baaad with ⟨db, c11, drest, h3, ⟨d2_is⟩, ⟨a1_is⟩, ⟨mid_nil⟩, len3⟩
      specialize h1_ih h3
      have H2 := h1_ih.2 hb (by rw [ha11.1])
      exact suffix_of_append H2

theorem Suffix'_of_nil (h : List.Suffix' a []) : a = [] := by
  rcases h with ⟨b, ⟨hb⟩⟩
  simp at hb
  aesop

theorem Prefix'_of_nil (h : List.Prefix' a []) : a = [] := by
  rcases h with ⟨b, ⟨hb⟩⟩
  simp at hb
  aesop

noncomputable def prefix_to_c (h : a <+: b) : List.Prefix' a b := by
  have H := h.choose_spec
  rw [← H]
  exact List.prefix_append_self_C

noncomputable def suffix_to_c (h : a <:+ b) : List.Suffix' a b := by
  have H := h.choose_spec
  rw [← H]
  exact List.suffix_append_self_C

theorem prefix_from_c (h : List.Prefix' a b) : a <+: b := by
  rcases h with ⟨c, hc⟩
  rw [← hc.1]
  exact List.prefix_append a c

theorem suffix_from_c (h : List.Suffix' a b) : a <:+ b := by
  rcases h with ⟨c, hc⟩
  rw [← hc.1]
  exact List.suffix_append c a

noncomputable def same_time_c (h : gridt i j k l) (h1 : PartialGrid a b mid d2 e2)
  : (a = to_up_plain i → List.Prefix' (b) (to_over_plain j) → List.Prefix' (mid) (to_over_plain l))
  × (b = to_over_plain j → List.Suffix' (a) (to_up_plain i) → List.Suffix' (e2) (to_up_plain k)) := by
  constructor
  · intro ha hb
    have H := (same_time h h1).1 ha (prefix_from_c hb)
    exact prefix_to_c H
  intro hb ha
  have H := (same_time h h1).2 hb (suffix_from_c ha)
  exact suffix_to_c H
