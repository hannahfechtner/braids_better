import BraidProject.PartialGrid_split
set_option maxHeartbeats 1000000

namespace Braid

def to_vertical_edge_plain (a : List α) : List (α × Bool) := List.map (fun x => (x, false)) a.reverse

def to_horizontal_edge_plain {α : Type} (a : List α) : List (α × Bool) := List.map (fun x => (x, true)) a

theorem remove_up_is_plain : SignedOptionList.toSignedList (to_vertical_edge i) = to_vertical_edge_plain i := by
  induction i with
  | nil => rfl
  | cons head tail ih =>
    match tail with
    | [] =>
      simp [SignedOptionList.toSignedList, to_vertical_edge_plain]
    | t1 :: t2 =>
      have H1 : (to_vertical_edge (head :: t1 :: t2)) = (to_vertical_edge (t1 :: t2)) ++ [(some head, false)] := by
        simp [to_vertical_edge]
      rw [H1, SignedOptionList.toSignedList_append, ih]
      simp [to_vertical_edge_plain, SignedOptionList.toSignedList]

theorem remove_over_is_plain : SignedOptionList.toSignedList (to_horizontal_edge j) = to_horizontal_edge_plain j := by
  induction j with
  | nil => rfl
  | cons head tail ih =>
    match tail with
    | [] =>
      simp [SignedOptionList.toSignedList, to_horizontal_edge_plain]
    | t1 :: t2 =>
      have H1 : (to_horizontal_edge (head :: t1 :: t2)) = [(some head, true)] ++ (to_horizontal_edge (t1 :: t2)) := by
        simp [to_horizontal_edge]
      rw [H1, SignedOptionList.toSignedList_append, ih]
      simp [to_horizontal_edge_plain, SignedOptionList.toSignedList]

open SignedOptionList
theorem eq_toList_of_SignedOptionList.toSignedList_eq_to_horizontal_edge_plain (h : SignedOptionList.toSignedList b = to_horizontal_edge_plain j) : j = toList b := by
  induction b generalizing j with
  | nil =>
    simp [SignedOptionList.toSignedList, to_horizontal_edge_plain] at h
    simp [h, toList]
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [SignedOptionList.toSignedList] at h
      simp [toList]
      exact ih h
    | (some a, _) =>
      simp [SignedOptionList.toSignedList] at h
      simp [toList]
      match j with
      | [] => simp [to_horizontal_edge_plain] at h
      | j1 :: j2 =>
        simp [to_horizontal_edge_plain] at h
        unfold to_horizontal_edge_plain at ih
        specialize ih h.2
        aesop

open SignedList

theorem SignedOptionList.toSignedList_eq_to_horizontal_edge_plain_of_eq_toList (h  : j = toList b) (hb : is_true b) :
    SignedOptionList.toSignedList b = to_horizontal_edge_plain j := by
  induction b generalizing j with
  | nil =>
    simp [toList] at h
    simp [SignedOptionList.toSignedList, to_horizontal_edge_plain]
    exact h
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [SignedOptionList.toSignedList]
      simp [toList] at h
      apply ih h
      exact (is_true_of_cons hb).2
    | (some a, true) =>
      simp [SignedOptionList.toSignedList]
      simp [toList] at h
      match j with
      | [] => simp [to_horizontal_edge_plain] at h
      | j1 :: j2 =>
        simp [to_horizontal_edge_plain] at h
        unfold to_horizontal_edge_plain at ih
        specialize ih h.2
        rw [ih]
        simp [to_horizontal_edge_plain]
        aesop
        exact (is_true_of_cons hb).2
    | (some a, false) =>
      specialize hb (some a, false) (by simp)
      simp at hb

theorem to_horizontal_edge_plain_toList_eq_SignedOptionList.toSignedList(h : is_true b) : to_horizontal_edge_plain (toList b) = SignedOptionList.toSignedList b := by
  induction b with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [to_horizontal_edge_plain, SignedOptionList.toSignedList, ← ih (is_true_of_cons h).2, toList]
    | (some a, true) =>
      simp [to_horizontal_edge_plain, SignedOptionList.toSignedList, ← ih (is_true_of_cons h).2, toList]
    | (some a, false) =>
      have H := (is_true_of_cons h).1 (some a, false) (by simp)
      simp at H

theorem to_vertical_edge_plain_toList_rev_eq_SignedOptionList.toSignedList (h : is_false a) : to_vertical_edge_plain (toList a.reverse) = SignedOptionList.toSignedList a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [to_vertical_edge_plain, SignedOptionList.toSignedList, ← ih (is_false_of_cons h).2, toList_append, toList]
    | (some a, true) =>
      have H := (is_false_of_cons h).1 (some a, true) (by simp)
      simp at H
    | (some a, false) =>
      simp [to_vertical_edge_plain, SignedOptionList.toSignedList, ← ih (is_false_of_cons h).2, toList_append, toList]

theorem to_vertical_edge_plain_inj (h : to_vertical_edge_plain a = to_vertical_edge_plain b) : a = b := by
  simp [to_vertical_edge_plain] at h
  exact (List.map_inj_right (by simp)).mp h

theorem to_horizontal_edge_plain_inj (h : to_horizontal_edge_plain a = to_horizontal_edge_plain b) : a = b := by
  simp [to_horizontal_edge_plain] at h
  exact (List.map_inj_right (by simp)).mp h

open Braid

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
  | horizontal_append h g1 g2 g1_ih g2_ih =>
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

theorem to_vertical_edge_len : (to_vertical_edge a).length > 0 := by
  match a with
  | [] => simp [to_vertical_edge]
  | a1 :: a2 => simp [to_vertical_edge]

theorem to_horizontal_edge_len : (to_horizontal_edge b).length > 0 := by
  match b with
  | [] => simp [to_horizontal_edge]
  | b1 :: b2 => simp [to_horizontal_edge]

theorem to_vertical_edge_plain_append : to_vertical_edge_plain (a ++ b) = to_vertical_edge_plain b ++ to_vertical_edge_plain a := by simp [to_vertical_edge_plain]
theorem to_horizontal_edge_plain_append : to_horizontal_edge_plain (a ++ b) = to_horizontal_edge_plain a ++ to_horizontal_edge_plain b := by simp [to_horizontal_edge_plain]
theorem SignedOptionList.toSignedList_len(a : List (Option α × Bool))  : (SignedOptionList.toSignedList a).length ≤ a.length := by
  induction a with
  | nil => simp [SignedOptionList.toSignedList]
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [SignedOptionList.toSignedList] at ih
      simp [SignedOptionList.toSignedList, ih]
      omega
    | (some a, true) =>
      simp [SignedOptionList.toSignedList] at ih
      simp [SignedOptionList.toSignedList, ih]
    | (some a, false) =>
      simp [SignedOptionList.toSignedList] at ih
      simp [SignedOptionList.toSignedList, ih]

theorem SignedOptionList.toSignedList_eq_append (h : SignedOptionList.toSignedList a = b ++ c) :
    ∃ a1 a2, a=a1++a2 ∧ SignedOptionList.toSignedList a1 = b ∧ SignedOptionList.toSignedList a2 = c := by
  induction a generalizing b c with
  | nil =>
    simp [SignedOptionList.toSignedList] at h
    aesop
  | cons head tail ih =>
    match head with
    | (none, b) =>
      simp [SignedOptionList.toSignedList] at h
      specialize ih h
      rcases ih with ⟨a1, a2, a_is, b_is, c_is⟩
      use (none, b) :: a1, a2
      simp_all [SignedOptionList.toSignedList]
    | (some d, e) =>
      match b with
      | [] =>
        match c with
        | [] => aesop
        | c1 :: c2 =>
          simp [SignedOptionList.toSignedList] at h
          use [], (some d, e) :: tail
          aesop
      | b1 :: b2 =>
        simp [SignedOptionList.toSignedList] at h
        match b2 with
        | [] =>
          use [(some d, e)], tail
          simp_all [SignedOptionList.toSignedList]
        | b21 :: b22 =>
          specialize ih h.2
          rcases ih with ⟨a1, a2, a_is, b_is, c_is⟩
          use (some d, e) :: a1, a2
          simp_all [SignedOptionList.toSignedList]

theorem SignedOptionList.toSignedList_eq_to_vertical_edge_plain_prod {m q : List α} (h : SignedOptionList.toSignedList a = to_vertical_edge_plain (m ++ q)) :
   m = [] ∨ q = [] ∨ ∃ (a1 a2 : List (Option α × Bool)), a1.length > 0 ∧ a2.length > 0 ∧
        a = a1 ++ a2 ∧ SignedOptionList.toSignedList a1 = to_vertical_edge_plain q ∧ SignedOptionList.toSignedList a2 = to_vertical_edge_plain m  := by
  induction m generalizing a q with
  | nil => exact Or.inl rfl
  | cons m1 m2 ih =>
    right
    match q with
    | [] => exact Or.inl rfl
    | q1 :: q2 =>
      right
      rw [to_vertical_edge_plain_append] at h
      rcases SignedOptionList.toSignedList_eq_append h with ⟨a1, a2, a_is, a1s, a2s⟩
      use a1, a2
      have a1l := SignedOptionList.toSignedList_len a1
      have a2l := SignedOptionList.toSignedList_len a2
      have a1le := congr_arg List.length a1s
      have a2le := congr_arg List.length a2s
      simp [to_vertical_edge_plain] at a1le
      simp [to_vertical_edge_plain] at a2le
      have a1_len : a1.length > 0 := by
        omega
      have a2_len : a2.length > 0 := by omega
      aesop

theorem SignedOptionList.toSignedList_eq_to_horizontal_edge_plain_prod {n : List (α)} (h : SignedOptionList.toSignedList b = to_horizontal_edge_plain (n ++ q)) :
  n = [] ∨ q = [] ∨ ∃ b1 b2, b1.length > 0 ∧ b2.length > 0 ∧
          b = b1 ++ b2 ∧ SignedOptionList.toSignedList b1 = to_horizontal_edge_plain n ∧ SignedOptionList.toSignedList b2 = to_horizontal_edge_plain q := by
  induction n generalizing b q with
  | nil => exact Or.inl rfl
  | cons n1 n2 ih =>
    right
    match q with
    | [] => exact Or.inl rfl
    | q1 :: q2 =>
      right
      rw [to_horizontal_edge_plain_append] at h
      rcases SignedOptionList.toSignedList_eq_append h with ⟨b1, b2, b_is, b1s, b2s⟩
      use b1, b2
      have b1l := SignedOptionList.toSignedList_len b1
      have b2l := SignedOptionList.toSignedList_len b2
      have b1le := congr_arg List.length b1s
      have b2le := congr_arg List.length b2s
      simp only [to_horizontal_edge_plain, List.map_cons, List.length_cons, List.length_map] at b1le
      simp only [to_horizontal_edge_plain, List.map_cons, List.length_cons, List.length_map] at b2le
      have b1_len : b1.length > 0 := by omega
      have b2_len : b2.length > 0 := by omega
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
    exact List.suffix_append ([f1] ++ f2) a

theorem List.prefix_of_append_mine {a b c : List α} (h : a <+: b ++ c) : a <+: b ∨ ∃ a2, a2.length > 0 ∧
  a = b ++ a2 ∧ a2 <+: c := by
  rcases h with ⟨r, hr⟩
  rcases List.append_eq_append_iff.mp hr with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · match tm with
    | [] => aesop
    | t1 :: t2 =>
      left
      rw [s1]
      exact List.prefix_append a (t1 :: t2)
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
    (ha : SignedOptionList.toSignedList a <:+ to_vertical_edge_plain q ++ to_vertical_edge_plain (m1 :: m2)) :
    SignedOptionList.toSignedList a <:+ to_vertical_edge_plain (m1 :: m2) ∨
    ∃ (a1 a2 : List (Option α × Bool)), a1.length > 0 ∧ a = a1 ++ a2 ∧
    SignedOptionList.toSignedList a2 = to_vertical_edge_plain (m1 :: m2) ∧ SignedOptionList.toSignedList a1 <:+ to_vertical_edge_plain q := by
  rcases List.suffix_of_append ha with one | two
  · left
    exact one
  rcases two with ⟨a1, a1_len, a_is, a1_suff⟩
  right
  rcases SignedOptionList.toSignedList_eq_append a_is with ⟨a3, a4, a_is, a3a1, m4⟩
  use a3, a4
  constructor
  · have H := SignedOptionList.toSignedList_len a3
    rw [a3a1] at H
    omega
  constructor
  · assumption
  constructor
  · exact m4
  rw [a3a1]
  assumption

theorem helper_kajillion {α : Type} {n q : List α} {b : List (Option α × Bool)} (h : SignedOptionList.toSignedList b <+: to_horizontal_edge_plain n ++ to_horizontal_edge_plain q) (hn : n.length > 0):
  SignedOptionList.toSignedList b <+: to_horizontal_edge_plain n ∨ ∃ (b₁ b₂ : List (Option α × Bool)), b₁.length > 0 ∧ b₂.length > 0 ∧ b = b₁ ++ b₂ ∧
    SignedOptionList.toSignedList b₁ = to_horizontal_edge_plain n ∧ SignedOptionList.toSignedList b₂ <+: to_horizontal_edge_plain q := by
  rcases List.prefix_of_append_mine h with one | two
  · left
    exact one
  rcases two with ⟨b1, b1_len, b_is, b1_pref⟩
  right
  rcases SignedOptionList.toSignedList_eq_append b_is with ⟨a3, a4, a_is, a3a1, m4⟩
  use a3, a4
  constructor
  · have H := SignedOptionList.toSignedList_len a3
    rw [a3a1] at H
    simp [to_horizontal_edge_plain] at H
    omega
  constructor
  · have H := SignedOptionList.toSignedList_len a4
    rw [m4] at H
    omega
  aesop

theorem frontier_options_from_vertical (h1 : PartialGrid a b mid d2 e2)
    (i1 : PartialGrid a2 b mid4 e5 d5) (i2 : PartialGrid a1 mid4 mid d4 e4)
    (hf : d4 ++ e4 ++ e5 ++ d5 = d2 ++ e2) :
    (d2 = d4 ++ e4 ++ e5 ∧ d5 = e2) ∨ (d2 = d4 ∧ e5 = [] ∧ e2 = e4 ++ d5) := by
  rcases PartialGrid.middle_frontier_spec i1 with ⟨⟨e5_nil⟩⟩ | ⟨fronte5, mide5, caboosee5, ⟨spece5⟩⟩
  · right
    rw [e5_nil, List.append_nil] at hf
    rcases PartialGrid.middle_frontier_spec h1 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, middled2, caboosed2, ⟨specd2⟩⟩
    · rw [d2_nil, List.nil_append] at hf
      rcases PartialGrid.middle_frontier_spec i2 with ⟨⟨d4_nil⟩⟩ | ⟨frontd4, middled4, caboosed4, ⟨specd4⟩⟩
      · rw [d4_nil, List.nil_append] at hf
        aesop
      rw [specd4] at hf
      have H : is_false e2 := h1.right_frontier_is_false
      rw [← hf] at H
      specialize H (caboosed4, true) (by simp)
      simp at H
    rw [specd2] at hf
    have H : is_false (e4 ++ d5) := by
        apply is_false_append
        · exact i2.right_frontier_is_false
        exact i1.right_frontier_is_false
    rcases PartialGrid.middle_frontier_spec i2 with ⟨⟨d4_nil⟩⟩ | ⟨frontd4, middled4, caboosed4, ⟨specd4⟩⟩
    · rw [d4_nil, List.nil_append] at hf
      rw [hf] at H
      specialize H (caboosed2, true) (by simp)
      simp at H
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
        specialize H (caboosed2, true) (by simp)
        simp at H
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
      specialize H (caboosed4, true) (by simp)
      simp at H
  left
  rw [spece5] at hf
  rcases List.append_eq_append_iff.mp hf with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · cases tm using List.reverseRecOn with
    | nil => aesop
    | append_singleton t1 t2 =>
      exfalso
      rcases PartialGrid.middle_frontier_spec h1 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, midd2, caboosed2, ⟨specd2⟩⟩
      · simp [d2_nil] at s1
      rw [specd2] at s1
      have H : t2 = (caboosed2, true) := by
        apply congr_arg List.getLast? at s1
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
        exact s1.symm
      have H1 : is_false d5 := i1.right_frontier_is_false
      rw [s2, H] at H1
      specialize H1 (caboosed2, true) (by simp)
      simp at H1
  cases fm using List.reverseRecOn with
  | nil => aesop
  | append_singleton f1 f2 =>
    have H : f2 = (caboosee5, true) := by
      apply congr_arg List.getLast? at s1
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
      exact s1.symm
    have H1 : is_false e2 := by exact h1.right_frontier_is_false
    rw [s2, H] at H1
    specialize H1 (caboosee5, true) (by simp)
    simp at H1

theorem frontier_options_from_horizontal (h1 : PartialGrid a b mid d2 e2)
    (i1 : PartialGrid a b1 d3 e3 mid1) (i2 : PartialGrid mid1 b2 d4 e4 e2)
    (hf : mid ++ d2 = d3 ++ (e3 ++ (d4 ++ e4))) :
    (mid = d3 ++ e3 ++ d4 ∧ e3 = []) ∨ (mid = d3 ∧ d2 = e3 ++ d4 ++ e4) := by
  have mid_t : is_true mid := h1.bottom_frontier_is_true
  have d3_t : is_true d3 := i1.bottom_frontier_is_true
  have d4_t : is_true d4 := i2.bottom_frontier_is_true
  have mid1_f : is_false mid1 := i2.left_frontier_is_false
  rcases PartialGrid.middle_frontier_spec h1 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, middled2, caboosed2, ⟨specd2⟩⟩
  · left
    rw [d2_nil, List.append_nil] at hf
    rcases PartialGrid.middle_frontier_spec i1 with ⟨⟨e3_nil⟩⟩ | ⟨fronte3, middlee3, caboosee3, ⟨spece3⟩⟩
    · rw [e3_nil, List.nil_append] at hf
      rcases PartialGrid.middle_frontier_spec i2 with ⟨⟨e4_nil⟩⟩ | ⟨fronte4, middlee4, caboosee4, ⟨spece4⟩⟩
      · rw [e4_nil, List.append_nil] at hf
        aesop
      rw [spece4] at hf
      rw [hf] at mid_t
      specialize mid_t (fronte4, false) (by simp)
      simp at mid_t
    rw [spece3] at hf
    rw [hf] at mid_t
    specialize mid_t (fronte3, false) (by simp)
    simp at mid_t
  rcases PartialGrid.middle_frontier_spec i1 with ⟨⟨e3_nil⟩⟩ | ⟨fronte3, middlee3, caboosee3, ⟨spece3⟩⟩
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
        have H : is_true (d3 ++ d4) := is_true_append d3_t d4_t
        rw [s1, ← s2.1] at H
        specialize H (frontd2, false) (by simp)
        simp at H
    match fm with
    | [] => aesop
    | f1 :: f2 =>
      rw [specd2] at s2
      rcases PartialGrid.middle_frontier_spec i2 with ⟨⟨e4_nil⟩⟩ | ⟨fronte4, middlee4, caboosee4, ⟨spece4⟩⟩
      · aesop
      rw [spece4] at s2
      simp at s2
      rw [← s2.1] at s1
      rw [s1] at mid_t
      specialize mid_t (fronte4, false) (by simp)
      simp at mid_t
  right
  rcases List.append_eq_append_iff.mp hf with
    ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · match tm with
    | [] => aesop
    | t1 :: t2 =>
      rw [specd2] at s2
      simp at s2
      rw [s1, ← s2.1] at d3_t
      specialize d3_t (frontd2, false) (by simp)
      simp at d3_t
  match fm with
  | [] => aesop
  | f1 :: f2 =>
    rw [specd2] at s2
    rcases PartialGrid.middle_frontier_spec i1 with ⟨⟨e3_nil⟩⟩ | ⟨fronte3, middlee3, caboosee3, ⟨spece3⟩⟩
    · aesop
    rw [spece3] at s2
    simp at s2
    rw [s1, ← s2.1] at mid_t
    specialize mid_t (fronte3, false) (by simp)
    simp at mid_t

theorem partial_grid_rm_empty_helper (h : PartialGrid a b c d e) : SignedOptionList.toSignedList a = [] → SignedOptionList.toSignedList b = [] →
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = []) := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all
    | sides i => simp_all
    | top_left i => simp_all [to_vertical_edge, SignedOptionList.toSignedList]
    | adjacent i k h => simp_all [to_vertical_edge, SignedOptionList.toSignedList]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih => simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all
  | vertical_append g1 g2 h g1_ih g2_ih => simp_all

theorem partial_grid_rm_top_helper (h : PartialGrid a b c d e) : SignedOptionList.toSignedList a = [] → SignedOptionList.toSignedList b = [(i, true)] →
    (SignedOptionList.toSignedList c = [(i, true)] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = []) ∨
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, true)] ∧ SignedOptionList.toSignedList e = []) := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all
    | sides i => simp_all
    | top_left i => simp_all [to_vertical_edge, SignedOptionList.toSignedList]
    | adjacent i k h => simp_all [to_vertical_edge, SignedOptionList.toSignedList]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    intro j_is kn_is
    rw [SignedOptionList.toSignedList_append] at kn_is
    rcases List.append_eq_singleton_iff.mp kn_is with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_empty_helper g1 j_is k_is
      simp_all
    simp_all only [SignedOptionList.toSignedList_nil, true_and, List.ne_cons_self, false_and, and_false, or_false,
      forall_const, IsEmpty.forall_iff, List.append_nil, SignedOptionList.toSignedList_append,
      List.cons_append, List.nil_append, List.cons.injEq]
    have H := partial_grid_rm_empty_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    intro j_is ko_is
    rw [SignedOptionList.toSignedList_append] at ko_is
    rcases List.append_eq_singleton_iff.mp ko_is with
      ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_empty_helper g1 j_is k_is
      simp_all
      rcases g2_ih with h1 | h2
      · simp_all
      simp_all
    have hn : SignedOptionList.toSignedList n = [] := by aesop
    have H := partial_grid_rm_empty_helper g2 hn o_is
    simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    intro oj_is k_is
    rw [SignedOptionList.toSignedList_append] at oj_is
    simp at oj_is
    specialize g1_ih oj_is.2 k_is
    rcases g1_ih with h1 | h2
    · specialize g2_ih oj_is.1 h1.1
      rcases g2_ih with h3 | h4
      · simp_all
      simp_all
    have H := partial_grid_rm_empty_helper g2 oj_is.1 h2.1
    simp_all

-- noncomputable def partial_grid_rm_top_helper_c (h : PartialGrid a b c d e) : SignedOptionList.toSignedList a = [] → SignedOptionList.toSignedList b = [(i, true)] →
--     PLift (SignedOptionList.toSignedList c = [(i, true)] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = []) ⊕
--     PLift (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, true)] ∧ SignedOptionList.toSignedList e = []) := by
--   induction h with
--   | single_gridt h =>
--     cases h with
--     | empty => intro h1 h2; simp_all [SignedOptionList.toSignedList]
--     | top_bottom i => intro h1 h2; simp_all [SignedOptionList.toSignedList]; left; constructor; trivial
--     | sides i => intro h1 h2; simp_all [SignedOptionList.toSignedList]
--     | top_left i => intro h1 h2; simp_all [SignedOptionList.toSignedList]
--     | adjacent i k h => intro h1 h2; simp_all [SignedOptionList.toSignedList]
--     | separated i j h => intro h1 h2; simp_all [SignedOptionList.toSignedList]
--   | empty a b ha ha1 hb hb => intro h1 h2; simp_all [SignedOptionList.toSignedList]; right; constructor; trivial
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     rename_i j k l m n o p q
--     intro j_is kn_is
--     rw [SignedOptionList.toSignedList_append] at kn_is
--     rcases List.append_eq_singleton_C kn_is with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
--     · have H := partial_grid_rm_empty_helper g1 j_is k_is
--       specialize g2_ih H.2.2 n_is
--       rcases g2_ih with h1 | h2
--       · simp_all [h1.1]; left; constructor; trivial
--       simp_all [h2.1]; right; constructor; trivial
--     specialize g1_ih j_is k_is
--     rcases g1_ih with ⟨⟨h1⟩⟩| ⟨⟨h2⟩⟩
--     · have H := partial_grid_rm_empty_helper g2 h1.2.2 n_is
--       simp_all; left; constructor; trivial
--     have H := partial_grid_rm_empty_helper g2 h2.2.2 n_is
--     simp_all
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     rename_i j k l m n o p q r
--     intro j_is ko_is
--     rw [SignedOptionList.toSignedList_append] at ko_is
--     rcases List.append_eq_singleton_C ko_is with
--       ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
--     · have H := partial_grid_rm_empty_helper g1 j_is k_is
--       specialize g2_ih H.2.2 o_is
--       rcases g2_ih with h1 | h2
--       · simp_all [h1.1]; right; constructor; trivial
--       simp_all [h2.1]; right; constructor; trivial
--     specialize g1_ih j_is k_is
--     have hn : SignedOptionList.toSignedList n = [] := by
--       rcases g1_ih with ⟨⟨h1⟩⟩| ⟨⟨h2⟩⟩
--       · aesop
--       aesop
--     have H := partial_grid_rm_empty_helper g2 hn o_is
--     rcases g1_ih with ⟨⟨h1⟩⟩| ⟨⟨h2⟩⟩
--     · simp_all
--       left; constructor; trivial
--     simp_all
--     right; constructor; trivial
--   | vertical_append_one g1 g2 g1_ih g2_ih =>
--     intro h1 h2; simp_all [SignedOptionList.toSignedList]
--     specialize g1_ih h1.2 h2
--     rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · specialize g2_ih h1.1 h3.1
--       rcases g2_ih with h5 | h6
--       · simp_all [h3.1, h5.1]; left; constructor; trivial
--       simp_all [h3.1, h6.1]; right; constructor; trivial
--     simp at h4
--   | vertical_append g1 g2 h g1_ih g2_ih =>
--     rename_i j k l m n o p q r
--     intro oj_is k_is
--     rw [SignedOptionList.toSignedList_append] at oj_is
--     simp at oj_is
--     specialize g1_ih oj_is.2 k_is
--     rcases g1_ih with h1 | h2
--     · specialize g2_ih oj_is.1 h1.1.1
--       rcases g2_ih with h3 | h4
--       · simp_all [h1.1, h3.1]; left; constructor; trivial
--       simp_all [h1.1, h4.1]; right; constructor; trivial
--     have H := partial_grid_rm_empty_helper g2 oj_is.1 h2.1.1
--     simp_all [h2.1]
--     right; constructor; trivial

theorem partial_grid_rm_top_helper_w (h : PartialGrid a b c d e)
    (h1 : SignedOptionList.toSignedList b = [(i, true), (j, true)]) (h2 : SignedOptionList.toSignedList a = []) :
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, true), (j, true)] ∧ SignedOptionList.toSignedList e = []) ∨
    (SignedOptionList.toSignedList c = [(i, true)] ∧ SignedOptionList.toSignedList d = [(j, true)] ∧ SignedOptionList.toSignedList e = []) ∨
    (SignedOptionList.toSignedList c = [(i, true), (j, true)] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = []) := by
  change _ = [(i, true)] ++ [(j, true)] at h1
  rcases SignedOptionList.toSignedList_eq_append h1 with ⟨a1, a2, ha⟩
  have ha1 : a1.length > 0 := by
    have H := SignedOptionList.toSignedList_len a1
    aesop
  have ha2 : a2.length > 0 := by
    have H := SignedOptionList.toSignedList_len a2
    aesop
  rcases splittable_vertically_of_pg' h _ _ ha.1 ha1 ha2 with
    ⟨mid, d1, e1, d2, e2, i1, i2, ⟨long⟩, len⟩ | baaad
  · have H := partial_grid_rm_top_helper i1 h2 ha.2.1
    have hmid : SignedOptionList.toSignedList mid = [] := by aesop
    have H2 := partial_grid_rm_top_helper i2 hmid ha.2.2
    have hc : SignedOptionList.toSignedList e = [] := by aesop
    simp [hc]
    have H : [(i, true), (j, true)] = SignedOptionList.toSignedList c ++ SignedOptionList.toSignedList d := by
      apply congr_arg SignedOptionList.toSignedList at long
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
    match hc : SignedOptionList.toSignedList c with
    | [] =>
      match hd : SignedOptionList.toSignedList d with
      | [] => simp [hc, hd] at H
      | d1 :: d2 => aesop
    | c1 :: c2 =>
      match hd : SignedOptionList.toSignedList d with
      | [] =>
        simp_all
      | d1 :: d2 =>
        right; left
        have hl := congr_arg List.length H
        rw [hc, hd] at hl
        simp at hl
        have hc2 : c2.length = 0 := by omega
        aesop
  rcases baaad with ⟨db, c1, i1, ⟨d_is⟩, ⟨db_is⟩, ⟨d_is'⟩, ⟨a_is⟩⟩
  have H := partial_grid_rm_top_helper i1 h2 ha.2.1
  aesop

theorem partial_grid_rm_side_helper (h : PartialGrid a b c d e)
    (h1 : SignedOptionList.toSignedList a = [(i, false)]) (h2 : SignedOptionList.toSignedList b = []) :
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, false)] ∧ SignedOptionList.toSignedList e = []) ∨
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = [(i, false)]) := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp_all [SignedOptionList.toSignedList]
    | top_bottom i => simp_all [SignedOptionList.toSignedList]
    | sides i => simp_all [SignedOptionList.toSignedList]
    | top_left i => simp_all [to_vertical_edge, SignedOptionList.toSignedList]
    | adjacent i k h => simp_all [to_vertical_edge, SignedOptionList.toSignedList]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    simp [SignedOptionList.toSignedList_append] at h2
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
    rw [SignedOptionList.toSignedList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · simp_all
      have H := partial_grid_rm_empty_helper g2 n_is g1_ih.1
      simp_all
    have H := partial_grid_rm_empty_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [SignedOptionList.toSignedList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · simp_all
      have l_is : SignedOptionList.toSignedList l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 o_is l_is
      simp_all
    have H := partial_grid_rm_empty_helper g1 j_is h2
    simp_all
    rcases g2_ih with h3 | h4
    · simp_all
    simp_all

-- noncomputable def partial_grid_rm_side_helper_c (h : PartialGrid a b c d e)
--     (h1 : SignedOptionList.toSignedList a = [(i, false)]) (h2 : SignedOptionList.toSignedList b = []) :
--     PLift (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, false)] ∧ SignedOptionList.toSignedList e = []) ⊕
--     PLift (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = [(i, false)]) := by
--   induction h with
--   | single_gridt h =>
--     cases h with
--     | empty => simp_all [SignedOptionList.toSignedList]
--     | top_bottom i => simp_all [SignedOptionList.toSignedList]
--     | sides i => simp_all [SignedOptionList.toSignedList]; right; constructor; trivial
--     | top_left i => simp_all [to_vertical_edge, SignedOptionList.toSignedList]
--     | adjacent i k h => simp_all [to_vertical_edge, SignedOptionList.toSignedList]
--     | separated i j h => simp_all; right; constructor; trivial
--   | empty a b ha ha1 hb hb => simp_all; left; constructor; trivial
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     simp [SignedOptionList.toSignedList_append] at h2
--     specialize g1_ih h1 h2.1
--     rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · simp_all
--     specialize g2_ih h4.2.2 h2.2
--     rcases g2_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · simp_all; left; constructor; trivial
--     simp_all; right; constructor; trivial
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     rename_i j k l m n o p q r
--     simp [SignedOptionList.toSignedList_append] at h2
--     specialize g1_ih h1 h2.1
--     rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · have H := partial_grid_rm_empty_helper g2 h3.2.2 h2.2
--       simp_all
--       left; constructor; trivial
--     specialize g2_ih h4.2.2 h2.2
--     rcases g2_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · simp_all; left; constructor; trivial
--     simp_all; right; constructor; trivial
--   | vertical_append_one g1 g2 g1_ih g2_ih =>
--     rename_i j k l m n o p q
--     rw [SignedOptionList.toSignedList_append] at h1
--     rcases List.append_eq_singleton_C h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
--     · specialize g1_ih j_is h2
--       have H : SignedOptionList.toSignedList l = [] := by
--         rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--         · aesop
--         aesop
--       have H := partial_grid_rm_empty_helper g2 n_is H
--       rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · simp_all
--       simp_all; right; constructor; trivial
--     have H := partial_grid_rm_empty_helper g1 j_is h2
--     specialize g2_ih n_is H.1
--     rcases g2_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · simp_all
--       left; constructor; trivial
--     simp_all
--     right; constructor; trivial
--   | vertical_append g1 g2 h g1_ih g2_ih =>
--     rename_i j k l m n o p q r
--     rw [SignedOptionList.toSignedList_append] at h1
--     rcases List.append_eq_singleton_C h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
--     · specialize g1_ih j_is h2
--       have l_is : SignedOptionList.toSignedList l = [] := by
--         rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--         · aesop
--         aesop
--       have H := partial_grid_rm_empty_helper g2 o_is l_is
--       rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · simp_all; left; constructor; trivial
--       simp_all; right; constructor; trivial
--     have H := partial_grid_rm_empty_helper g1 j_is h2
--     specialize g2_ih o_is H.1
--     rcases g2_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · simp_all
--       left; constructor; trivial
--     simp_all; left; constructor; trivial

theorem partial_grid_rm_side_helper_w (h : PartialGrid a b c d e)
    (h1 : SignedOptionList.toSignedList a = [(i, false), (j, false)]) (h2 : SignedOptionList.toSignedList b = []) :
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, false), (j, false)] ∧ SignedOptionList.toSignedList e = []) ∨
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, false)] ∧ SignedOptionList.toSignedList e = [(j, false)]) ∨
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = [(i, false), (j, false)]) := by
  change _ = [(i, false)] ++ [(j, false)] at h1
  rcases SignedOptionList.toSignedList_eq_append h1 with ⟨a1, a2, ha⟩
  have ha1 : a1.length > 0 := by
    have H := SignedOptionList.toSignedList_len a1
    aesop
  have ha2 : a2.length > 0 := by
    have H := SignedOptionList.toSignedList_len a2
    aesop
  rcases splittable_horizontally_of_pg h _ _ ha.1 ha2 ha1 with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨long⟩, len⟩ | baaad
  · have H := partial_grid_rm_side_helper i1 ha.2.2 h2
    have hmid : SignedOptionList.toSignedList mid = [] := by aesop
    have H2 := partial_grid_rm_side_helper i2 ha.2.1 hmid
    have hc : SignedOptionList.toSignedList c = [] := by aesop
    simp [hc]
    have H : [(i, false), (j, false)] = SignedOptionList.toSignedList d ++ SignedOptionList.toSignedList e := by
      apply congr_arg SignedOptionList.toSignedList at long
      simp at long
      rcases H with h3 | h4
      · rcases H2 with h5 | h6
        · simp [h3, h5] at long
          exact long
        simp [h3, h6] at long
        exact long
      rcases H2 with h7 | h8
      · simp [h4, h7] at long
        exact long
      simp [h4, h8] at long
      exact long
    match hd : SignedOptionList.toSignedList d with
    | [] => aesop
    | d1 :: d2 =>
      match he :SignedOptionList.toSignedList e with
      | [] => aesop
      | e1 :: e2 =>
        rcases List.append_eq_len_two (by simp [hd]) (by simp [he]) H.symm
        aesop
  rcases baaad with ⟨db, c1, drest, i1, ⟨d_is⟩, ⟨db_is⟩, ⟨c_nil⟩, len⟩
  have H := partial_grid_rm_side_helper i1 ha.2.2 h2
  aesop

theorem partial_grid_rm_top_left_helper (h : PartialGrid a b c d e) (h1 : SignedOptionList.toSignedList a = [(i, false)])
  (h2 : SignedOptionList.toSignedList b = [(i, true)]) : (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = []) ∨
  (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, false), (i, true)] ∧ SignedOptionList.toSignedList e = []) := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [SignedOptionList.toSignedList]
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [SignedOptionList.toSignedList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_empty_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [SignedOptionList.toSignedList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    have n_is : SignedOptionList.toSignedList n = [] := by aesop
    have H := partial_grid_rm_empty_helper g2 n_is o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [SignedOptionList.toSignedList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : SignedOptionList.toSignedList l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 n_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [SignedOptionList.toSignedList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : SignedOptionList.toSignedList l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 o_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
    rcases H with h3 | h4
    · aesop
    have H := partial_grid_rm_side_helper g2 o_is h4.1
    aesop

-- noncomputable def partial_grid_rm_top_left_helper_c (h : PartialGrid a b c d e) (h1 : SignedOptionList.toSignedList a = [(i, false)])
--   (h2 : SignedOptionList.toSignedList b = [(i, true)]) : PLift (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = []) ⊕
--   PLift (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, false), (i, true)] ∧ SignedOptionList.toSignedList e = []) := by
--   induction h with
--   | single_gridt h =>
--     cases h
--     all_goals simp_all [SignedOptionList.toSignedList]
--     left; constructor; trivial
--   | empty a b ha ha1 hb hb => simp_all; right;  constructor; trivial
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     rename_i j k l m n o p q
--     rw [SignedOptionList.toSignedList_append] at h2
--     rcases List.append_eq_singleton_C h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
--     · have H := partial_grid_rm_side_helper_c g1 h1 k_is
--       rcases H with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · simp_all
--       simp_all
--       specialize g2_ih h4.2 n_is
--       rcases g2_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · simp_all; left; constructor; trivial
--       simp_all; right; constructor; trivial
--     specialize g1_ih h1 k_is
--     have H : SignedOptionList.toSignedList m = [] := by
--       rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · aesop
--       aesop
--     have H2 : SignedOptionList.toSignedList l = [] := by
--       rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · aesop
--       aesop
--     have H := partial_grid_rm_empty_helper g2 H n_is
--     simp_all; left; constructor; trivial
--   | horizontal_append h g1 g2 g1_ih g2_ih =>
--     rename_i j k l m n o p q r
--     rw [SignedOptionList.toSignedList_append] at h2
--     rcases List.append_eq_singleton_C h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
--     · have H := partial_grid_rm_side_helper_c g1 h1 k_is
--       rcases H with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · have H2 := partial_grid_rm_top_helper_c g2 h3.2.2 o_is
--         rcases H2 with
--           ⟨⟨h5⟩⟩ | ⟨⟨h6⟩⟩
--         · simp_all [h5.1]; right; constructor; trivial
--         simp_all [h6.1]; right; constructor; trivial
--       specialize g2_ih h4.2.2 o_is
--       rcases g2_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · simp_all; left; constructor; trivial
--       simp_all; right; constructor; trivial
--     specialize g1_ih h1 k_is
--     have n_is : SignedOptionList.toSignedList n = [] := by
--       rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · simp_all
--       simp_all
--     have H := partial_grid_rm_empty_helper g2 n_is o_is
--     simp_all
--     rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · simp_all; left; constructor; trivial
--     simp_all; right; constructor; trivial
--   | vertical_append_one g1 g2 g1_ih g2_ih =>
--     rename_i j k l m n o p q
--     rw [SignedOptionList.toSignedList_append] at h1
--     rcases List.append_eq_singleton_C h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
--     · specialize g1_ih j_is h2
--       have l_nil : SignedOptionList.toSignedList l = [] := by
--         rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--         · aesop
--         aesop
--       have H := partial_grid_rm_empty_helper g2 n_is l_nil
--       rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · simp_all
--         left; constructor; trivial
--       simp_all
--     have H := partial_grid_rm_top_helper_c g1 j_is h2
--     rcases H with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · simp_all
--       specialize g2_ih n_is h3.1
--       rcases g2_ih with ⟨⟨h5⟩⟩ | ⟨⟨h6⟩⟩
--       · simp_all [h3.1, h5.1]; left; constructor; trivial
--       simp_all [h3.1, h6.1]; right; constructor; trivial
--     simp_all
--   | vertical_append g1 g2 h g1_ih g2_ih =>
--     rename_i j k l m n o p q r
--     rw [SignedOptionList.toSignedList_append] at h1
--     rcases List.append_eq_singleton_C h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
--     · specialize g1_ih j_is h2
--       have l_nil : SignedOptionList.toSignedList l = [] := by
--         rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--         · aesop
--         aesop
--       have H := partial_grid_rm_empty_helper g2 o_is l_nil
--       rcases g1_ih with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--       · simp_all; left; constructor; trivial
--       simp_all; right; constructor; trivial
--     have H := partial_grid_rm_top_helper_c g1 j_is h2
--     rcases H with ⟨⟨h3⟩⟩ | ⟨⟨h4⟩⟩
--     · specialize g2_ih o_is h3.1
--       rcases g2_ih with ⟨⟨h5⟩⟩ | ⟨⟨h6⟩⟩
--       · simp_all [h3.1, h5.1]; left; constructor; trivial
--       simp_all; right; constructor; trivial
--     have H := partial_grid_rm_side_helper_c g2 o_is h4.1
--     rcases H with
--       ⟨⟨h5⟩⟩ | ⟨⟨h6⟩⟩
--     · simp_all
--       right; constructor; trivial
--     simp_all; right; constructor; trivial

theorem partial_grid_rm_adjacent_helper
  (h : PartialGrid a b c d e) (h1 : SignedOptionList.toSignedList a = [(i, false)])
  (h2 : SignedOptionList.toSignedList b = [(j, true)]) (hij : i.dist j = 1):
  (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, false), (j, true)] ∧ SignedOptionList.toSignedList e = []) ∨
  (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(j, true), (i, true), (j, false), (i, false)] ∧ SignedOptionList.toSignedList e = [])  ∨
  (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(j, true), (i, true), (j, false)] ∧ SignedOptionList.toSignedList e = [(i, false)]) ∨
  (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(j, true), (i, true)] ∧ SignedOptionList.toSignedList e = [(j, false), (i, false)]) ∨
  (SignedOptionList.toSignedList c = [(j, true)] ∧ SignedOptionList.toSignedList d = [(i, true), (j, false), (i, false)] ∧ SignedOptionList.toSignedList e = []) ∨
  (SignedOptionList.toSignedList c = [(j, true)] ∧ SignedOptionList.toSignedList d = [(i, true), (j, false)] ∧ SignedOptionList.toSignedList e = [(i, false)]) ∨
  (SignedOptionList.toSignedList c = [(j, true)] ∧ SignedOptionList.toSignedList d = [(i, true)] ∧ SignedOptionList.toSignedList e = [(j, false), (i, false)]) ∨
  (SignedOptionList.toSignedList c = [(j, true), (i, true)] ∧ SignedOptionList.toSignedList d = [(j, false), (i, false)] ∧ SignedOptionList.toSignedList e = []) ∨
  (SignedOptionList.toSignedList c = [(j, true), (i, true)] ∧ SignedOptionList.toSignedList d = [(j, false)] ∧ SignedOptionList.toSignedList e = [(i, false)]) ∨
  (SignedOptionList.toSignedList c = [(j, true), (i, true)] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = [(j, false), (i, false)]) := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [SignedOptionList.toSignedList]
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [SignedOptionList.toSignedList_append] at h2
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
    rw [SignedOptionList.toSignedList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    simp_all
    rename_i j'
    have H : SignedOptionList.toSignedList n = [] ∨ SignedOptionList.toSignedList n = [(i, false)] ∨
      SignedOptionList.toSignedList n = [(j', false), (i, false)] := by aesop
    rcases H with h3 | h4 | h5
    · have H := partial_grid_rm_empty_helper g2 h3 o_is
      aesop
    · have H := partial_grid_rm_side_helper g2 h4 o_is
      aesop
    have H := partial_grid_rm_side_helper_w g2 h5 o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [SignedOptionList.toSignedList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      simp_all
      have H := partial_grid_rm_top_helper_w g2 g1_ih.1 n_is
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i k l m n o p q r s
    rw [SignedOptionList.toSignedList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨p_is, k_is⟩ | ⟨p_is, k_is⟩
    · specialize g1_ih k_is h2
      have H : SignedOptionList.toSignedList m = [] ∨ SignedOptionList.toSignedList m = [(j, true)] ∨ SignedOptionList.toSignedList m = [(j, true), (i, true)] := by
        rcases g1_ih with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
        any_goals apply Or.inl h1.1
        any_goals apply Or.inr (Or.inl h1.1)
        any_goals apply Or.inr (Or.inr h1.1)
      rcases H with h1 | h1 | h1
      · have H := partial_grid_rm_empty_helper g2 p_is h1
        simp only [H.1, true_and, SignedOptionList.toSignedList_append, H.2.1, H.2.2, List.nil_append]
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
      aesop
    simp_all
    have H := partial_grid_rm_side_helper g2 p_is h1.1
    aesop

theorem partial_grid_rm_separated_helper (h : PartialGrid a b c d e) (h1 : SignedOptionList.toSignedList a = [(i, false)])
    (h2 : SignedOptionList.toSignedList b = [(j, true)]) (hij : i.dist j > 1): (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(i, false), (j, true)] ∧ SignedOptionList.toSignedList e = []) ∨
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(j, true), (i, false)] ∧ SignedOptionList.toSignedList e = [])  ∨
    (SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList d = [(j, true)] ∧ SignedOptionList.toSignedList e = [(i, false)]) ∨
    (SignedOptionList.toSignedList c = [(j, true)] ∧ SignedOptionList.toSignedList d = [(i, false)] ∧ SignedOptionList.toSignedList e = []) ∨
    (SignedOptionList.toSignedList c = [(j, true)] ∧ SignedOptionList.toSignedList d = [] ∧ SignedOptionList.toSignedList e = [(i, false)]) := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [SignedOptionList.toSignedList]
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [SignedOptionList.toSignedList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_side_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [SignedOptionList.toSignedList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    simp_all
    have n_is : SignedOptionList.toSignedList n = [] ∨ SignedOptionList.toSignedList n = [(i, false)] := by aesop
    rcases n_is with hn | hn
    · have H := partial_grid_rm_empty_helper g2 hn o_is
      aesop
    have H := partial_grid_rm_side_helper g2 hn o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [SignedOptionList.toSignedList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      rename_i j'
      have l_nil : SignedOptionList.toSignedList l = [] ∨ SignedOptionList.toSignedList l = [(j', true)]:= by aesop
      rcases l_nil with hl | hl
      · have H := partial_grid_rm_empty_helper g2 n_is hl
        aesop
      have H := partial_grid_rm_top_helper g2 n_is hl
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [SignedOptionList.toSignedList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · specialize g1_ih j_is h2
      rename_i j'
      have l_nil : SignedOptionList.toSignedList l = [] ∨ SignedOptionList.toSignedList l = [(j', true)]:= by aesop
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

def suffix_of_singleton_c (h : List.SuffixData l [a]) : PLift (l = []) ⊕ PLift (l = [a]) := by
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

def prefix_of_singleton_c (h : List.PrefixData l [a]) : PLift (l = []) ⊕ PLift (l = [a]) := by
  rcases h with ⟨r, ⟨hr⟩⟩
  match r with
  | [] => right; constructor; aesop
  | r1 :: r2 =>
    apply congr_arg List.length at hr
    simp at hr
    have H : l.length = 0 := by omega
    left; constructor
    aesop

-- theorem unique_g_pg_c
--     (g1 : PartialGrid a2 b2 bot2 [] up2)
--     (ha : to_vertical_edge a1 = a2)
--     (b4_is : to_horizontal_edge b4 = b2)
--     (b9 : gridt a1 b4 b6 b7) : to_vertical_edge_plain b6 = SignedOptionList.toSignedList up2 ∧ to_horizontal_edge_plain b7 = SignedOptionList.toSignedList bot2 := by
--     have H := gridt_of_PartialGrid g1
--     unfold gridt_option at H
--     have H3 := unicity_c b9 H
--     rw [← ha, ← b4_is] at H3
--     specialize H3 toList_up_rev.symm toList_over.symm
--     rw [← H3.1.1, ← H3.2.1]
--     constructor
--     · apply to_vertical_edge_plain_toList_rev_eq_SignedOptionList.toSignedList
--       exact g1.right_frontier_is_false
--     apply to_horizontal_edge_plain_toList_eq_SignedOptionList.toSignedList
--     exact g1.bottom_frontier_is_true

theorem unique_g_pg_c_ones_okay
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_vertical_edge_plain a1 = SignedOptionList.toSignedList a2)
    (b4_is : to_horizontal_edge_plain b4 = SignedOptionList.toSignedList b2)
    (b9 : GridData a1 b4 b7 b6) : to_vertical_edge_plain b6 = SignedOptionList.toSignedList up2 ∧ to_horizontal_edge_plain b7 = SignedOptionList.toSignedList bot2 := by
    have ha1 : a1 = toList a2.reverse := by
      rw [← to_vertical_edge_plain_toList_rev_eq_SignedOptionList.toSignedList] at ha
      · exact to_vertical_edge_plain_inj ha
      exact g1.left_frontier_is_false
    have hb4 : b4 = toList b2 := by
      rw [← to_horizontal_edge_plain_toList_eq_SignedOptionList.toSignedList] at b4_is
      · exact to_horizontal_edge_plain_inj b4_is
      exact g1.top_frontier_is_true
    have H := GridData_of_PartialGrid g1
    unfold GridData_option at H
    have H3 := GridData.unicity b9 H
    specialize H3 ha1 hb4
    rw [← H3.1.1, ← H3.2.1]
    constructor
    · apply to_vertical_edge_plain_toList_rev_eq_SignedOptionList.toSignedList
      exact g1.right_frontier_is_false
    apply to_horizontal_edge_plain_toList_eq_SignedOptionList.toSignedList
    exact g1.bottom_frontier_is_true

theorem to_horizontal_edge_plain_prod (a b : FreeMonoid ℕ) : to_horizontal_edge_plain (a * b) = to_horizontal_edge_plain a ++ to_horizontal_edge_plain b := by
  have H : to_horizontal_edge_plain a ++ to_horizontal_edge_plain b = to_horizontal_edge_plain (a.toList ++ b.toList) := by
    simp [to_horizontal_edge_plain]
    convert
    rfl
  rw [H]
  convert
  rfl

theorem to_vertical_edge_plain_prod (a b : FreeMonoid ℕ) : to_vertical_edge_plain (a * b) = to_vertical_edge_plain b ++ to_vertical_edge_plain a := by
  have H : to_vertical_edge_plain b ++ to_vertical_edge_plain a = to_vertical_edge_plain (a.toList ++ b.toList) := by
    simp [to_vertical_edge_plain]
    convert
    rfl
  rw [H]
  convert
  rfl

theorem same_time (h : GridData i j l k) (h1 : PartialGrid a b mid d2 e2)
  : (SignedOptionList.toSignedList a = to_vertical_edge_plain i → SignedOptionList.toSignedList b <+: to_horizontal_edge_plain j → SignedOptionList.toSignedList mid <+: to_horizontal_edge_plain l)
  ∧ (SignedOptionList.toSignedList b = to_horizontal_edge_plain j → SignedOptionList.toSignedList a <:+ to_vertical_edge_plain i → SignedOptionList.toSignedList e2 <:+ to_vertical_edge_plain k) := by
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
      have H : SignedOptionList.toSignedList mid = [] ∨ SignedOptionList.toSignedList mid = [(k, true)] ∨
        SignedOptionList.toSignedList mid = [(k, true), (i, true)] := by aesop
      change _ <+: [(k, true), (i, true)]
      aesop
    intro b_is a_is
    rcases suffix_of_singleton a_is with h3 | h4
    · have H := partial_grid_rm_top_helper h1 h3 b_is
      aesop
    have H := partial_grid_rm_adjacent_helper h1 h4 b_is h
    have H : SignedOptionList.toSignedList mid = [] ∨ SignedOptionList.toSignedList mid = [(k, true)] ∨
        SignedOptionList.toSignedList mid = [(k, true), (i, true)] := by aesop
    change _ <:+ [(k, false), (i, false)]
    aesop
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
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    constructor
    · intro ha hb
      have ha1 : m = [] ∨ q = [] ∨ ∃ a1 a2, a1.length > 0 ∧ a2.length > 0 ∧
          a = a1 ++ a2 ∧ SignedOptionList.toSignedList a1 = to_vertical_edge_plain q ∧ SignedOptionList.toSignedList a2 = to_vertical_edge_plain m :=
        SignedOptionList.toSignedList_eq_to_vertical_edge_plain_prod ha
      rcases ha1 with m_nil | q_nil | ⟨a1, a2, a1_len, a2_len, ha1, a1q, a2m⟩
      · have H : SignedOptionList.toSignedList a = to_vertical_edge_plain q := by
          rw [m_nil] at ha
          convert ha
        have on := GridData.DeterminativeSpine.one_word t m_nil
        specialize h2_ih h1
        have new_h2_ih := h2_ih.1 H
        rw [on.1] at new_h2_ih
        exact new_h2_ih hb
      · have H : SignedOptionList.toSignedList a = to_vertical_edge_plain m := by
          rw [q_nil] at ha
          convert ha
          change m = m.toList ++ [] -- i need a helper here! this is utter chaos
          erw [List.append_nil]; rfl
        have rs := GridData.DeterminativeSpine.one_word h2 q_nil
        specialize h1_ih h1
        have new_h2_ih := h1_ih.1 H hb
        rw [rs.1]
        exact new_h2_ih
      rcases splittable_horizontally_of_pg h1 _ _ ha1 a2_len a1_len
        with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
      · specialize h1_ih i1
        have new_h1_ih := h1_ih.1 a2m hb
        exact (h2_ih i2).1 a1q new_h1_ih
      rcases baaad with ⟨_, _, _, _, _, _, ⟨mid_nil⟩, _⟩
      aesop
    intro hb ha
    have ha1 : SignedOptionList.toSignedList a <:+ to_vertical_edge_plain q ++ to_vertical_edge_plain m := by
      rw [to_vertical_edge_plain_prod m q] at ha
      exact ha
    rw [to_vertical_edge_plain_prod]
    match m with
    | [] =>
      nth_rewrite 2 [to_vertical_edge_plain] at ha1
      simp at ha1
      specialize h2_ih h1
      have on := GridData.DeterminativeSpine.one_word t rfl
      rw [← on.1] at hb
      have h_new := h2_ih.2 hb ha1
      rw [on.2]
      nth_rewrite 2 [to_vertical_edge_plain]
      simp
      change _ <:+ _ ++ []
      erw [List.append_nil]
      exact h_new
    | m1 :: m2 =>
      have H : SignedOptionList.toSignedList a <:+ to_vertical_edge_plain (m1 :: m2) ∨
        ∃ a1 a2, a1.length > 0 ∧ a = a1 ++ a2 ∧
        SignedOptionList.toSignedList a2 = to_vertical_edge_plain  (m1 :: m2) ∧ SignedOptionList.toSignedList a1 <:+ to_vertical_edge_plain q := by
        exact helper_bajillion ha1
      rcases H with ha1 | ⟨a1, a2, a1_len, a1_is, ha11⟩
      · have H2 := (h1_ih h1).2 hb ha1
        exact suffix_of_append H2
      have a2_len : a2.length > 0 := by
        have H := SignedOptionList.toSignedList_len a2
        rw [ha11.1] at H
        simp [to_vertical_edge_plain] at H
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
        rw [fb.2.2, SignedOptionList.toSignedList_append, H.1]
        refine List.suffix_append_right ?_
        exact (h2_ih i2).2 H.2.symm ha11.2
      rcases baaad with ⟨db, c11, drest, h3, ⟨d2_is⟩, ⟨a1_is⟩, ⟨mid_nil⟩, len3⟩
      specialize h1_ih h3
      have H2 := h1_ih.2 hb (by rw [ha11.1])
      exact suffix_of_append H2
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    constructor
    · intro a_is b_is
      rw [to_horizontal_edge_plain_prod] at b_is
      match n with
      | [] =>
        have H := GridData.DeterminativeSpine.word_one t rfl
        specialize h2_ih h1
        simp_all [to_horizontal_edge_plain]
      | n1 :: n2 =>
        rcases helper_kajillion b_is (by simp) with one | two
        · specialize h1_ih h1
          have new_ih := h1_ih.1 a_is one
          rw [to_horizontal_edge_plain_prod]
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
            rw [h_one.1, h_one.2, List.append_nil, SignedOptionList.toSignedList_append, to_horizontal_edge_plain_prod, H.2]
            exact (List.prefix_append_right_inj (SignedOptionList.toSignedList d3)).mpr ((h2_ih).1 H.1.symm)
          have helper := h1_ih.1
          rw [h_two.1, to_horizontal_edge_plain_prod]
          exact List.prefix_of_append helper
        rcases baaad with ⟨db, drest, h3, ⟨d2_is⟩, ⟨a1_is⟩, ⟨mid_nil⟩, len3⟩
        specialize h1_ih h3
        have H2 := h1_ih.1 a_is (by rw [b1_n])
        rw [to_horizontal_edge_plain_prod]
        exact List.prefix_of_append H2
    intro b_is a_is
    have hb1 : n = [] ∨ q = [] ∨ ∃ b1 b2, b1.length > 0 ∧ b2.length > 0 ∧
        b = b1 ++ b2 ∧ SignedOptionList.toSignedList b1 = to_horizontal_edge_plain n ∧ SignedOptionList.toSignedList b2 = to_horizontal_edge_plain q :=
      SignedOptionList.toSignedList_eq_to_horizontal_edge_plain_prod b_is
    rcases hb1 with n_nil | q_nil | ⟨b1, b2, b1_len, b2_len, b1_is, b1n, b2q⟩
    · have H : SignedOptionList.toSignedList b = to_horizontal_edge_plain q := by
        rw [n_nil] at b_is
        convert b_is
      have op := GridData.DeterminativeSpine.word_one t n_nil
      specialize h2_ih h1
      have new_h2_ih := h2_ih.2 H
      rw [op.2] at new_h2_ih
      exact new_h2_ih a_is
    · have H : SignedOptionList.toSignedList b = to_horizontal_edge_plain n := by
        rw [q_nil] at b_is
        convert b_is
        change n = n.toList ++ []
        erw [List.append_nil]; rfl
      have rs := GridData.DeterminativeSpine.word_one h2 q_nil
      specialize h1_ih h1
      have new_h2_ih := h1_ih.2 H a_is
      rw [rs.2]
      exact new_h2_ih
    rcases splittable_vertically_of_pg' h1 _ _ b1_is b1_len b2_len
        with ⟨mid4, d4, e4, e5, d5, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · specialize h1_ih i1
      specialize h2_ih i2
      simp_all
    rcases baaad with ⟨d5, d6, i3, _ , ⟨e2_nil⟩, ⟨d2_is⟩, ⟨b2_is⟩⟩
    aesop

theorem SuffixData_of_nil (h : List.SuffixData a []) : a = [] := by
  rcases h with ⟨b, ⟨hb⟩⟩
  simp at hb
  aesop

theorem PrefixData_of_nil (h : List.PrefixData a []) : a = [] := by
  rcases h with ⟨b, ⟨hb⟩⟩
  aesop

noncomputable def prefix_to_c (h : a <+: b) : List.PrefixData a b := by
  rw [← h.choose_spec]
  exact List.PrefixData.append_self

noncomputable def suffix_to_c (h : a <:+ b) : List.SuffixData a b := by
  rw [← h.choose_spec]
  exact List.SuffixData.append_self

theorem prefix_from_c (h : List.PrefixData a b) : a <+: b := by
  rcases h with ⟨c, hc⟩
  rw [← hc.1]
  exact List.prefix_append a c

theorem suffix_from_c (h : List.SuffixData a b) : a <:+ b := by
  rcases h with ⟨c, hc⟩
  rw [← hc.1]
  exact List.suffix_append c a

noncomputable def same_time_c (h : GridData i j l k) (h1 : PartialGrid a b mid d2 e2)
  : (SignedOptionList.toSignedList a = to_vertical_edge_plain i → List.PrefixData (SignedOptionList.toSignedList b) (to_horizontal_edge_plain j) → List.PrefixData (SignedOptionList.toSignedList mid) (to_horizontal_edge_plain l))
  × (SignedOptionList.toSignedList b = to_horizontal_edge_plain j → List.SuffixData (SignedOptionList.toSignedList a) (to_vertical_edge_plain i) → List.SuffixData (SignedOptionList.toSignedList e2) (to_vertical_edge_plain k)) := by
  constructor
  · intro ha hb
    have H := (same_time h h1).1 ha (prefix_from_c hb)
    exact prefix_to_c H
  intro hb ha
  have H := (same_time h h1).2 hb (suffix_from_c ha)
  exact suffix_to_c H
