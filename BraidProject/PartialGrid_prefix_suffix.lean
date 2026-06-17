import BraidProject.PartialGrid.FrontierPossibilities
import BraidProject.PartialGrid.DeterminativeSpine
import BraidProject.List_C
import BraidProject.Additions.List

set_option maxHeartbeats 1000000

namespace Braid

open List

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
  have mid1_f : is_false mid1 := i2.left_side_is_false
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



theorem unique_g_pg_c_ones_okay
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_vertical_edge_plain a1 = SignedOptionList.toSignedList a2)
    (b4_is : to_horizontal_edge_plain b4 = SignedOptionList.toSignedList b2)
    (b9 : GridData a1 b4 b7 b6) : to_vertical_edge_plain b6 = SignedOptionList.toSignedList up2 ∧ to_horizontal_edge_plain b7 = SignedOptionList.toSignedList bot2 := by
    have ha1 : a1 = toList a2.reverse := by
      rw [← to_vertical_edge_plain_toList_rev_eq_SignedOptionList.toSignedList] at ha
      · exact to_vertical_edge_plain_inj ha
      exact g1.left_side_is_false
    have hb4 : b4 = toList b2 := by
      rw [← to_horizontal_edge_plain_toList_eq_SignedOptionList.toSignedList] at b4_is
      · exact to_horizontal_edge_plain_inj b4_is
      exact g1.top_side_is_true
    have H := GridData.PartialGridStyle.of_PartialGrid g1
    unfold GridData.PartialGridStyle at H
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

open PartialGrid FrontierPossibilitiesEpsilonRemoved
theorem same_time (h : GridData i j l k) (h1 : PartialGrid a b mid d2 e2)
  : (SignedOptionList.toSignedList a = to_vertical_edge_plain i → SignedOptionList.toSignedList b <+: to_horizontal_edge_plain j → SignedOptionList.toSignedList mid <+: to_horizontal_edge_plain l)
  ∧ (SignedOptionList.toSignedList b = to_horizontal_edge_plain j → SignedOptionList.toSignedList a <:+ to_vertical_edge_plain i → SignedOptionList.toSignedList e2 <:+ to_vertical_edge_plain k) := by
  induction h generalizing a b mid d2 e2 with
  | empty =>
    constructor
    · intro a_is b_is
      change _ <+: [] at b_is
      simp at b_is
      have H := empty_empty h1 a_is b_is
      aesop
    intro b_is a_is
    change _ <:+ [] at a_is
    simp at a_is
    have H := empty_empty h1 a_is b_is
    aesop
  | top_bottom i =>
    constructor
    · intro a_is b_is
      rcases IsPrefix.of_singleton b_is with h3 | h4
      · have H2 := empty_empty h1 a_is h3
        aesop
      have H := empty_generator h1 a_is h4
      aesop
    intro b_is a_is
    change _ <:+ [] at a_is
    simp at a_is
    have H := empty_generator h1 a_is b_is
    aesop
  | sides i =>
    constructor
    · intro a_is b_is
      change _ <+: [] at b_is
      simp at b_is
      have H := generator_empty h1 b_is a_is
      aesop
    intro b_is a_is
    rcases IsSuffix.of_singleton a_is with h3 | h4
    · have H := empty_empty h1 h3 b_is
      aesop
    have H := generator_empty h1 b_is h4
    aesop
  | top_left i =>
    constructor
    · intro a_is b_is
      rcases IsPrefix.of_singleton b_is with h3 | h4
      · have H := generator_empty h1 h3 a_is
        aesop
      have H := generator_generator_same h1 a_is h4
      aesop
    intro b_is a_is
    rcases IsSuffix.of_singleton a_is with h3 | h4
    · have H := empty_generator h1 h3 b_is
      aesop
    have H := generator_generator_same h1 h4 b_is
    aesop
  | adjacent i k h =>
    constructor
    · intro a_is b_is
      rcases IsPrefix.of_singleton b_is with h3 | h4
      · have H := generator_empty h1 h3 a_is
        aesop
      have H := partial_grid_rm_adjacent_helper h1 a_is h4 h
      have H : SignedOptionList.toSignedList mid = [] ∨ SignedOptionList.toSignedList mid = [(k, true)] ∨
        SignedOptionList.toSignedList mid = [(k, true), (i, true)] := by aesop
      change _ <+: [(k, true), (i, true)]
      aesop
    intro b_is a_is
    rcases IsSuffix.of_singleton a_is with h3 | h4
    · have H := empty_generator h1 h3 b_is
      aesop
    have H := partial_grid_rm_adjacent_helper h1 h4 b_is h
    have H : SignedOptionList.toSignedList mid = [] ∨ SignedOptionList.toSignedList mid = [(k, true)] ∨
        SignedOptionList.toSignedList mid = [(k, true), (i, true)] := by aesop
    change _ <:+ [(k, false), (i, false)]
    aesop
  | separated i j h =>
    constructor
    · intro a_is b_is
      rcases IsPrefix.of_singleton b_is with h3 | h4
      · have H := generator_empty h1 h3 a_is
        aesop
      have H := generator_generator_apart h1 a_is h4 h
      aesop
    intro b_is a_is
    rcases IsSuffix.of_singleton a_is with h3 | h4
    · have H := empty_generator h1 h3 b_is
      aesop
    have H := generator_generator_apart h1 h4 b_is h
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
      rcases PartialGrid.splittable_horizontally h1 _ _ ha1 a2_len a1_len
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
      rcases PartialGrid.splittable_horizontally h1 _ _ a1_is a2_len a1_len
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
        rcases PartialGrid.splittable_vertically h1 _ _ b_is b1_len b2_len
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
    rcases PartialGrid.splittable_vertically h1 _ _ b1_is b1_len b2_len
        with ⟨mid4, d4, e4, e5, d5, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · specialize h1_ih i1
      specialize h2_ih i2
      simp_all
    rcases baaad with ⟨d5, d6, i3, _ , ⟨e2_nil⟩, ⟨d2_is⟩, ⟨b2_is⟩⟩
    aesop

noncomputable def same_time_c (h : GridData i j l k) (h1 : PartialGrid a b mid d2 e2)
  : (SignedOptionList.toSignedList a = to_vertical_edge_plain i → List.PrefixData (SignedOptionList.toSignedList b) (to_horizontal_edge_plain j) → List.PrefixData (SignedOptionList.toSignedList mid) (to_horizontal_edge_plain l))
  × (SignedOptionList.toSignedList b = to_horizontal_edge_plain j → List.SuffixData (SignedOptionList.toSignedList a) (to_vertical_edge_plain i) → List.SuffixData (SignedOptionList.toSignedList e2) (to_vertical_edge_plain k)) := by
  constructor
  · intro ha hb
    have H := (same_time h h1).1 ha (PrefixData.to_IsPrefix hb)
    exact PrefixData.from_IsPrefix H
  intro hb ha
  have H := (same_time h h1).2 hb (SuffixData.to_IsSuffix ha)
  exact SuffixData.from_IsSuffix ((same_time h h1).2 hb (SuffixData.to_IsSuffix ha))
