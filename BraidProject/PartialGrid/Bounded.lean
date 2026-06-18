import BraidProject.PartialGrid.ToGrid
import BraidProject.PartialGrid.FrontierPossibilities
import BraidProject.PartialGrid.NestedFrame

namespace Braid

open SignedOptionList PartialGrid PartialGrid.FrontierPossibilitiesEpsilonRemovedBoolRemoved
theorem pg_sm_g_eq1 (h : PartialGrid a b c d e) (h1 : GridData a1 b1 g f)
    : toList (FreeGroup.invRev a) = a1 → toList b = b1 →
    h.length ≤ GridData.length h1 := by
  induction h1 generalizing a b c d e with
  | empty =>
    intro ha hb
    simp [empty_empty h ha hb]
  | top_bottom i =>
    intro ha hb
    simp [empty_generator h ha hb]
  | sides i =>
    intro ha hb
    simp [generator_empty h ha (toList_invRev_eq_nil_iff.mpr hb)]
  | top_left i =>
    intro ha hb
    have := generator_generator_same h ha hb
    rw [GridData.length]
    aesop
  | adjacent i k hd =>
    intro ha hb
    have := generator_generator_close h (toList_invRev_eq_singleton_iff.mp ha) hb hd
    rw [GridData.length]
    aesop
  | separated i j hd =>
    intro ha hb
    have := generator_generator_apart h (toList_invRev_eq_singleton_iff.mp ha) hb hd
    rw [GridData.length]
    aesop
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i i j k l m n o
    intro a_is b_is
    rcases toList_invRev_eq_append_cases a_is with one | two | splits
    · have i_one : i = 1 := by
        convert one
      rw [i_one, one_mul] at a_is
      specialize h2_ih h a_is
      have H := GridData.DeterminativeSpine.one_word h1 i_one
      have H : GridData.length h1 = 0 := GridData.DeterminativeSpineLength.one_word h1 one
      simp [H, GridData.length]
      apply h2_ih
      convert b_is
      aesop
    · have i_one : m = 1 := by
        convert two
      rw [i_one, mul_one] at a_is
      specialize h1_ih h a_is
      have H := GridData.DeterminativeSpine.one_word h2 i_one
      have H : GridData.length h2 = 0 := GridData.DeterminativeSpineLength.one_word h2 two
      simp [H, GridData.length]
      apply h1_ih
      exact b_is
    rcases splits with ⟨a1, a2, a1_len, a2_len, H, a1m, a2i⟩
    have H' := congr_arg FreeGroup.invRev H
    simp at H'
    rcases splittable_horizontally h _ _ H' a1_len a2_len
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl]
      have hi1 := h1_ih i1 a1m b_is
      have hi2 : i2.length ≤ GridData.length h2 := by
        have H : toList mid <+: k :=
          (PartialGrid.same_time h1 i1).1 a1m (by rw [b_is])
        rcases H with ⟨r, hr⟩
        match r_is : r with
        | [] =>
          rw [List.append_nil] at hr
          exact h2_ih i2 (a2i) hr
        | r1 :: r2 =>
          have i3 := PartialGrid.extend_top_side_w_length i2 (List.map (fun x => (some x, true)) (r1 :: r2))
            (by sorry) (by simp)
          specialize h2_ih i3.1 (a2i)
          subst hr
          simp [SignedOptionList.toList] at h2_ih
          rw [i3.2.1]
          apply h2_ih
          sorry --SignedOptionList.toSignedList_add_some_is_self
      simp [GridData.length]
      omega
    rcases baaad with ⟨ db, c1, drest, i1, ⟨long⟩, ⟨db_is⟩, ⟨c_nil⟩, ⟨len⟩⟩
    specialize h1_ih i1 a1m b_is
    simp [GridData.length]
    omega
  | horizontal h1 h2 h1_ih h2_ih =>
    intro a_is b_is
    rename_i i j k l m n o
    rcases SignedOptionList.toList_eq_append_cases b_is with one | two | splits
    · have i_one : j = 1 := by
        convert one
      rw [i_one, one_mul] at b_is
      have H := GridData.DeterminativeSpine.word_one h1 i_one
      rw [← H.2] at a_is
      specialize h2_ih h a_is b_is
      have H : GridData.length h1 = 0 := GridData.DeterminativeSpineLength.word_one h1 one
      simp [H, GridData.length, h2_ih]
    · have m_one : m = 1 := by
        convert two
      rw [m_one, mul_one] at b_is
      have H := GridData.DeterminativeSpine.word_one h2 m_one
      specialize h1_ih h a_is b_is
      have H : GridData.length h2 = 0 := GridData.DeterminativeSpineLength.word_one h2 two
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
          rw [List.append_nil] at hr
          exact h2_ih i2 hr b2m
        | r1 :: r2 =>
          have H := PartialGrid.extend_left_side_w_length i2
            (List.map (fun x => (some x, false)) (r1 :: r2)).reverse (by sorry) (by simp)
          rcases H with ⟨h3, ⟨len⟩⟩
          rw [len]
          have hk : toList (FreeGroup.invRev ((List.map (fun x ↦ (some x, false)) (r1 :: r2)).reverse ++ mid)) = l := by
            rw [FreeGroup.invRev_append, SignedOptionList.toList_append]
            rw [← hr]
            simp only [toList_invRev, List.map_cons, List.reverse_cons, FreeGroup.invRev_append,
              toList_append, toList, List.reverse_nil, List.nil_append, List.cons_append,
              List.append_cancel_left_eq, List.cons.injEq, true_and]
            sorry
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



open SignedList SignedOptionList PartialGrid FrontierPossibilitiesEpsilonRemoved
theorem partial_grid_rm_top_bottom_length (h : PartialGrid a b c d e) (ha : SignedOptionList.toSignedList a = []) (hb : SignedOptionList.toSignedList b = [(i, true)]) :
    SignedOptionList.toSignedList c <+: [(i, true)] ∧ SignedOptionList.toSignedList e = [] ∧ h.length = 0 := by
  sorry

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
  sorry

theorem partial_grid_rm_side_length (h : PartialGrid a b c d e) (ha : SignedOptionList.toSignedList a = [(i, false)]) (hb : SignedOptionList.toSignedList b = []) :
    SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList e <:+ [(i, false)] ∧ h.length = 0 := by
  sorry

theorem partial_grid_rm_side_length_w (h : PartialGrid a b c d e)
    (ha : SignedOptionList.toSignedList a = [(i1, false), (i2, false)]) (hb : SignedOptionList.toSignedList b = []) :
    SignedOptionList.toSignedList c = [] ∧ SignedOptionList.toSignedList e <:+ [(i1, false), (i2, false)] ∧ h.length = 0 := by
  sorry

theorem partial_grid_rm_top_left_length (h : PartialGrid a b c d e) (ha : SignedOptionList.toSignedList a = [(i, false)]) (hb : SignedOptionList.toSignedList b = [(i, true)]) :
    SignedOptionList.toSignedList c <+: [(i, true)] ∧ SignedOptionList.toSignedList e <:+ [(i, false)] ∧ h.length ≤ 1 := by
  sorry

theorem partial_grid_rm_adjacent_length (h : PartialGrid a b c d e)
    (ha : SignedOptionList.toSignedList a = [(i, false)]) (hb : SignedOptionList.toSignedList b = [(k, true)]) :
    SignedOptionList.toSignedList c <+: [(k, true), (i, true)] ∧ SignedOptionList.toSignedList e <:+ [(k, false), (i, false)] ∧ h.length ≤ 1 := by
  sorry

theorem partial_grid_rm_separated_length (h : PartialGrid a b c d e)
    (ha : SignedOptionList.toSignedList a = [(i, false)]) (hb : SignedOptionList.toSignedList b = [(j, true)]) (hd : i.dist j > 1) :
    SignedOptionList.toSignedList c <+: [(j, true)] ∧ SignedOptionList.toSignedList e <:+ [(i, false)] ∧ h.length ≤ 1 := by
  sorry

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
theorem pg_sm_g_eq1' (h : PartialGrid a b c d e) (h1 : GridData a1 b1 g f)
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
