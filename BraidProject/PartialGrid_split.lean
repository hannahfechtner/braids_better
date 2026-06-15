import BraidProject.GridData_length
import BraidProject.PartialGrid
import BraidProject.SignedOptionList

open Braid

theorem all_ones_length_pg (h : PartialGrid a b c d e) : a = [(none, false)] → b = [(none, true)] → h.length = 0 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i =>
      intro h1
      simp [to_vertical_edge] at h1
    | adjacent i k h =>
      intro h1
      simp [to_vertical_edge] at h1
    | separated i j h =>
      intro h1
      simp [to_vertical_edge] at h1
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
  | single_cell h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i =>  simp [PartialGrid.length]
    | sides i =>  simp [PartialGrid.length]
    | top_left i =>
      intro ha
      simp [to_vertical_edge] at ha
    | adjacent i k h =>
      intro ha
      simp [to_vertical_edge] at ha
    | separated i j h =>
      intro ha
      simp [to_vertical_edge] at ha
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
  | single_cell h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i =>  simp [PartialGrid.length]
    | sides i =>  simp [PartialGrid.length]
    | top_left i =>
      intro ha hb
      simp [to_horizontal_edge] at hb
    | adjacent i k h =>
      intro ha hb
      simp [to_horizontal_edge] at hb
    | separated i j h =>
      intro ha hb
      simp [to_horizontal_edge] at hb
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

open SignedOptionList
theorem top_left_length_pg {a b c d e i} (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some i, true)] →
  toSignedList (c ++ d ++ e) = [] → h.length = 1 := by
  induction h with
  | single_cell h =>
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
    simp [toSignedList] at rm
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
    toSignedList (c ++ d ++ e) = [(j, true), (i, true), (j, false), (i, false)] → i.dist j = 1 → h.length = 1 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h => simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro a_is b_is rm
    simp [a_is, b_is, toSignedList] at rm
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
    toSignedList (c ++ d ++ e) = [(k, true), (i, false)] → i.dist k > 1 → h.length = 1 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h => simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro a_is b_is rm
    simp [a_is, b_is, toSignedList] at rm
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

-- def split_vertically_pg_1 (h : PartialGrid a b c d e)  := ∀ b₁ b₂, b = b₁ ++ b₂ →
--   b₁.length > 0 → b₂.length > 0 →
--   (Σ mid c1 d1 c2 d2,
--   (h1 : PartialGrid a b₁ c1 d1 mid) × (h2 : PartialGrid mid b₂ c2 d2 e) ×
--   PLift (c ++ d = c1 ++ d1 ++ c2 ++ d2) ×
--   PLift (h.length = h1.length + h2.length) ×
--     (∀ {c3 m3 c4 d4}, PartialGrid a b₁ c3 [] m3 → PartialGrid m3 b₂ c4 d4 e →
--       PLift (c3 ++ c4 = c → d4 = d → c1 = c3 ∧ mid = m3 ∧ d1 = [] ∧ c2 = c4 ∧ d2 = d4))) ⊕
--   (Σ d1 d2, (h1 : PartialGrid a b₁ c d1 []) × PLift (h.length = h1.length) ×
--     PLift (e = []) × PLift (d = d1 ++ d2) × PLift (b₂ = d2))

def List.append_eq_singleton_C (h : a ++ b = [c]) : PLift (a = [] ∧ b = [c]) ⊕ PLift (a = [c] ∧ b = []) := by
  induction a with
  | nil =>
    simp only [nil_append] at h
    exact Sum.inl ⟨rfl, h⟩
  | cons x xs ih =>
    simp at h
    right
    constructor
    simp [h]

open FreeMonoid

/-- An induction principle on free monoids, with cases for `1`, `FreeMonoid.of` and `*`. -/
@[to_additive (attr := elab_as_elim, induction_eliminator)
/--An induction principle on free monoids, with cases for `0`, `FreeAddMonoid.of` and `+`.-/]
def FreeMonoid.inductionOn'' {C : FreeMonoid α → Type} (z : FreeMonoid α) (one : C 1)
    (of : ∀ (x : α), C (FreeMonoid.of x)) (mul : ∀ (x y : FreeMonoid α), C x → C y → C (x * y)) :
  C z := List.rec one (fun _ _ ih => mul [_] _ (of _) ih) z

/-- An induction principle for free monoids which mirrors induction on lists, with cases analogous
to the empty list and cons -/
@[to_additive (attr := elab_as_elim) self /--An induction principle for free monoids which mirrors
induction on lists, with cases analogous to the empty list and cons-/]
def FreeMonoid.inductionOn''' {p : FreeMonoid α → Type} (a : FreeMonoid α)
    (one : p (1 : FreeMonoid α)) (mul_of : ∀ b a, p a → p (of b * a)) : p a :=
  List.rec one (fun _ _ tail_ih => mul_of _ _ tail_ih) a

def FreeMonoid.prod_eq_prod' {a b c d : FreeMonoid α} (h : a * b = c * d) :
  (Σ from_middle, PLift (c = a * from_middle) × PLift (b = from_middle * d)) ⊕
  (Σ to_middle, PLift (a = c * to_middle) × PLift (d = to_middle * b)) := by
  induction a using FreeMonoid.inductionOn''' generalizing c with
  | one =>
    simp_all
    left
    use c
    exact ⟨{down := rfl}, {down := rfl}⟩
  | mul_of a as ih =>
    cases c
    · right
      use of a * as
      simp [h]
      exact ⟨{down := trivial}, {down := trivial}⟩
    rename_i x xs
    cases ih (parts_eq h).2
    · rename_i hv
      left
      use hv.1
      simp [hv.2.1.1, hv.2.2.1, ← (parts_eq h).1]
      exact ⟨{down := by rw [← mul_assoc]}, {down := trivial}⟩
    rename_i hv
    right
    use hv.1
    simp [hv.2.1.1, hv.2.2.1, ← (parts_eq h).1]
    exact ⟨{down := by rw [← mul_assoc]}, {down := trivial}⟩

def FreeMonoid.prod_eq_of' {a b : FreeMonoid α} {i : α} (h : a * b = FreeMonoid.of i) :
    (PLift (a = 1) × PLift (b = FreeMonoid.of i)) ⊕
  (PLift (a = FreeMonoid.of i) × PLift (b = 1)) := by
  have H : FreeMonoid.length (a * b) = 1 := by
    rw [h]
    exact FreeMonoid.length_of _
  rw [FreeMonoid.length_mul] at H
  match ha : length a with
  | 0 =>
    have a_eq : a = 1 := length_eq_zero.mp ha
    have b_eq : b = of i := by rw [a_eq, one_mul] at h; exact h
    exact Sum.inl ⟨⟨length_eq_zero.mp ha⟩, ⟨b_eq⟩⟩
  | (n + 1) =>
    have b_eq : b = 1 := length_eq_zero.mp (by omega)
    have a_eq : a = of i := by rw [b_eq, mul_one] at h; exact h
    exact Sum.inr ⟨⟨a_eq⟩, ⟨b_eq⟩⟩

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
  | single_cell h =>
    intro ha hb
    simp [to_vertical_edge] at hb
    rename_i c _
    match c with
    | [] => split at hb; simp at hb; aesop
    | c1 :: c2 => split at hb; simp at hb; aesop
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
  | single_cell h =>
    intro ha hb
    simp [to_horizontal_edge] at ha
    rename_i c
    match c with
    | [] => split at ha; simp at ha; aesop
    | c1 :: c2 => split at ha; simp at ha; aesop
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

open SignedList
-- de.ete the other extends mahybe?
noncomputable def PartialGrid.extend_bottom_w_len (h : PartialGrid a b c d e) (a2) (h2 : is_false a2) (h3 : a2 ≠ []) :
    (h1 : PartialGrid (a2 ++ a) b [] (a2 ++ c ++ d) e) × PLift (h.length = h1.length):= by
  induction h with
  | single_cell h =>
    cases a2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i c d
      rw [List.append_nil]
      have H := PartialGrid.vertical_append_one (PartialGrid.single_cell h)
        (PartialGrid.empty (head :: tail) (to_horizontal_edge c) (by simp) h2 to_horizontal_edge_length_pos is_true_to_horizontal_edge)
      use PartialGrid.vertical_append_one (PartialGrid.single_cell h)
        (PartialGrid.empty (head :: tail) (to_horizontal_edge c) (by simp) h2 to_horizontal_edge_length_pos is_true_to_horizontal_edge)
      constructor
      simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, ← List.append_assoc]
    use PartialGrid.empty (a2 ++ a) b (by rw [List.length_append]; omega) (SignedList.is_false_append h2 ha1) (by assumption) hb
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

noncomputable def splittable_vertically_of_pg' (h : PartialGrid a b c d e) : split_vertically_pg' h := by
  induction h with
  | single_cell h =>
    cases h with
    | empty =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_horizontal_edge] at b_is
      apply congr_arg List.length at b_is
      simp only [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | top_bottom i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_horizontal_edge] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | sides i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_horizontal_edge] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | top_left i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_horizontal_edge] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | adjacent i k h =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_horizontal_edge] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | separated i j h =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_horizontal_edge] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
  | empty a b ha ha1 hb hb1 =>
    intro b₁ b₂ b_is b₁_len b₂_len
    right
    use a ++ b₁
    have itb₁ : is_true b₁ := by
      rw [b_is] at hb1
      exact (is_true_of_append hb1).1
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
        simp only [List.append_assoc, List.append_nil, PartialGrid.length]
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
          have H2 := PartialGrid.middle_frontier_spec h2
          rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
          · simp at H2
            exact H2.1.elim
          rw [spec.1] at H
          specialize H (front, false)
          simp at H
      | d11 :: d12 =>
        have H : is_true bot1 := by exact g2.top_frontier_is_true
        simp only [List.append_nil, List.append_assoc] at long
        rw [long] at H
        have H2 := PartialGrid.middle_frontier_spec h1
        rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
        · simp at H2
          exact H2.1.elim
        rw [spec.1] at H
        specialize H (front, false)
        simp at H
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
            is_true_append h1.bottom_frontier_is_true h2.bottom_frontier_is_true
        have bot1_is : bot1 = c1 ++ c2 := by
          rw [List.append_nil] at long
          rcases PartialGrid.middle_frontier_spec g1 with H | ⟨front, mid, caboose, spec⟩
          · rw [H.1] at h
            simp at h
          rw [spec.1] at long
          simp only [List.cons_append, List.nil_append, List.append_assoc] at long
          rcases PartialGrid.middle_frontier_spec h2 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp only [H.1, List.append_nil] at long
            rw [← long] at both_c
            specialize both_c (front, false)
            simp at both_c
          rw [spec1.1] at long
          simp only [List.cons_append, List.nil_append] at long
          have := SignedList.eq_of_is_true_append_false_append_eq (g2.top_frontier_is_true) both_c
            (by simp only [List.append_assoc, List.cons_append, List.nil_append]; exact long)
          aesop
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
          rcases PartialGrid.middle_frontier_spec h1 with H | ⟨front, mid, caboose, spec⟩
          · simp at H
            exact H.1.elim
          rw [spec.1] at long
          rcases PartialGrid.middle_frontier_spec g1 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp [H.1] at long
            rw [long] at H0
            specialize H0 (front, false)
            simp at H0
          rw [spec1.1] at long
          simp at long
          have := SignedList.eq_of_is_true_append_false_append_eq (g2.top_frontier_is_true) h1.bottom_frontier_is_true
            (by simp only [List.append_assoc, List.cons_append, List.nil_append]; exact long)
          grind
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

theorem bool_swap_to_horizontal_edge : bool_swap (to_horizontal_edge a) = to_vertical_edge a := by
  cases a with
  | nil => simp [to_horizontal_edge, to_vertical_edge, bool_swap]
  | cons head tail =>
    simp [bool_swap, to_horizontal_edge,to_vertical_edge]

theorem bool_swap_to_vertical_edge : bool_swap (to_vertical_edge a) = to_horizontal_edge a := by
  cases a with
  | nil => simp [to_horizontal_edge, to_vertical_edge, bool_swap]
  | cons head tail =>
    simp [bool_swap, to_vertical_edge, to_horizontal_edge]

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
  specialize h (a1, false) a1_in
  simp at h

def bool_swap_false (h : is_false a) : is_true (bool_swap a) := by
  simp [is_true, bool_swap]
  intro a1 a1_in
  specialize h (a1, true) a1_in
  simp at h

theorem nil_of_bool_swap_eq_nil (h : bool_swap a = []) : a = [] := by
  apply congr_arg bool_swap at h
  rw [bool_swap_idem, bool_swap_nil] at h
  exact h

open GridData in
noncomputable def reflect (h : PartialGrid a b c d e) :
    (h1 : PartialGrid (bool_swap b) (bool_swap a) (bool_swap e) (bool_swap d) (bool_swap c)) ×
    PLift (h.length = h1.length) := by
  induction h with
  | single_cell h =>
    rw [bool_swap_to_vertical_edge, bool_swap_to_horizontal_edge, bool_swap_to_vertical_edge, bool_swap_to_horizontal_edge, bool_swap_nil]
    cases h with
    | empty =>
      use PartialGrid.single_cell (CellData.empty)
      exact ⟨rfl⟩
    | top_bottom i =>
      use PartialGrid.single_cell (CellData.sides i)
      exact ⟨rfl⟩
    | sides i =>
      use PartialGrid.single_cell (CellData.top_bottom i)
      exact ⟨rfl⟩
    | top_left i =>
      use PartialGrid.single_cell (CellData.top_left i)
      exact ⟨rfl⟩
    | adjacent i k h =>
      use PartialGrid.single_cell (CellData.adjacent k i (by rw [Nat.dist_comm] at h; exact h))
      exact ⟨rfl⟩
    | separated i j h =>
      use PartialGrid.single_cell (CellData.separated j i (by rw [Nat.dist_comm] at h; exact h))
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
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]; rfl⟩
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
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]; rfl⟩
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

noncomputable def reflect_all (a b c d e) (h : PartialGrid a1 b1 c1 d1 e1) :
    a1 = bool_swap a → b1 = bool_swap b → c1 = bool_swap c → d1 = bool_swap d → e1 = bool_swap e →
    (h1 : PartialGrid b a e d c) × PLift (h.length = h1.length) := by
  intro a_eq b_eq c_eq d_eq e_eq
  apply congr_arg bool_swap at a_eq
  rw [bool_swap_idem] at a_eq
  rw [← a_eq]
  apply congr_arg bool_swap at b_eq
  rw [bool_swap_idem] at b_eq
  rw [← b_eq]
  apply congr_arg bool_swap at c_eq
  rw [bool_swap_idem] at c_eq
  rw [← c_eq]
  apply congr_arg bool_swap at d_eq
  rw [bool_swap_idem] at d_eq
  rw [← d_eq]
  apply congr_arg bool_swap at e_eq
  rw [bool_swap_idem] at e_eq
  rw [← e_eq]
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
  rw [H.2.1, len.1]
  exact H0.2.1

noncomputable def PartialGrid.extend_side_w_len  (h : PartialGrid a b c d e) (b2) (h2 : is_true b2) (h3 : b2 ≠ []) :
    (h1 : PartialGrid a (b ++ b2) c (d ++ e ++ b2) []) × PLift  (h.length = h1.length) := by
  rcases reflect h with ⟨h4, ⟨len⟩⟩
  have ⟨h5, ⟨len2⟩⟩ := PartialGrid.extend_bottom_w_len h4 (bool_swap b2) (bool_swap_true h2)
    (fun h => h3 (nil_of_bool_swap_eq_nil h))
  rcases reflect h5 with ⟨h6, ⟨len3⟩⟩
  rcases reflect_all _ _ _ _ _ h6 rfl rfl rfl rfl rfl with ⟨h7, ⟨len4⟩⟩
  have H7 := @reflect_all _ _ _ _ _ (b ++ b2) a [] (d ++ e ++ b2) c h7 (bool_swap_append).symm
    rfl bool_swap_nil (by simp [bool_swap_append]) rfl
  rcases H7 with ⟨h8, ⟨len5⟩⟩
  use h8
  constructor
  omega

theorem pg_empty {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(none, false)]) (hb : b = [(none, true)]) (hd : d = []) :
  c = [(none, true)] ∧ e = [(none, false)] := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [to_horizontal_edge, to_vertical_edge]
    | top_bottom i => simp [to_horizontal_edge] at hb
    | sides i => simp [to_vertical_edge] at ha
    | top_left i => simp [to_horizontal_edge] at hb
    | adjacent i k h => simp [to_horizontal_edge] at hb
    | separated i j h => simp [to_horizontal_edge] at hb
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
  | single_cell h =>
    cases h with
    | empty => simp [to_horizontal_edge] at hb
    | top_bottom i => simp [ha, hb]
    | sides i => simp [to_horizontal_edge] at hb
    | top_left i => simp [to_vertical_edge] at ha
    | adjacent i k h => simp [to_vertical_edge] at ha
    | separated i j h => simp [to_vertical_edge] at ha
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
  | single_cell h =>
    cases h with
    | empty => simp [to_vertical_edge] at ha
    | top_bottom i => simp [ha, hb]
    | sides i => simp [ha, hb]
    | top_left i => simp [to_horizontal_edge] at hb
    | adjacent i k h => simp [to_horizontal_edge] at hb
    | separated i j h => simp [to_horizontal_edge] at hb
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
  | single_cell h =>
    cases h with
    | empty => simp [to_vertical_edge] at ha
    | top_bottom i => simp [to_vertical_edge] at ha
    | sides i => simp [to_horizontal_edge] at hb
    | top_left i => simp
    | adjacent i k h =>
      simp [to_vertical_edge] at ha
      simp [to_horizontal_edge] at hb
      rw [ha, hb] at h
      aesop
    | separated i j h =>
      simp [to_vertical_edge] at ha
      simp [to_horizontal_edge] at hb
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
  | single_cell h =>
    cases h with
    | empty => simp [to_vertical_edge] at ha
    | top_bottom i => simp [to_vertical_edge] at ha
    | sides i => simp [to_horizontal_edge] at hb
    | top_left i =>
      simp [to_vertical_edge] at ha
      simp [to_horizontal_edge] at hb
      aesop
    | adjacent i k h =>
      simp [to_vertical_edge] at ha
      simp [to_horizontal_edge] at hb
      rw [ha, hb] at h
      simp [to_vertical_edge, to_horizontal_edge, ha, hb]
    | separated i j h =>
      simp [to_vertical_edge] at ha
      simp [to_horizontal_edge] at hb
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
  | single_cell h =>
    cases h with
    | empty => simp [to_vertical_edge] at ha
    | top_bottom i => simp [to_vertical_edge] at ha
    | sides i => simp [to_horizontal_edge] at hb
    | top_left i =>
      simp [to_vertical_edge] at ha
      simp [to_horizontal_edge] at hb
      aesop
    | adjacent i k h =>
      simp [to_vertical_edge] at ha
      simp [to_horizontal_edge] at hb
      aesop
    | separated i j h =>
      simp [to_vertical_edge] at ha
      simp [to_horizontal_edge] at hb
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
