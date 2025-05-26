import BraidProject.BraidMonoid
import BraidProject.Grids
import Mathlib.Data.Nat.Dist
open FreeMonoid

/-- a reversing gridl, inductively defined as the set of basic cells, and a vertical and horizontal
closure under appending-/
inductive gridl : List (Option ℕ) → List (Option ℕ) → List (Option ℕ) → List (Option ℕ) → Type
  | empty : gridl [none] [none] [none] [none]
  | top_bottom (i : ℕ) : gridl [none] [some i] [none] [some i]
  | sides (i : ℕ) : gridl [some i] [none] [some i] [none]
  | top_left (i : ℕ) : gridl [some i] [some i] [none] [none]
  | adjacent (i k : ℕ) (h : i.dist k = 1) : gridl [some i] [some k] [some i, some k] [some k, some i]
  | separated (i j : ℕ) (h : i.dist j > 1) : gridl [some i] [some j] [some i] [some j]
  | vertical (h1: gridl u v u' v') (h2 : gridl a v' c d) : gridl (u ++ a) v (u' ++ c) d
  | horizontal (h1: gridl u v u' v') (h2 : gridl u' b c d) : gridl u (v ++ b) c (v' ++ d)

noncomputable def gridl_swap : gridl a b c d → gridl b a d c := by
  intro h
  induction h with
  | empty => exact gridl.empty
  | top_bottom i => exact gridl.sides i
  | sides i => exact gridl.top_bottom i
  | top_left i => exact gridl.top_left i
  | adjacent i k h => exact gridl.adjacent k i (by rw [Nat.dist_comm] at h; exact h)
  | separated i j h => exact gridl.separated j i (by rw [Nat.dist_comm] at h; exact h)
  | vertical _ _ h1 h2 => exact gridl.horizontal h1 h2
  | horizontal _ _ h1 h2 => exact gridl.vertical h1 h2

def gridl_sides_word (u : List (Option ℕ)) (h1 : u.length ≥ 1): gridl u [none] u [none] := by
  induction u with
  | nil => simp at h1
  | cons head tail ih =>
    match tail with
    | [] =>
      match head with
      | none => exact gridl.empty
      | some i => exact gridl.sides (i)
    | t1 :: t2 =>
      match head with
      | none => exact gridl.vertical (gridl.empty) (ih (by simp))
      | some i => exact gridl.vertical (gridl.sides _) (ih (by simp))

def gridl_top_bottom_word (u : List (Option ℕ)) (h1 : u.length > 0): gridl [none] u [none] u := by
  induction u with
  | nil => simp at h1
  | cons head tail ih =>
    match tail with
    | [] =>
      match head with
      | none => exact gridl.empty
      | some i => exact gridl.top_bottom (i)
    | t1 :: t2 =>
      match head with
      | none => exact gridl.horizontal (gridl.empty) (ih (by simp))
      | some i => exact gridl.horizontal (gridl.top_bottom _) (ih (by simp))

def gridl_top_left_word (u : List (Option ℕ)) (h1 : u.length > 0): gridl u u [none] [none] := by
  induction u with
  | nil => simp at h1
  | cons head tail ih =>
    match tail with
    | [] =>
      match head with
      | none => exact gridl.empty
      | some i => exact gridl.top_left (i)
    | t1 :: t2 =>
      match head with
      | none =>
        sorry -- have H := gridl.vertical (gridl_top_bottom_word (t1 :: t2) (by simp)) (ih (by simp))

      | some i => sorry --exact gridl.horizontal (gridl.top_bottom _) (ih (by simp))
    -- exact gridl.vertical (gridl.horizontal one (gridl_top_bottom_word y))
    --   (gridl.horizontal (gridl_sides_word y) two)
def to_fm (a : List (Option ℕ)) : FreeMonoid ℕ := by
  match a with
  | [] => exact 1
  | none :: tail => exact to_fm tail
  | some i :: tail =>exact FreeMonoid.of i * to_fm tail

theorem to_fm_append {a b : List (Option ℕ)} : to_fm (a ++ b) = to_fm a * to_fm b := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | none =>
      simp [to_fm, ih]
    | some i => simp [to_fm, ih, mul_assoc]

/-- relating gridl equivalence to braid equivalence, one way -/
theorem braid_eq_of_gridl (h : gridl a b c d) :
    BraidMonoidInf.mk (to_fm (a ++ d)) = BraidMonoidInf.mk (to_fm (b ++ c)) := by
  induction h with
  | empty => rfl
  | top_bottom i => rfl
  | sides i => rfl
  | top_left i => rfl
  | adjacent i =>
      apply PresentedMonoid.sound
      simp [to_fm]
      rw [← mul_assoc, ← mul_assoc]
      rename_i k h_dist
      rcases Nat.dist_eq_one h_dist with ha | hb
      · rw [ha]
        apply ConGen.Rel.symm
        apply ConGen.Rel.of
        apply braid_rels_m_inf.adjacent
      apply ConGen.Rel.of
      rw [hb]
      apply braid_rels_m_inf.adjacent
  | separated i j h =>
      apply PresentedMonoid.sound
      rcases or_dist_iff.mp h
      · rename_i h1
        apply ConGen.Rel.of
        exact braid_rels_m_inf.separated _ _ h1
      rename_i h2
      apply ConGen.Rel.symm
      apply ConGen.Rel.of
      exact braid_rels_m_inf.separated _ _ h2
  | vertical _ _ h1_ih h2_ih =>
      apply PresentedMonoid.sound
      rename_i e f g i j k l m n
      rw [List.append_assoc]
      rw [to_fm_append]
      apply (ConGen.Rel.mul (ConGen.Rel.refl _) (Quotient.exact h2_ih)).trans
      --rw [← mul_assoc, ← mul_assoc]
      rw [← to_fm_append, ← List.append_assoc, ← List.append_assoc, to_fm_append, @to_fm_append _ k]
      exact ConGen.Rel.mul (Quotient.exact h1_ih) (ConGen.Rel.refl _)
  | horizontal _ _ h1_ih h2_ih =>
      apply PresentedMonoid.sound
      rename_i e f g i j k l m n
      rw [← List.append_assoc, to_fm_append, @to_fm_append _ k]
      apply (ConGen.Rel.mul (Quotient.exact h1_ih) (ConGen.Rel.refl _)).trans
      rw [← to_fm_append, ← to_fm_append, List.append_assoc, List.append_assoc, to_fm_append,
        @to_fm_append _ (j ++ k)]
      exact (ConGen.Rel.mul (ConGen.Rel.refl _) (Quotient.exact h2_ih))

-- theorem gridl_diag_length_eq (h : gridl a b c d) : a.length + d.length = b.length + c.length := by
--   have H := congr_arg BraidMonoidInf.length (braid_eq_of_gridl h)
--   simp only [BraidMonoidInf.length_mk, length_mul] at H
--   exact H

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

def split_vertically_t (a b c d : List (Option ℕ)) := ∀ b₁ b₂, b = b₁ ++ b₂ →
  b₁.length > 0 → b₂.length > 0 →
  Σ u d₁ d₂, (gridl a b₁ u d₁) × gridl u b₂ c d₂ × PLift (d = d₁ ++ d₂)

-- def split_vertically_t' (a b c d : FreeMonoid ℕ) (h0 : gridl a b c d) := ∀ b₁ b₂, b = b₁ * b₂ →
--   Σ u d₁ d₂, (h1 : (gridl a b₁ u d₁)) × (h2 : gridl u b₂ c d₂) × PLift (d = d₁ * d₂) ×
--     PLift (h0 = gridl.horizontal h1 h2)
/-- An induction principle for free monoids which mirrors induction on lists, with cases analogous
to the empty list and cons -/
@[to_additive (attr := elab_as_elim) "An induction principle for free monoids which mirrors
induction on lists, with cases analogous to the empty list and cons"]
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

  -- have H := List.append_eq_append_iff.mp h
  -- match H with
  -- | Sum.inl ⟨middle, hc, hb⟩ =>
  --     exact Sum.inl ⟨middle, ⟨⟨hc⟩, ⟨hb⟩⟩⟩
  -- | Sum.inr ⟨middle, ha, hd⟩ =>
  --     exact Sum.inr ⟨middle, ⟨⟨ha⟩, ⟨hd⟩⟩⟩

theorem gridl_bot_len_pos (h : gridl a b c d) : d.length > 0 := by
  induction h with
  | empty => simp
  | top_bottom i => simp
  | sides i => simp
  | top_left i => simp
  | adjacent i k h => simp
  | separated i j h => simp
  | vertical h1 h2 h1_ih h2_ih => exact h2_ih
  | horizontal h1 h2 h1_ih h2_ih => simp [h2_ih]

theorem gridl_left_len_pos (h : gridl a b c d) : a.length > 0 := by
  induction h with
  | empty => simp
  | top_bottom i => simp
  | sides i => simp
  | top_left i => simp
  | adjacent i k h => simp
  | separated i j h => simp
  | vertical h1 h2 h1_ih h2_ih => simp [h1_ih]
  | horizontal h1 h2 h1_ih h2_ih => simp [h1_ih]

theorem gridl_top_len_pos (h : gridl a b c d) : b.length > 0 := by
  induction h with
  | empty => simp
  | top_bottom i => simp
  | sides i => simp
  | top_left i => simp
  | adjacent i k h => simp
  | separated i j h => simp
  | vertical h1 h2 h1_ih h2_ih => exact h1_ih
  | horizontal h1 h2 h1_ih h2_ih => simp [h1_ih]

theorem gridl_right_len_pos (h : gridl a b c d) : c.length > 0 := by
  induction h with
  | empty => simp
  | top_bottom i => simp
  | sides i => simp
  | top_left i => simp
  | adjacent i k h => simp
  | separated i j h => simp
  | vertical h1 h2 h1_ih h2_ih => simp [h2_ih]
  | horizontal h1 h2 h1_ih h2_ih => simp [h2_ih]

noncomputable def splittable_vertically_of_gridl (h : gridl a b c d) :
    split_vertically_t a b c d := by
  induction h with
  | empty =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | top_bottom i =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | sides i =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | top_left i =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | adjacent i =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | separated i j h =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | vertical _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is f₁_len f₂_len
    rcases h1_ih f₁ f₂ f_is f₁_len f₂_len with ⟨l, m, n, hg1⟩
    have hm : m.length > 0 := gridl_bot_len_pos hg1.1
    have hn : n.length > 0 := gridl_bot_len_pos hg1.2.1
    rcases h2_ih m n hg1.2.2.1 hm hn with ⟨o, p, q, hg3⟩
    use l ++ o, p, q
    exact ⟨gridl.vertical hg1.1 hg3.1, ⟨gridl.vertical hg1.2.1 hg3.2.1, {down := hg3.2.2.1}⟩⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is f1_len f2_len
    rcases FreeMonoid.prod_eq_prod' fi_is with ha | hb
    · rcases ha with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
      rcases h2_ih m fi₂ hm2  (by sorry) f2_len with ⟨u, k₁, k₂, g1⟩
      use u, h ++ k₁, k₂
      rw [hm1]
      exact ⟨gridl.horizontal h1 g1.1, ⟨g1.2.1, {down := by rw [List.append_assoc, g1.2.2.1]}⟩⟩
    rcases hb with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
    rcases h1_ih fi₁ m hm1 f1_len (by sorry) with ⟨u, h₁, h₂, g1, g2, ⟨hh⟩⟩
    use u, h₁, (h₂ ++ k)
    rw [hm2]
    exact ⟨g1, ⟨gridl.horizontal g2 h2, {down := by rw [← List.append_assoc, hh]}⟩⟩

def split_horizontally_t (a b c d) := ∀ a₁ a₂, a = a₁ ++ a₂ →
  a₁.length > 0 → a₂.length > 0 →
  Σ u c₁ c₂, gridl a₁ b c₁ u × gridl a₂ u c₂ d × PLift (c = c₁ ++ c₂)

noncomputable def splittable_horizontally_of_gridl (h : gridl a b c d) :
    split_horizontally_t a b c d := by
  induction h with
  | empty =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | top_bottom i =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | sides i =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | top_left i =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | adjacent i =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | separated i j h =>
    intro _ _ b_is h1 h2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    sorry
    -- rcases FreeMonoid.prod_eq_prod' fi_is with ha | hb
    -- · rcases ha with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
    --   rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, ⟨hk⟩⟩
    --   use u, g * k₁, k₂
    --   rw [hm1]
    --   exact ⟨gridl.vertical h1 g1, ⟨g2, {down := by rw [mul_assoc, hk]}⟩⟩
    -- rcases hb with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
    -- rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, ⟨hh⟩⟩
    -- use u, h₁, (h₂ * j)
    -- rw [hm2]
    -- exact ⟨g1, ⟨gridl.vertical g2 h2, {down := by rw [← mul_assoc, hh]}⟩⟩
  | horizontal _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is f1_len f2_len
    rcases h1_ih f₁ f₂ f_is f1_len f2_len with ⟨l, m, n, hg1, hg2, ⟨heq⟩⟩
    rcases h2_ih m n heq (by sorry) (by sorry) with ⟨o, p, q, hg3, hg4, ⟨heq'⟩⟩
    use l ++ o, p, q
    exact ⟨gridl.horizontal hg1 hg3, ⟨gridl.horizontal hg2 hg4, {down := heq'}⟩⟩
