import BraidProject.BraidMonoid
import Mathlib.Data.Nat.Dist
open FreeMonoid

--regular prop-valued gridrs with empty arrows marked as an option

/-- a reversing gridr, inductively defined as the set of basic cells, and a vertical and horizontal
closure under appending-/
inductive gridr : List (Option ℕ) → List (Option ℕ) → List (Option ℕ) → List (Option ℕ) → Prop
  | empty : gridr [none] [none] [none] [none]
  | top_bottom (i : ℕ) : gridr [none] [some i] [none] [some i]
  | sides (i : ℕ) : gridr [some i]  [none] [some i]  [none]
  | top_left (i : ℕ) : gridr [some i] [some i] [none] [none]
  | adjacent (i k : ℕ) (h : i.dist k = 1) : gridr [some i]  [some k] [some i, some k] [some k, some i]
  | separated (i j : ℕ) (h : i.dist j > 1) : gridr [some i]  [some j] [some i]  [some j]
  | vertical (h1: gridr u v u' v') (h2 : gridr a v' c d) : gridr (u ++ a) v (u' ++ c) d
  | horizontal (h1: gridr u v u' v') (h2 : gridr u' b c d) : gridr u (v ++ b) c (v' ++ d)

noncomputable def gridr_swap : gridr a b c d → gridr b a d c := by
  intro h
  induction h with
  | empty => exact gridr.empty
  | top_bottom i => exact gridr.sides i
  | sides i => exact gridr.top_bottom i
  | top_left i => exact gridr.top_left i
  | adjacent i k h => exact gridr.adjacent k i (by rw [Nat.dist_comm] at h; exact h)
  | separated i j h => exact gridr.separated j i (by rw [Nat.dist_comm] at h; exact h)
  | vertical _ _ h1 h2 => exact gridr.horizontal h1 h2
  | horizontal _ _ h1 h2 => exact gridr.vertical h1 h2

-- /-- An induction principle on free monoids, with cases for `1`, `FreeMonoid.of` and `*`. -/
-- @[to_additive (attr := elab_as_elim, induction_eliminator)
-- "An induction principle on free monoids, with cases for `0`, `FreeAddMonoid.of` and `+`."]
-- def FreeMonoid.inductionOn'' {C : FreeMonoid α → Type} (z : FreeMonoid α) (one : C 1)
--     (of : ∀ (x : α), C (FreeMonoid.of x)) (mul : ∀ (x y : FreeMonoid α), C x → C y → C (x * y)) :
--   C z := List.rec one (fun _ _ ih => mul [_] _ (of _) ih) z

theorem gridr_sides_word (u : List (Option ℕ)) : gridr u [none] u [none] := by sorry
  -- induction u with
  -- | one => exact gridr.empty
  -- | of => exact gridr.sides _
  -- | mul i u ih1 ih2 => exact gridr.vertical ih1 ih2
  -- · exact gridr.empty
  -- · exact gridr.sides _
  -- · rename_i one two
  --   exact gridr.vertical one two

theorem gridr_top_bottom_word (u : FreeMonoid ℕ) : gridr [none] u [none] u := by sorry
  -- induction' u
  -- · exact gridr.empty
  -- · exact gridr.top_bottom _
  -- · rename_i one two
  --   exact gridr.horizontal one two

theorem gridr_top_left_word (u : FreeMonoid ℕ) : gridr u u [none] [none] := by sorry
  -- induction' u
  -- · exact gridr.empty
  -- · exact gridr.top_left _
  -- · rename_i x y one two
  --   exact gridr.vertical (gridr.horizontal one (gridr_top_bottom_word y))
  --     (gridr.horizontal (gridr_sides_word y) two)
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
/-- relating gridr equivalence to braid equivalence, one way -/
theorem braid_eq_of_gridr (h : gridr a b c d) :
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
  | vertical _ _ h1_ih h2_ih => sorry
      -- apply PresentedMonoid.sound
      -- rw [mul_assoc]
      -- apply (ConGen.Rel.mul (ConGen.Rel.refl _) (Quotient.exact h2_ih)).trans
      -- rw [← mul_assoc, ← mul_assoc]
      -- exact ConGen.Rel.mul (Quotient.exact h1_ih) (ConGen.Rel.refl _)
  | horizontal _ _ h1_ih h2_ih =>
      apply PresentedMonoid.sound
      sorry
      -- rw [← mul_assoc]
      -- apply (ConGen.Rel.mul (Quotient.exact h1_ih) (ConGen.Rel.refl _)).trans
      -- rw [mul_assoc, mul_assoc]
      -- exact (ConGen.Rel.mul (ConGen.Rel.refl _) (Quotient.exact h2_ih))

-- theorem gridr_diag_length_eq (h : gridr a b c d) : a.length + d.length = b.length + c.length := by
--   have H := congr_arg BraidMonoidInf.length (braid_eq_of_gridr h)
--   simp only [BraidMonoidInf.length_mk, length_mul] at H
--   exact H

theorem FreeMonoid.prod_eq_one {a b : FreeMonoid α} (h : a * b = 1) : a = 1 ∧ b = 1 := by
  have H : FreeMonoid.length (a * b) = 0 := by
    rw [h, length_one]
  rw [FreeMonoid.length_mul] at H
  constructor
  · have H : length a = 0 := by linarith [h]
    exact length_eq_zero.mp H
  have H : length b = 0 := by linarith [h]
  exact length_eq_zero.mp H

theorem FreeMonoid.prod_eq_of {a b : FreeMonoid α} {i : α} (h : a * b = FreeMonoid.of i) :
    (a = 1 ∧ b = of i) ∨ (a = of i ∧ b = 1) := by
  have H : FreeMonoid.length (a * b) = 1 := by
    rw [h]
    exact FreeMonoid.length_of _
  rw [FreeMonoid.length_mul] at H
  have H2 : length a = 0 ∨ length b = 0 := by
    revert H
    rcases (length a)
    · exact fun _ => Or.inl rfl
    intro H
    right
    linarith [H]
  rcases H2 with a_one | b_one
  · left
    constructor
    · exact length_eq_zero.mp a_one
    rw [length_eq_zero.mp a_one] at h
    exact h
  right
  constructor
  · rw [length_eq_zero.mp b_one, mul_one] at h
    exact h
  exact length_eq_zero.mp b_one

def split_vertically (a b c d : List (Option ℕ)) := ∀ b₁ b₂, b = b₁ ++ b₂ →
  b₁.length > 0 → b₂.length > 0 →
  ∃ u d₁ d₂, gridr a b₁ u d₁ ∧ gridr u b₂ c d₂ ∧ d = d₁ ++ d₂

-- theorem eq_of_length_eq {a b c d : FreeMonoid α} (h : a * b = c * d) (hl : a.length = c.length) :
--     a = c := by
--   have h1 : ((FreeMonoid.toList a) ++ (FreeMonoid.toList b)).take a.length = (List.append c d).take a.length := by
--     exact congrArg (List.take a.length) h
--   have h2 := List.take_left (FreeMonoid.toList a) (FreeMonoid.toList b)
--   have h3 := List.take_left (FreeMonoid.toList c) (FreeMonoid.toList d)
--   have hf : List.take (List.length (FreeMonoid.toList a)) ((FreeMonoid.toList a) ++ (FreeMonoid.toList b)) =
--       List.take (List.length (FreeMonoid.toList c)) ((FreeMonoid.toList c) ++ (FreeMonoid.toList d)) := by
--     have H_len : List.length (FreeMonoid.toList a) = List.length (FreeMonoid.toList c) := hl
--     rw [← H_len]
--     exact h1
--   rw [h2, h3] at hf
--   exact hf

theorem FreeMonoid.prod_eq_prod {a b c d : FreeMonoid α} (h : a * b = c * d) :
    (∃ from_middle, c = a * from_middle ∧ b = from_middle * d) ∨
    (∃ to_middle, a = c * to_middle ∧ d = to_middle * b) := List.append_eq_append_iff.mp h

theorem splittable_vertically_of_gridr {a b c d : List (Option ℕ)} (h : gridr a b c d) :
    split_vertically a b c d := by
  induction h with
  | empty =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | top_bottom i =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | sides i =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | top_left i =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | adjacent i =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | separated i j h =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | vertical _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    sorry
    -- rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, heq⟩
    -- rcases h2_ih m n heq with ⟨o, p, q, hg3, hg4, heq'⟩
    -- use l * o, p, q
    -- exact ⟨gridr.vertical hg1 hg3, ⟨gridr.vertical hg2 hg4, heq'⟩⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    sorry

    -- rcases FreeMonoid.prod_eq_prod fi_is with ha | hb
    -- · rcases ha with ⟨m, hm1, hm2⟩
    --   rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, hk⟩
    --   use u, h * k₁, k₂
    --   rw [hm1]
    --   exact ⟨gridr.horizontal h1 g1, ⟨g2, by rw [mul_assoc, hk]⟩⟩
    -- rcases hb with ⟨m, hm1, hm2⟩
    -- rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, hh⟩
    -- use u, h₁, (h₂ * k)
    -- rw [hm2]
    -- exact ⟨g1, ⟨gridr.horizontal g2 h2, by rw [← mul_assoc, hh]⟩⟩

def split_horizontally (a b c d : List (Option ℕ)) := ∀ a₁ a₂, a = a₁ ++ a₂ →
  a₁.length > 0 → a₂.length > 0 →
  ∃ u c₁ c₂, gridr a₁ b c₁ u ∧ gridr a₂ u c₂ d ∧ c = c₁ ++ c₂

theorem splittable_horizontally_of_gridr {a b c d : List (Option ℕ)} (h : gridr a b c d) :
    split_horizontally a b c d := by
  induction h with
  | empty =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | top_bottom i =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | sides i =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | top_left i =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | adjacent i =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | separated i j h =>
    intro _ _ b_is b1 b2
    apply congr_arg List.length at b_is
    simp at b_is
    omega
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    sorry
    -- rcases FreeMonoid.prod_eq_prod fi_is with ha | hb
    -- · rcases ha with ⟨m, hm1, hm2⟩
    --   rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, hk⟩
    --   use u, g * k₁, k₂
    --   rw [hm1]
    --   exact ⟨gridr.vertical h1 g1, ⟨g2, by rw [mul_assoc, hk]⟩⟩
    -- rcases hb with ⟨m, hm1, hm2⟩
    -- rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, hh⟩
    -- use u, h₁, (h₂ * j)
    -- rw [hm2]
    -- exact ⟨g1, ⟨gridr.vertical g2 h2, by rw [← mul_assoc, hh]⟩⟩
  | horizontal _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    sorry
    -- rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, heq⟩
    -- rcases h2_ih m n heq with ⟨o, p, q, hg3, hg4, heq'⟩
    -- use l * o, p, q
    -- exact ⟨gridr.horizontal hg1 hg3, ⟨gridr.horizontal hg2 hg4, heq'⟩⟩
