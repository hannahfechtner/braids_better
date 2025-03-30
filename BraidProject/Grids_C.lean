import BraidProject.BraidMonoid
import Mathlib.Data.Nat.Dist
open FreeMonoid

/-- a reversing grid, inductively defined as the set of basic cells, and a vertical and horizontal
closure under appending-/
inductive grid : FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → Type
  | empty : grid 1 1 1 1
  | top_bottom (i : ℕ) : grid 1 (of i) 1 (.of i)
  | sides (i : ℕ) : grid (of i) 1 (of i) 1
  | top_left (i : ℕ) : grid (of i) (of i) 1 1
  | adjacent (i k : ℕ) (h : i.dist k = 1) : grid (of i) (of k) (of i * of k) (of k * of i)
  | separated (i j : ℕ) (h : i.dist j > 1) : grid (of i) (of j) (of i) (of j)
  | vertical (h1: grid u v u' v') (h2 : grid a v' c d) : grid (u * a) v (u' * c) d
  | horizontal (h1: grid u v u' v') (h2 : grid u' b c d) : grid u (v * b) c (v' * d)

noncomputable def grid_swap : grid a b c d → grid b a d c := by
  intro h
  induction h with
  | empty => exact grid.empty
  | top_bottom i => exact grid.sides i
  | sides i => exact grid.top_bottom i
  | top_left i => exact grid.top_left i
  | adjacent i k h => exact grid.adjacent k i (by rw [Nat.dist_comm] at h; exact h)
  | separated i j h => exact grid.separated j i (by rw [Nat.dist_comm] at h; exact h)
  | vertical _ _ h1 h2 => exact grid.horizontal h1 h2
  | horizontal _ _ h1 h2 => exact grid.vertical h1 h2

/-- An induction principle on free monoids, with cases for `1`, `FreeMonoid.of` and `*`. -/
@[to_additive (attr := elab_as_elim, induction_eliminator)
"An induction principle on free monoids, with cases for `0`, `FreeAddMonoid.of` and `+`."]
def FreeMonoid.inductionOn'' {C : FreeMonoid α → Type} (z : FreeMonoid α) (one : C 1)
    (of : ∀ (x : α), C (FreeMonoid.of x)) (mul : ∀ (x y : FreeMonoid α), C x → C y → C (x * y)) :
  C z := List.rec one (fun _ _ ih => mul [_] _ (of _) ih) z

def grid_sides_word (u : FreeMonoid ℕ) : grid u 1 u 1 := by
  induction u using FreeMonoid.inductionOn'' with
  | one => exact grid.empty
  | of => exact grid.sides _
  | mul i u ih1 ih2 => exact grid.vertical ih1 ih2

def grid_top_bottom_word (u : FreeMonoid ℕ) : grid 1 u 1 u := by
  induction' u
  · exact grid.empty
  · exact grid.top_bottom _
  · rename_i one two
    exact grid.horizontal one two

def grid_top_left_word (u : FreeMonoid ℕ) : grid u u 1 1 := by
  induction' u
  · exact grid.empty
  · exact grid.top_left _
  · rename_i x y one two
    exact grid.vertical (grid.horizontal one (grid_top_bottom_word y))
      (grid.horizontal (grid_sides_word y) two)

/-- relating grid equivalence to braid equivalence, one way -/
theorem braid_eq_of_grid (h : grid a b c d) :
    BraidMonoidInf.mk (a * d) = BraidMonoidInf.mk (b * c) := by
  induction h with
  | empty => rfl
  | top_bottom i => rfl
  | sides i => rfl
  | top_left i => rfl
  | adjacent i =>
      apply PresentedMonoid.sound
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
      rw [mul_assoc]
      apply (ConGen.Rel.mul (ConGen.Rel.refl _) (Quotient.exact h2_ih)).trans
      rw [← mul_assoc, ← mul_assoc]
      exact ConGen.Rel.mul (Quotient.exact h1_ih) (ConGen.Rel.refl _)
  | horizontal _ _ h1_ih h2_ih =>
      apply PresentedMonoid.sound
      rw [← mul_assoc]
      apply (ConGen.Rel.mul (Quotient.exact h1_ih) (ConGen.Rel.refl _)).trans
      rw [mul_assoc, mul_assoc]
      exact (ConGen.Rel.mul (ConGen.Rel.refl _) (Quotient.exact h2_ih))

theorem grid_diag_length_eq (h : grid a b c d) : a.length + d.length = b.length + c.length := by
  have H := congr_arg BraidMonoidInf.length (braid_eq_of_grid h)
  simp only [BraidMonoidInf.length_mk, length_mul] at H
  exact H

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

def split_vertically (a b c d : FreeMonoid ℕ) := ∀ b₁ b₂, b = b₁ * b₂ →
  Σ u d₁ d₂, (grid a b₁ u d₁) × grid u b₂ c d₂ × PLift (d = d₁ * d₂)

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

noncomputable def splittable_vertically_of_grid {a b c d : FreeMonoid ℕ} (h : grid a b c d) :
    split_vertically a b c d := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1
    exact ⟨grid.empty, ⟨grid.empty, {down := rfl}⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · rw [ha1, ha2]
      use 1, 1, (of i)
      exact ⟨grid.empty, ⟨grid.top_bottom _, {down := rfl}⟩⟩
    rw [ha1, ha2]
    use 1, (of i), 1
    exact ⟨grid.top_bottom _, ⟨grid.empty, {down := rfl}⟩⟩
  | sides i =>
    intro _ _ b_is
    use (of i), 1, 1
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    exact ⟨grid.sides _, ⟨grid.sides _, {down := rfl}⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of' b_is.symm) with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · rw [ha1, ha2]
      use (of i), 1, 1
      exact ⟨grid.sides _, ⟨grid.top_left _, {down := rfl}⟩⟩
    · rw [ha1, ha2]
      use 1, 1, 1
      exact ⟨grid.top_left _, ⟨grid.empty, {down := rfl}⟩⟩
  | adjacent i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of' b_is.symm) with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · rw [ha1, ha2]
      rename_i k l m n
      use of i, 1, of (k) * of i
      exact ⟨grid.sides i, ⟨grid.adjacent i k l, {down := rfl}⟩⟩
    · rw [ha1, ha2]
      rename_i k l m n
      use of i * of k, of k * of i, 1
      exact ⟨grid.adjacent i k l, ⟨grid_sides_word _, {down := rfl}⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of' b_is.symm) with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · rw [ha1, ha2]
      use of i, 1, of j
      exact ⟨grid.sides _, ⟨grid.separated _ _ h, {down := rfl}⟩⟩
    rw [ha1, ha2]
    use of i, of j, 1
    exact ⟨grid.separated _ _ h, ⟨grid.sides _, {down := rfl}⟩⟩
  | vertical _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1⟩
    rcases h2_ih m n hg1.2.2.1 with ⟨o, p, q, hg3⟩
    use l * o, p, q
    exact ⟨grid.vertical hg1.1 hg3.1, ⟨grid.vertical hg1.2.1 hg3.2.1, {down := hg3.2.2.1}⟩⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    rcases FreeMonoid.prod_eq_prod' fi_is with ha | hb
    · rcases ha with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
      rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1⟩
      use u, h * k₁, k₂
      rw [hm1]
      exact ⟨grid.horizontal h1 g1.1, ⟨g1.2.1, {down := by rw [mul_assoc, g1.2.2.1]}⟩⟩
    rcases hb with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, ⟨hh⟩⟩
    use u, h₁, (h₂ * k)
    rw [hm2]
    exact ⟨g1, ⟨grid.horizontal g2 h2, {down := by rw [← mul_assoc, hh]}⟩⟩

def split_horizontally (a b c d : FreeMonoid ℕ) := ∀ a₁ a₂, a = a₁ * a₂ →
  Σ u c₁ c₂, grid a₁ b c₁ u × grid a₂ u c₂ d × PLift (c = c₁ * c₂)

noncomputable def splittable_horizontally_of_grid {a b c d : FreeMonoid ℕ} (h : grid a b c d) :
    split_horizontally a b c d := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1
    exact ⟨grid.empty, ⟨grid.empty, {down := rfl}⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use of i, 1, 1
    exact ⟨grid.top_bottom _, ⟨grid.top_bottom _, {down := rfl}⟩⟩
  | sides i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
    · rw [ha1, ha2]
      use 1, 1, of i
      exact ⟨grid.empty, ⟨grid.sides _, {down := rfl}⟩⟩
    rw [hb1, hb2]
    use 1, of i, 1
    exact ⟨grid.sides _, ⟨grid.empty, {down := rfl}⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
    · rw [ha1, ha2]
      use of i, 1, 1
      exact ⟨grid.top_bottom _, ⟨grid.top_left _, {down := rfl}⟩⟩
    rw [hb1, hb2]
    use 1, 1, 1
    exact ⟨grid.top_left _, ⟨grid.empty, {down := rfl}⟩⟩
  | adjacent i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
    · rw [ha1, ha2]
      rename_i k dist _ _
      use of k, 1, of i * (of k)
      exact ⟨grid.top_bottom _, ⟨grid.adjacent i k dist, {down := rfl}⟩⟩
    rw [hb1, hb2]
    rename_i k dist _ _
    use of k * of i, of i * of k, 1
    exact ⟨grid.adjacent i k dist, ⟨grid_top_bottom_word _, {down := rfl}⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
    · rw [ha1, ha2]
      use of j, 1, of i
      exact ⟨grid.top_bottom _, ⟨grid.separated _ _ h, {down := rfl}⟩⟩
    rw [hb1, hb2]
    use of j, of i, 1
    exact ⟨grid.separated _ _ h, ⟨grid.top_bottom _, {down := rfl}⟩⟩
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    rcases FreeMonoid.prod_eq_prod' fi_is with ha | hb
    · rcases ha with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
      rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, ⟨hk⟩⟩
      use u, g * k₁, k₂
      rw [hm1]
      exact ⟨grid.vertical h1 g1, ⟨g2, {down := by rw [mul_assoc, hk]}⟩⟩
    rcases hb with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, ⟨hh⟩⟩
    use u, h₁, (h₂ * j)
    rw [hm2]
    exact ⟨g1, ⟨grid.vertical g2 h2, {down := by rw [← mul_assoc, hh]}⟩⟩
  | horizontal _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, ⟨heq⟩⟩
    rcases h2_ih m n heq with ⟨o, p, q, hg3, hg4, ⟨heq'⟩⟩
    use l * o, p, q
    exact ⟨grid.horizontal hg1 hg3, ⟨grid.horizontal hg2 hg4, {down := heq'}⟩⟩
