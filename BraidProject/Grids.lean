import BraidProject.BraidMonoid
import Mathlib.Data.Nat.Dist
open FreeMonoid

noncomputable section

/-- a reversing grid, inductively defined as the set of basic cells, and a vertical and horizontal
closure under appending-/
inductive gridt : FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → Type
  | empty : gridt 1 1 1 1
  | top_bottom (i : ℕ) : gridt 1 (of i) 1 (.of i)
  | sides (i : ℕ) : gridt (of i) 1 (of i) 1
  | top_left (i : ℕ) : gridt (of i) (of i) 1 1
  | adjacent (i k : ℕ) (h : i.dist k = 1) : gridt (of i) (of k) (of i * of k) (of k * of i)
  | separated (i j : ℕ) (h : i.dist j > 1) : gridt (of i) (of j) (of i) (of j)
  | vertical (h1: gridt u v u' v') (h2 : gridt a v' c d) : gridt (u * a) v (u' * c) d
  | horizontal (h1: gridt u v u' v') (h2 : gridt u' b c d) : gridt u (v * b) c (v' * d)

def hasSize : gridt a b c d → ℕ → Prop
  | gridt.empty, n => n = 0
  | gridt.top_bottom _, n => n = 0
  | gridt.sides _, n => n = 0
  | gridt.top_left _, n => n = 1
  | gridt.adjacent _ _ _, n => n = 1
  | gridt.separated _ _ _, n => n = 1
  | gridt.vertical h1 h2, n => ∃ n1 n2, hasSize h1 n1 ∧ hasSize h2 n2 ∧ n = n1 + n2
  | gridt.horizontal h1 h2, n => ∃ n1 n2, hasSize h1 n1 ∧ hasSize h2 n2 ∧ n = n1 + n2

theorem all_gridts_have_size (h : gridt a b c d) : ∃ n, hasSize h n := by
  induction h with
  | empty => exact ⟨0, rfl⟩
  | top_bottom i => exact ⟨0, rfl⟩
  | sides i => exact ⟨0, rfl⟩
  | top_left i => exact ⟨1, rfl⟩
  | adjacent i k h => exact ⟨1, rfl⟩
  | separated i j h => exact ⟨1, rfl⟩
  | vertical h1 h2 h1_ih h2_ih =>
    rcases h1_ih with ⟨n1, h1_ih⟩
    rcases h2_ih with ⟨n2, h2_ih⟩
    exact ⟨n1 + n2, ⟨n1, n2, h1_ih, h2_ih, rfl⟩⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rcases h1_ih with ⟨n1, h1_ih⟩
    rcases h2_ih with ⟨n2, h2_ih⟩
    exact ⟨n1 + n2, ⟨n1, n2, h1_ih, h2_ih, rfl⟩⟩

def gridt.sizeOf (h : gridt a b c d) : Nat := (all_gridts_have_size h).choose

theorem gridt_uniqueness (h1 : hasSize h n1) (h2 : hasSize h n2) : n1 = n2 := by
  induction h generalizing n1 n2
   <;> simp_all [hasSize]
  · rcases h1 with ⟨u2, hu2, v2, hv2, rfl⟩
    rcases h2 with ⟨u1, hu1, v1, hv1, rfl⟩
    rename_i ih1 ih2
    have H := ih1 hu2 hu1
    have H2 := ih2 hv2 hv1
    omega
  rcases h1 with ⟨u2, hu2, v2, hv2, rfl⟩
  rcases h2 with ⟨u1, hu1, v1, hv1, rfl⟩
  rename_i ih1 ih2
  have H := ih1 hu2 hu1
  have H2 := ih2 hv2 hv1
  omega

@[simp]
lemma sizeOf_empty : gridt.sizeOf gridt.empty = 0 := by
  have H := all_gridts_have_size gridt.empty
  exact H.choose_spec

@[simp]
lemma sizeOf_top_bottom (i : ℕ) : gridt.sizeOf (gridt.top_bottom i) = 0 := by
  have H := all_gridts_have_size (gridt.top_bottom i)
  exact H.choose_spec

@[simp]
lemma sizeOf_sides (i : ℕ) : gridt.sizeOf (gridt.sides i) = 0 := by
  have H := all_gridts_have_size (gridt.sides i)
  exact H.choose_spec

@[simp]
lemma sizeOf_top_left (i : ℕ) : gridt.sizeOf (gridt.top_left i) = 1 := by
  have H := all_gridts_have_size (gridt.top_left i)
  exact H.choose_spec

@[simp]
lemma sizeOf_adjacent (i k : ℕ) (h : i.dist k = 1) : gridt.sizeOf (gridt.adjacent i k h) = 1 := by
  have H := all_gridts_have_size (gridt.adjacent i k h)
  exact H.choose_spec

@[simp]
lemma sizeOf_separated (i j : ℕ) (h : i.dist j > 1) : gridt.sizeOf (gridt.separated i j h) = 1 := by
  have H := all_gridts_have_size (gridt.separated i j h)
  exact H.choose_spec

-- theorem size_of_unique (h : gridt.sizeOf g = n) (h2 : gridt.sizeOf g = n2) : n = n2 := by sorry
-- theorem hasSize_of_sizeOf (h1 : gridt.sizeOf h = n) : hasSize h n := by
--   induction h generalizing n
--    <;> simp_all [hasSize]
--   · rename_i a b c d e f g i j k l h3 h4 h5 h6
--     use h3.sizeOf
--     constructor
--     · exact h5
--     use h4.sizeOf
--     constructor
--     · exact h6
--     sorry --omega
--   sorry

theorem hasSize_vert (h1 : hasSize g1 n1) (h2 : hasSize g2 n2) : hasSize (g1.vertical g2) (n1 + n2) := by
  simp [hasSize]
  use n1
  constructor
  · exact h1
  use n2

theorem hasSize_horiz (h1 : hasSize g1 n1) (h2 : hasSize g2 n2) : hasSize (g1.horizontal g2) (n1 + n2) := by
  simp [hasSize]
  use n1
  constructor
  · exact h1
  use n2

theorem hasSize_add (h1 : hasSize g1 n1) (h2 : hasSize g2 n2) (h3 : hasSize (g1.vertical g2) c) : n1 + n2 = c := by
  have H0 := hasSize_vert h1 h2
  exact gridt_uniqueness H0 h3

theorem hasSize_add_horiz (h1 : hasSize g1 n1) (h2 : hasSize g2 n2) (h3 : hasSize (g1.horizontal g2) c) : n1 + n2 = c := by
  have H0 := hasSize_horiz h1 h2
  exact gridt_uniqueness H0 h3

theorem sizeOf_eq_hasSize (h1 : hasSize g n1) (h2 : gridt.sizeOf g = n2) : n1 = n2 := by
  induction g generalizing n1 n2 <;> simp_all [hasSize]
  · rename_i ih1 ih2
    rcases h1 with ⟨u, hu, v, hv, rfl⟩
    specialize ih1 hu
    specialize ih2 hv
    rw [← h2, ih1, ih2]
    simp [gridt.sizeOf]
    rename_i g1 g2
    have H0 := (all_gridts_have_size g1).choose_spec
    have H1 := (all_gridts_have_size g2).choose_spec
    have H2 := (all_gridts_have_size (g1.vertical g2)).choose_spec
    have H4 := hasSize_add H0 H1 H2
    exact H4
  rename_i ih1 ih2
  rcases h1 with ⟨u, hu, v, hv, rfl⟩
  specialize ih1 hu
  specialize ih2 hv
  rw [← h2, ih1, ih2]
  simp [gridt.sizeOf]
  rename_i g1 g2
  have H0 := (all_gridts_have_size g1).choose_spec
  have H1 := (all_gridts_have_size g2).choose_spec
  have H2 := (all_gridts_have_size (g1.horizontal g2)).choose_spec
  have H4 := hasSize_add_horiz H0 H1 H2
  exact H4


  -- have H0 := (all_gridts_have_size h).choose_spec
  -- have H5 := gridt_uniqueness H0 h1
  -- rw [← H5]
  -- have H7 : sizeOf h = (all_gridts_have_size h).choose := by sorry
  -- rw [← H7, h2]
  --rw [← h2]


  -- with
  -- | empty => simp_all [hasSize]
  -- | top_bottom i => sorry
  -- | sides i => sorry
  -- | top_left i => sorry
  -- | adjacent i k h => sorry
  -- | separated i j h => sorry
  -- | vertical h1 h2 h1_ih h2_ih => sorry
  -- | horizontal h1 h2 h1_ih h2_ih => sorry

lemma sizeOf_vertical (h1 : gridt u v u' v') (h2 : gridt a v' c d) :
    gridt.sizeOf (gridt.vertical h1 h2) = gridt.sizeOf h1 + gridt.sizeOf h2 := by
  have H1 := all_gridts_have_size (gridt.vertical h1 h2)
  have H2 := H1.choose_spec
  simp [hasSize] at H1
  simp only [hasSize] at H2
  rcases H2 with ⟨n3, n4, spec⟩
  rcases H1 with ⟨n5, n6, spec2⟩
  rcases H1 with ⟨n7, n8, n9, spec3⟩
  conv => lhs; simp [gridt.sizeOf, spec.2.2]
  have H : h1.sizeOf = n3 := (sizeOf_eq_hasSize spec.1 rfl).symm
  have H2 : h2.sizeOf = n4 := (sizeOf_eq_hasSize spec.2.1 rfl).symm
  omega




end


/-- a reversing grid, inductively defined as the set of basic cells, and a vertical and horizontal
closure under appending-/
inductive grid : FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → Prop
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

-- /-- An induction principle on free monoids, with cases for `1`, `FreeMonoid.of` and `*`. -/
-- @[to_additive (attr := elab_as_elim, induction_eliminator)
-- "An induction principle on free monoids, with cases for `0`, `FreeAddMonoid.of` and `+`."]
-- def FreeMonoid.inductionOn'' {C : FreeMonoid α → Type} (z : FreeMonoid α) (one : C 1)
--     (of : ∀ (x : α), C (FreeMonoid.of x)) (mul : ∀ (x y : FreeMonoid α), C x → C y → C (x * y)) :
--   C z := List.rec one (fun _ _ ih => mul [_] _ (of _) ih) z

theorem grid_sides_word (u : FreeMonoid ℕ) : grid u 1 u 1 := by
  induction u with
  | one => exact grid.empty
  | of => exact grid.sides _
  | mul i u ih1 ih2 => exact grid.vertical ih1 ih2
  -- · exact grid.empty
  -- · exact grid.sides _
  -- · rename_i one two
  --   exact grid.vertical one two

theorem grid_top_bottom_word (u : FreeMonoid ℕ) : grid 1 u 1 u := by
  induction' u
  · exact grid.empty
  · exact grid.top_bottom _
  · rename_i one two
    exact grid.horizontal one two

theorem grid_top_left_word (u : FreeMonoid ℕ) : grid u u 1 1 := by
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

def split_vertically (a b c d : FreeMonoid ℕ) := ∀ b₁ b₂, b = b₁ * b₂ →
  ∃ u d₁ d₂, grid a b₁ u d₁ ∧ grid u b₂ c d₂ ∧ d = d₁ * d₂

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

theorem splittable_vertically_of_grid {a b c d : FreeMonoid ℕ} (h : grid a b c d) :
    split_vertically a b c d := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1
    exact ⟨grid.empty, ⟨grid.empty, rfl⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ha | hb
    · rw [ha.1, ha.2]
      use 1, 1, (of i)
      exact ⟨grid.empty, ⟨grid.top_bottom _, rfl⟩⟩
    · rw [hb.1, hb.2]
      use 1, (of i), 1
      exact ⟨grid.top_bottom _, ⟨grid.empty, rfl⟩⟩
  | sides i =>
    intro _ _ b_is
    use (of i), 1, 1
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    exact ⟨grid.sides _, ⟨grid.sides _, rfl⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ha | hb
    · rw [ha.1, ha.2]
      use (of i), 1, 1
      exact ⟨grid.sides _, ⟨grid.top_left _, rfl⟩⟩
    · rw [hb.1, hb.2]
      use 1, 1, 1
      exact ⟨grid.top_left _, ⟨grid.empty, rfl⟩⟩
  | adjacent i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ha | hb
    · rw [ha.1, ha.2]
      rename_i k l m n
      rcases or_dist_iff_eq.mp l with k_is | i_is
      · use of i, 1, of (i+1) * of i
        rw [← k_is]
        constructor
        · exact grid.sides i
        constructor
        · apply grid.adjacent i (i + 1)
          unfold Nat.dist
          simp
        rfl
      rw [← i_is]
      use of (k + 1), 1, of k * of (k + 1)
      constructor
      · exact grid.sides _
      constructor
      · apply grid.adjacent
        unfold Nat.dist
        simp
      rfl
    · rw [hb.1, hb.2]
      rename_i k l m n
      rcases or_dist_iff_eq.mp l with k_is | i_is
      · rw [← k_is]
        use of i * of (i+1), of (i+1) * of i, 1
        exact ⟨grid.adjacent i (i + 1) dist_succ, ⟨grid_sides_word _, rfl⟩⟩
      rw [← i_is]
      use of (k + 1) * of k, of k * of (k + 1), 1
      constructor
      · exact grid.adjacent _ _ (by unfold Nat.dist; simp)
      exact ⟨grid_sides_word _, rfl⟩
  | separated i j h =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ha | hb
    · rw [ha.1, ha.2]
      use of i, 1, of j
      exact ⟨grid.sides _, ⟨grid.separated _ _ h, rfl⟩⟩
    rw [hb.1, hb.2]
    use of i, of j, 1
    exact ⟨grid.separated _ _ h, ⟨grid.sides _, rfl⟩⟩
  | vertical _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, heq⟩
    rcases h2_ih m n heq with ⟨o, p, q, hg3, hg4, heq'⟩
    use l * o, p, q
    exact ⟨grid.vertical hg1 hg3, ⟨grid.vertical hg2 hg4, heq'⟩⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    rcases FreeMonoid.prod_eq_prod fi_is with ha | hb
    · rcases ha with ⟨m, hm1, hm2⟩
      rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, hk⟩
      use u, h * k₁, k₂
      rw [hm1]
      exact ⟨grid.horizontal h1 g1, ⟨g2, by rw [mul_assoc, hk]⟩⟩
    rcases hb with ⟨m, hm1, hm2⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, hh⟩
    use u, h₁, (h₂ * k)
    rw [hm2]
    exact ⟨g1, ⟨grid.horizontal g2 h2, by rw [← mul_assoc, hh]⟩⟩

def split_horizontally (a b c d : FreeMonoid ℕ) := ∀ a₁ a₂, a = a₁ * a₂ →
  ∃ u c₁ c₂, grid a₁ b c₁ u ∧ grid a₂ u c₂ d ∧ c = c₁ * c₂

theorem splittable_horizontally_of_grid {a b c d : FreeMonoid ℕ} (h : grid a b c d) :
    split_horizontally a b c d := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1
    exact ⟨grid.empty, ⟨grid.empty, rfl⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use of i, 1, 1
    exact ⟨grid.top_bottom _, ⟨grid.top_bottom _, rfl⟩⟩
  | sides i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ha | hb
    · rw [ha.1, ha.2]
      use 1, 1, of i
      exact ⟨grid.empty, ⟨grid.sides _, rfl⟩⟩
    rw [hb.1, hb.2]
    use 1, of i, 1
    exact ⟨grid.sides _, ⟨grid.empty, rfl⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ha | hb
    · rw [ha.1, ha.2]
      use of i, 1, 1
      exact ⟨grid.top_bottom _, ⟨grid.top_left _, rfl⟩⟩
    rw [hb.1, hb.2]
    use 1, 1, 1
    exact ⟨grid.top_left _, ⟨grid.empty, rfl⟩⟩
  | adjacent i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ha | hb
    · rw [ha.1, ha.2]
      rename_i dist _ _
      rcases or_dist_iff_eq.mp dist with k_is | i_is
      · use of (i+1), 1, of i * of (i + 1)
        rw [← k_is]
        exact ⟨grid.top_bottom _, ⟨grid.adjacent i (i + 1) dist_succ, rfl⟩⟩
      rename_i k _ _
      rw [← i_is]
      use of k, 1, of (k + 1) * of k
      exact ⟨grid.top_bottom _, ⟨grid.adjacent _ _ (by unfold Nat.dist; simp), rfl⟩⟩
    rw [hb.1, hb.2]
    rename_i k dist _ _
    rcases or_dist_iff_eq.mp dist with k_is | i_is
    · rw [← k_is]
      use of (i + 1) * of i, of i * of (i + 1), 1
      exact ⟨grid.adjacent i (i + 1) dist_succ, ⟨grid_top_bottom_word _, rfl⟩⟩
    rw [← i_is]
    use of k * of (k + 1), of (k + 1) * of k, 1
    exact ⟨grid.adjacent _ _ (by unfold Nat.dist; simp), ⟨grid_top_bottom_word _, rfl⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ha | hb
    · rw [ha.1, ha.2]
      use of j, 1, of i
      exact ⟨grid.top_bottom _, ⟨grid.separated _ _ h, rfl⟩⟩
    rw [hb.1, hb.2]
    use of j, of i, 1
    exact ⟨grid.separated _ _ h, ⟨grid.top_bottom _, rfl⟩⟩
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    rcases FreeMonoid.prod_eq_prod fi_is with ha | hb
    · rcases ha with ⟨m, hm1, hm2⟩
      rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, hk⟩
      use u, g * k₁, k₂
      rw [hm1]
      exact ⟨grid.vertical h1 g1, ⟨g2, by rw [mul_assoc, hk]⟩⟩
    rcases hb with ⟨m, hm1, hm2⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, hh⟩
    use u, h₁, (h₂ * j)
    rw [hm2]
    exact ⟨g1, ⟨grid.vertical g2 h2, by rw [← mul_assoc, hh]⟩⟩
  | horizontal _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, heq⟩
    rcases h2_ih m n heq with ⟨o, p, q, hg3, hg4, heq'⟩
    use l * o, p, q
    exact ⟨grid.horizontal hg1 hg3, ⟨grid.horizontal hg2 hg4, heq'⟩⟩
