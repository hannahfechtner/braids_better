import BraidProject.BraidMonoid
import Mathlib.Data.Nat.Dist
open FreeMonoid
/-- a reversing grid, inductively defined as the set of basic cells, and a vertical and horizontal
closure under appending-/



inductive grid_sz : FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → ℕ → Prop
  | empty : grid_sz 1 1 1 1 0
  | top_bottom (i : ℕ) : grid_sz 1 (of i) 1 (.of i) 0
  | sides (i : ℕ) : grid_sz (of i) 1 (of i) 1 0
  | top_left (i : ℕ) : grid_sz (of i) (of i) 1 1 1
  | adjacent (i k : ℕ) (h : i.dist k = 1) : grid_sz (of i) (of k) (of i * of k) (of k * of i) 1
  | separated (i j : ℕ) (h : i.dist j > 1) : grid_sz (of i) (of j) (of i) (of j) 1
  | vertical (h1: grid_sz u v u' v' n1) (h2 : grid_sz a v' c d n2) : grid_sz (u * a) v (u' * c) d (n1 + n2)
  | horizontal (h1: grid_sz u v u' v' n1) (h2 : grid_sz u' b c d n2) : grid_sz u (v * b) c (v' * d) (n1 + n2)


theorem grid_swap : grid_sz a b c d n → grid_sz b a d c n := by
  intro h
  induction h with
  | empty => exact grid_sz.empty
  | top_bottom i => exact grid_sz.sides i
  | sides i => exact grid_sz.top_bottom i
  | top_left i => exact grid_sz.top_left i
  | adjacent i k h => exact grid_sz.adjacent k i (by rw [Nat.dist_comm] at h; exact h)
  | separated i j h => exact grid_sz.separated j i (by rw [Nat.dist_comm] at h; exact h)
  | vertical _ _ h1 h2 => exact grid_sz.horizontal h1 h2
  | horizontal _ _ h1 h2 => exact grid_sz.vertical h1 h2

theorem grid_sides_word (u : FreeMonoid ℕ) : grid_sz u 1 u 1 0 := by
  induction' u
  · exact grid_sz.empty
  · exact grid_sz.sides _
  · rename_i one two
    exact grid_sz.vertical one two

theorem grid_top_bottom_word (u : FreeMonoid ℕ) : grid_sz 1 u 1 u 0 := by
  induction' u
  · exact grid_sz.empty
  · exact grid_sz.top_bottom _
  · rename_i one two
    exact grid_sz.horizontal one two

theorem grid_top_left_word (u : FreeMonoid ℕ) : grid_sz u u 1 1 (u.length) := by
  induction' u
  · exact grid_sz.empty
  · exact grid_sz.top_left _
  · rename_i x y one two
    simp only [length_mul]
    have H := (grid_sz.horizontal (grid_sides_word y) two)
    simp at H
    exact grid_sz.vertical (grid_sz.horizontal one (grid_top_bottom_word y)) H

/-- relating grid_sz equivalence to braid equivalence, one way -/
theorem braid_eq_of_grid_sz (h : grid_sz a b c d n) :
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

theorem grid_diag_length_eq (h : grid_sz a b c d n) : a.length + d.length = b.length + c.length := by
  have H := congr_arg BraidMonoidInf.length (braid_eq_of_grid_sz h)
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

def split_vertically (a b c d : FreeMonoid ℕ) (n) := ∀ b₁ b₂, b = b₁ * b₂ →
  ∃ u d₁ d₂ n₁ n₂, grid_sz a b₁ u d₁ n₁ ∧ grid_sz u b₂ c d₂ n₂ ∧ d = d₁ * d₂ ∧ n₁ + n₂ = n

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

theorem splittable_vertically_of_grid_sz {a b c d : FreeMonoid ℕ} (h : grid_sz a b c d n) :
    split_vertically a b c d n := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1, 0, 0
    exact ⟨grid_sz.empty, ⟨grid_sz.empty, ⟨rfl, rfl⟩⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ha | hb
    · rw [ha.1, ha.2]
      use 1, 1, (of i), 0, 0
      exact ⟨grid_sz.empty, ⟨grid_sz.top_bottom _, ⟨rfl, rfl⟩⟩⟩
    · rw [hb.1, hb.2]
      use 1, (of i), 1, 0, 0
      exact ⟨grid_sz.top_bottom _, ⟨grid_sz.empty, ⟨rfl, rfl⟩⟩⟩
  | sides i =>
    intro _ _ b_is
    use (of i), 1, 1, 0, 0
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    exact ⟨grid_sz.sides _, ⟨grid_sz.sides _, ⟨rfl, rfl⟩⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ha | hb
    · rw [ha.1, ha.2]
      use (of i), 1, 1, 0, 1
      exact ⟨grid_sz.sides _, ⟨grid_sz.top_left _, ⟨rfl, rfl⟩⟩⟩
    · rw [hb.1, hb.2]
      use 1, 1, 1, 1, 0
      exact ⟨grid_sz.top_left _, ⟨grid_sz.empty, ⟨rfl, rfl⟩⟩⟩
  | adjacent i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ha | hb
    · rw [ha.1, ha.2]
      rename_i k l m n
      rcases or_dist_iff_eq.mp l with k_is | i_is
      · use of i, 1, of (i+1) * of i, 0, 1
        rw [← k_is]
        constructor
        · exact grid_sz.sides i
        constructor
        · apply grid_sz.adjacent i (i + 1)
          unfold Nat.dist
          simp
        exact ⟨rfl, rfl⟩
      rw [← i_is]
      use of (k + 1), 1, of k * of (k + 1), 0, 1
      constructor
      · exact grid_sz.sides _
      constructor
      · apply grid_sz.adjacent
        unfold Nat.dist
        simp
      exact ⟨rfl, rfl⟩
    · rw [hb.1, hb.2]
      rename_i k l m n
      rcases or_dist_iff_eq.mp l with k_is | i_is
      · rw [← k_is]
        use of i * of (i+1), of (i+1) * of i, 1, 1, 0
        exact ⟨grid_sz.adjacent i (i + 1) dist_succ, ⟨grid_sides_word _, ⟨rfl, rfl⟩⟩⟩
      rw [← i_is]
      use of (k + 1) * of k, of k * of (k + 1), 1, 1, 0
      constructor
      · exact grid_sz.adjacent _ _ (by unfold Nat.dist; simp)
      exact ⟨grid_sides_word _, ⟨rfl, rfl⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ha | hb
    · rw [ha.1, ha.2]
      use of i, 1, of j, 0, 1
      exact ⟨grid_sz.sides _, ⟨grid_sz.separated _ _ h, ⟨rfl, rfl⟩⟩⟩
    rw [hb.1, hb.2]
    use of i, of j, 1, 1, 0
    exact ⟨grid_sz.separated _ _ h, ⟨grid_sz.sides _, ⟨rfl, rfl⟩⟩⟩
  | vertical _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n,  n1, n2, hg1, hg2, heq, n_is⟩
    rcases h2_ih m n heq with ⟨o, p, q, n3, n4, hg3, hg4, heq'⟩
    use l * o, p, q, n1 + n3, n2 + n4
    exact ⟨grid_sz.vertical hg1 hg3, ⟨grid_sz.vertical hg2 hg4, ⟨heq'.1, by omega⟩ ⟩⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h n3 i j k n4
    intro fi₁ fi₂ fi_is
    rcases FreeMonoid.prod_eq_prod fi_is with ha | hb
    · rcases ha with ⟨m, hm1, hm2⟩
      rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, n1, n2, g1, g2, hk, n_is⟩
      use u, h * k₁, k₂, n3 + n1, n2
      rw [hm1]
      exact ⟨grid_sz.horizontal h1 g1, ⟨g2, ⟨by rw [mul_assoc, hk], by omega⟩⟩⟩
    rcases hb with ⟨m, hm1, hm2⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, n1, n2, g1, g2, hh, n_is⟩
    use u, h₁, (h₂ * k), n1, n2 + n4
    rw [hm2]
    exact ⟨g1, ⟨grid_sz.horizontal g2 h2, ⟨by rw [← mul_assoc, hh], by omega⟩ ⟩⟩

def split_horizontally (a b c d : FreeMonoid ℕ) (n : ℕ) := ∀ a₁ a₂, a = a₁ * a₂ →
  ∃ u c₁ c₂ n1 n2, grid_sz a₁ b c₁ u n1 ∧ grid_sz a₂ u c₂ d n2 ∧ c = c₁ * c₂ ∧ n1 + n2 = n

theorem splittable_horizontally_of_grid_sz {a b c d : FreeMonoid ℕ} (h : grid_sz a b c d n) :
    split_horizontally a b c d n := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1, 0, 0
    exact ⟨grid_sz.empty, ⟨grid_sz.empty, ⟨rfl, rfl⟩⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use of i, 1, 1, 0, 0
    exact ⟨grid_sz.top_bottom _, ⟨grid_sz.top_bottom _, ⟨rfl, rfl⟩⟩⟩
  | sides i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ha | hb
    · rw [ha.1, ha.2]
      use 1, 1, of i, 0, 0
      exact ⟨grid_sz.empty, ⟨grid_sz.sides _, ⟨rfl, rfl⟩⟩⟩
    rw [hb.1, hb.2]
    use 1, of i, 1, 0, 0
    exact ⟨grid_sz.sides _, ⟨grid_sz.empty, ⟨rfl, rfl⟩⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ha | hb
    · rw [ha.1, ha.2]
      use of i, 1, 1, 0, 1
      exact ⟨grid_sz.top_bottom _, ⟨grid_sz.top_left _, ⟨rfl, rfl⟩⟩⟩
    rw [hb.1, hb.2]
    use 1, 1, 1, 1, 0
    exact ⟨grid_sz.top_left _, ⟨grid_sz.empty, ⟨rfl, rfl⟩⟩⟩
  | adjacent i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ha | hb
    · rw [ha.1, ha.2]
      rename_i dist _ _
      rcases or_dist_iff_eq.mp dist with k_is | i_is
      · use of (i+1), 1, of i * of (i + 1), 0, 1
        rw [← k_is]
        exact ⟨grid_sz.top_bottom _, ⟨grid_sz.adjacent i (i + 1) dist_succ, ⟨rfl, rfl⟩⟩⟩
      rename_i k _ _
      rw [← i_is]
      use of k, 1, of (k + 1) * of k, 0, 1
      exact ⟨grid_sz.top_bottom _, ⟨grid_sz.adjacent (k+1) k (by rw [Nat.dist_comm, dist_succ]), ⟨rfl, rfl⟩⟩⟩
    rw [hb.1, hb.2]
    rename_i k dist _ _
    rcases or_dist_iff_eq.mp dist with k_is | i_is
    · rw [← k_is]
      use of (i + 1) * of i, of i * of (i + 1), 1, 1, 0
      exact ⟨grid_sz.adjacent i (i + 1) dist_succ, ⟨grid_top_bottom_word _, ⟨rfl, rfl⟩⟩⟩
    rw [← i_is]
    use of k * of (k + 1), of (k + 1) * of k, 1, 1, 0
    exact ⟨grid_sz.adjacent _ _ (by unfold Nat.dist; simp), ⟨grid_top_bottom_word _, ⟨rfl, rfl⟩⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ha | hb
    · rw [ha.1, ha.2]
      use of j, 1, of i, 0, 1
      exact ⟨grid_sz.top_bottom _, ⟨grid_sz.separated _ _ h, ⟨rfl, rfl⟩⟩⟩
    rw [hb.1, hb.2]
    use of j, of i, 1, 1, 0
    exact ⟨grid_sz.separated _ _ h, ⟨grid_sz.top_bottom _, ⟨rfl, rfl⟩⟩⟩
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h n3 i j k n4
    intro fi₁ fi₂ fi_is
    rcases FreeMonoid.prod_eq_prod fi_is with ha | hb
    · rcases ha with ⟨m, hm1, hm2⟩
      rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, n1, n2, g1, g2, hk, n_is⟩
      use u, g * k₁, k₂, n3 + n1, n2
      rw [hm1]
      exact ⟨grid_sz.vertical h1 g1, ⟨g2, ⟨by rw [mul_assoc, hk], by omega⟩⟩⟩
    rcases hb with ⟨m, hm1, hm2⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, n1, n2, g1, g2, hh, n_is⟩
    use u, h₁, (h₂ * j), n1, n2 + n4
    rw [hm2]
    exact ⟨g1, ⟨grid_sz.vertical g2 h2, ⟨by rw [← mul_assoc, hh], by omega⟩ ⟩⟩
  | horizontal _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, n1, n2, hg1, hg2, heq, n_is⟩
    rcases h2_ih m n heq with ⟨o, p, q, n3, n4, hg3, hg4, heq', n'_is⟩
    use l * o, p, q, n1 + n3, n2 + n4
    exact ⟨grid_sz.horizontal hg1 hg3, ⟨grid_sz.horizontal hg2 hg4, ⟨heq', by omega⟩ ⟩⟩
