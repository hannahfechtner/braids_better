import BraidProject.BraidMonoidInf
import Mathlib.Data.Nat.Dist
import BraidProject.Additions.FreeMonoid
import BraidProject.Additions.NatDist

open FreeMonoid

namespace Braid
/-- a rectangular grid for the braid monoid, inductively defined as from the set of basic cells,
along with vertical and horizontal closure under abutting -/
inductive grid : FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → Prop
  | empty : grid 1 1 1 1
  | top_bottom (i : ℕ) : grid 1 (of i) (of i) 1
  | sides (i : ℕ) : grid (of i) 1 1 (of i)
  | top_left (i : ℕ) : grid (of i) (of i) 1 1
  | adjacent (i k : ℕ) (h : i.dist k = 1) : grid (of i) (of k) (of k * of i) (of i * of k)
  | separated (i j : ℕ) (h : i.dist j > 1) : grid (of i) (of j) (of j) (of i)
  | vertical (h1: grid a b c d) (h2 : grid e c f g) : grid (a * e) b f (d * g)
  | horizontal (h1: grid a b c d) (h2 : grid d e f g) : grid a (b * e) (c * f) g

namespace Grid

/-- grids can be flipped along their NW - SE axis to produce another grid -/
noncomputable def swap : grid a b c d → grid b a d c := by
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

/-- Given any word u, there is a grid with u on the left and right sides, and 1 on the top and
bottom -/
theorem sides_word (u : FreeMonoid ℕ) : grid u 1 1 u := by
  induction u with
  | one => exact grid.empty
  | of => exact grid.sides _
  | mul x y ih1 ih2 => exact grid.vertical ih1 ih2

/-- Given any word u, there is a grid with u on the top and bottom, and 1 on the left and
right sides -/
theorem top_bottom_word (u : FreeMonoid ℕ) : grid 1 u u 1 := swap (sides_word _)

/-- Given any word u, there is a grid with u on the top and left sides, and 1 on the bottom and
right sides -/
theorem top_left_word (u : FreeMonoid ℕ) : grid u u 1 1 := by
  induction u with
  | one => exact grid.empty
  | of => exact grid.top_left _
  | mul x y ih1 ih2 =>
    exact grid.vertical (grid.horizontal ih1 (top_bottom_word y))
      (grid.horizontal (sides_word y) ih2)

/-- relating grid equivalence to braid equivalence in the forward direction -/
theorem braid_eq_of_grid (h : grid a b c d) :
    BraidMonoidInf.mk (a * c) = BraidMonoidInf.mk (b * d) := by
  induction h with
  | empty => rfl
  | top_bottom i => rfl
  | sides i => rfl
  | top_left i => rfl
  | adjacent i k h_dist =>
    simp only [BraidMonoidInf.mk_mul, ← mul_assoc]
    exact BraidMonoidInf.braid_rw_self _ _ h_dist
  | separated i j h =>
    simp only [BraidMonoidInf.mk_mul]
    rw [BraidMonoidInf.comm_rw_self i j h]
  | vertical _ _ h1_ih h2_ih =>
    simp_all only [BraidMonoidInf.mk_mul, ← mul_assoc]
    rw [← h1_ih, mul_assoc, h2_ih, ← mul_assoc]
  | horizontal _ _ h1_ih h2_ih =>
    simp_all only [BraidMonoidInf.mk_mul, mul_assoc]
    rw [← h2_ih, ← mul_assoc, h1_ih, ← mul_assoc]

theorem braid_equiv_of_grid_empty_sink : grid a b 1 1 → BraidMonoidInf.rel a b := by
  intro h
  apply BraidMonoidInf.exact
  rw [← mul_one a, ← mul_one b]
  exact braid_eq_of_grid h

/- the length of the words labelling the left-bottom and top-right paths in a grid are equal -/
theorem diag_length_eq (h : grid a b c d) : a.length + c.length = b.length + d.length := by
  have H := congr_arg BraidMonoidInf.length (braid_eq_of_grid h)
  simp only [BraidMonoidInf.length_mk, length_mul] at H
  exact H

def split_vertically (a b c d : FreeMonoid ℕ) := ∀ b₁ b₂, b = b₁ * b₂ →
  ∃ u c₁ c₂, grid a b₁ c₁ u ∧ grid u b₂ c₂ d ∧ c = c₁ * c₂

/-- if the top of a grid consists of two or more arrows, the grid may be divided into a
left subgrid and a right subgrid. The edge case where either b₁ or b₂ is 1 is dealt with
by using a side-side grid -/
theorem splittable_vertically {a b c d : FreeMonoid ℕ} (h : grid a b c d) :
    split_vertically a b c d := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1
    exact ⟨grid.empty, ⟨grid.empty, rfl⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · use 1, 1, of i
      exact ⟨grid.empty, ⟨grid.top_bottom _, rfl⟩⟩
    use 1, (of i), 1
    exact ⟨grid.top_bottom _, ⟨grid.empty, rfl⟩⟩
  | sides i =>
    intro _ _ b_is
    use (of i), 1, 1
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    exact ⟨grid.sides _, ⟨grid.sides _, rfl⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · use (of i), 1, 1
      exact ⟨grid.sides _, ⟨grid.top_left _, rfl⟩⟩
    use 1, 1, 1
    exact ⟨grid.top_left _, ⟨grid.empty, rfl⟩⟩
  | adjacent i k l =>
    intro m n b_is
    rcases (FreeMonoid.prod_eq_of b_is.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases or_dist_iff_eq.mp l with rfl | rfl
      · use of i, 1, of (i+1) * of i
        exact ⟨grid.sides i, ⟨grid.adjacent i (i+1) dist_succ, rfl⟩⟩
      use of (k+1), 1, of k * of (k+1)
      exact ⟨grid.sides (k+1), ⟨grid.adjacent (k+1) k l, rfl⟩⟩
    · rcases or_dist_iff_eq.mp l with rfl | rfl
      · use of i * of (i+1), of (i+1) * of i, 1
        exact ⟨grid.adjacent i (i+1) dist_succ, ⟨sides_word _, rfl⟩⟩
      use of (k+1) * of k, of k * of (k+1), 1
      exact ⟨grid.adjacent _ _ l, ⟨sides_word _, rfl⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · use of i, 1, of j
      exact ⟨grid.sides _, ⟨grid.separated _ _ h, rfl⟩⟩
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
    rcases FreeMonoid.prod_eq_prod fi_is with ⟨m, rfl, hm2⟩ | ⟨m, hm1, rfl⟩
    · rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, hk⟩
      use u, g * k₁, k₂
      exact ⟨grid.horizontal h1 g1, ⟨g2, by rw [mul_assoc, hk]⟩⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, hh⟩
    use u, h₁, (h₂ * j)
    exact ⟨g1, ⟨grid.horizontal g2 h2, by rw [← mul_assoc, hh]⟩⟩

def split_horizontally (a b c d : FreeMonoid ℕ) := ∀ a₁ a₂, a = a₁ * a₂ →
  ∃ u d₁ d₂, grid a₁ b u d₁ ∧ grid a₂ u c d₂ ∧ d = d₁ * d₂

/-- if the left side of a grid consists of two or more arrows, the grid may be divided into a
top subgrid and a bottom subgrid. edge case where either a₁ or a₂ is 1 is dealt with by appending
a top-bottom grid -/
theorem splittable_horizontally {a b c d : FreeMonoid ℕ} (h : grid a b c d) :
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
    rcases FreeMonoid.prod_eq_of b_is.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · use 1, 1, of i
      exact ⟨grid.empty, ⟨grid.sides _, rfl⟩⟩
    use 1, of i, 1
    exact ⟨grid.sides _, ⟨grid.empty, rfl⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · use of i, 1, 1
      exact ⟨grid.top_bottom _, ⟨grid.top_left _, rfl⟩⟩
    use 1, 1, 1
    exact ⟨grid.top_left _, ⟨grid.empty, rfl⟩⟩
  | adjacent i j dist =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases or_dist_iff_eq.mp dist with rfl | rfl
      · use of (i+1), 1, of i * of (i + 1)
        exact ⟨grid.top_bottom _, ⟨grid.adjacent i (i + 1) dist_succ, rfl⟩⟩
      use of j, 1, of (j + 1) * of j
      exact ⟨grid.top_bottom _, ⟨grid.adjacent _ _ succ_dist, rfl⟩⟩
    rcases or_dist_iff_eq.mp dist with k_is | i_is
    · rw [← k_is]
      use of (i + 1) * of i, of i * of (i + 1), 1
      exact ⟨grid.adjacent i (i + 1) dist_succ, ⟨top_bottom_word _, rfl⟩⟩
    rw [← i_is]
    use of j * of (j + 1), of (j + 1) * of j, 1
    exact ⟨grid.adjacent _ _ succ_dist, ⟨top_bottom_word _, rfl⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of b_is.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · use of j, 1, of i
      exact ⟨grid.top_bottom _, ⟨grid.separated _ _ h, rfl⟩⟩
    use of j, of i, 1
    exact ⟨grid.separated _ _ h, ⟨grid.top_bottom _, rfl⟩⟩
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    rcases FreeMonoid.prod_eq_prod fi_is with ⟨m, rfl, hm2⟩ | ⟨m, hm1, rfl⟩
    · rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, hk⟩
      use u, h * k₁, k₂
      exact ⟨grid.vertical h1 g1, ⟨g2, by rw [mul_assoc, hk]⟩⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, hh⟩
    use u, h₁, (h₂ * k)
    exact ⟨g1, ⟨grid.vertical g2 h2, by rw [← mul_assoc, hh]⟩⟩
  | horizontal _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, heq⟩
    rcases h2_ih m n heq with ⟨o, p, q, hg3, hg4, heq'⟩
    use l * o, p, q
    exact ⟨grid.horizontal hg1 hg3, ⟨grid.horizontal hg2 hg4, heq'⟩⟩

end Grid
end Braid
