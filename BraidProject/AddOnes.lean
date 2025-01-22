import BraidProject.BraidMonoid
import BraidProject.BraidGroup

variable {a : Type*}

open FreeMonoid'

inductive rev_rels : FreeMonoid' ((FreeMonoid' ℕ) × Bool) → FreeMonoid' ((FreeMonoid' ℕ) × Bool) → Prop
  | inverse (a : ℕ): rev_rels [(of a, false), (of a, true)] []
  | adjacent (a b : ℕ) (h : Nat.dist a b = 1) : rev_rels [(of a,false), (of b, true)] [(of b, true), (of a, true), (of b, false), (of a, false)]
  | separated (a c : ℕ) (h : Nat.dist a c > 1) : rev_rels [(of a, false), (of c, true)] [(of c, true), (of a, false)]

inductive rev_rels_one : FreeMonoid' ((FreeMonoid' ℕ) × Bool) → FreeMonoid' ((FreeMonoid' ℕ) × Bool) → Prop
  | inverse (a : ℕ): rev_rels_one [(of a, false), (of a, true)] [(1, true), (1, false)]
  | adjacent (a b : ℕ) (h : Nat.dist a b = 1) : rev_rels_one [(of a,false), (of b, true)] [(of b, true), (of a, true), (of b, false), (of a, false)]
  | separated (a c : ℕ) (h : Nat.dist a c > 1) : rev_rels_one [(of a, false), (of c, true)] [(of c, true), (of a, false)]
  | one_over (a : ℕ) : rev_rels_one [(of a, false), (1, true)] [(1, true), (of a, false)]
  | one_up (a : ℕ) : rev_rels_one [(1, false), (of a, true)] [(of a, true), (1, false)]

def remove_ones (b : FreeMonoid' (FreeMonoid' ℕ × Bool)) : FreeMonoid' (FreeMonoid' ℕ × Bool) :=
  match b with
  | 1 => 1
  | (1, true) :: a => remove_ones a
  | (1, false) :: a => remove_ones a
  | (a :: b, true) :: c => (a::b, true) :: (remove_ones c)
  | (a :: b, false) :: c => (a::b, false) :: (remove_ones c)
open PresentedMonoid

theorem add_ones {a b : FreeMonoid' (FreeMonoid' ℕ × Bool)} (h : Con'Gen.Rel rev_rels a b) :
    ∃ c, PresentedMonoid.rel rev_rels_one a c ∧ remove_ones c = b := by
  induction h with
  | of x y h =>
    cases h with
    | inverse a =>
      use [(1, true), (1, false)]
      constructor
      · apply rel_alone
        exact rev_rels_one.inverse a
      rfl
    | adjacent a b h =>
      use [(FreeMonoid'.of b, true), (FreeMonoid'.of a, true), (FreeMonoid'.of b, false),
        (FreeMonoid'.of a, false)]
      constructor
      · apply rel_alone
        exact rev_rels_one.adjacent a b h
      rfl
    | separated a c h =>
      use [(FreeMonoid'.of c, true), (FreeMonoid'.of a, false)]
      constructor
      · apply rel_alone
        exact rev_rels_one.separated a c h
      rfl
  | refl x =>
    use x
    constructor
    · exact PresentedMonoid.refl
    sorry
  | symm k hk => sorry
  | trans h1 h2 ih1 ih2 =>
    rename_i x y z
    rcases ih1 with ⟨c1, hc1⟩
    rcases ih2 with ⟨c2, hc2⟩
    use c2
    constructor
    · apply hc1.1.trans
      have H : rel rev_rels_one c1 y := by
        rw [← hc1.2]
        sorry
      exact H.trans hc2.1
    exact hc2.2
  | mul h1 h2 ih1 ih2 =>
    rename_i w x y z
    rcases ih1 with ⟨c1, hc1⟩
    rcases ih2 with ⟨c2, hc2⟩
    use c1 * c2
    constructor
    · exact mul hc1.1 hc2.1
    rw [← hc2.2, ← hc1.2]
    sorry
