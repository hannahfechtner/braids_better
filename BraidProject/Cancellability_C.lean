import BraidProject.Stability'
import BraidProject.Grids_C
import BraidProject.FlipBraid'
import BraidProject.Cancellability

namespace Braid

def gridt_of_grid (h : grid a b c d) : Nonempty (gridt a b c d) := by
  induction h with
  | empty =>
    apply Nonempty.intro gridt.empty
  | top_bottom i => apply Nonempty.intro (gridt.top_bottom i)
  | sides i => apply Nonempty.intro (gridt.sides i)
  | top_left i => apply Nonempty.intro (gridt.top_left i)
  | adjacent i k h => apply Nonempty.intro (gridt.adjacent i k h)
  | separated i j h => apply Nonempty.intro (gridt.separated i j h)
  | vertical h1 h2 ih1 ih2 =>
    exact Nonempty.intro ((Classical.choice ih1).vertical (Classical.choice ih2))
  | horizontal h1 h2 ih1 ih2 =>
    exact Nonempty.intro ((Classical.choice ih1).horizontal (Classical.choice ih2))

theorem grid_of_gridt (h : gridt a b c d) : grid a b c d := by
  induction h with
  | empty => exact grid.empty
  | top_bottom i => exact grid.sides i
  | sides i => exact grid.sides i
  | top_left i => exact grid.top_left i
  | adjacent i k h => exact grid.adjacent i k h
  | separated i j h => exact grid.separated i j h
  | vertical h1 h2 ih1 ih2 => exact ih1.vertical ih2
  | horizontal h1 h2 ih1 ih2 => exact ih1.horizontal ih2

def unicity_c {a b c d c' d'} (h1 : gridt a b c d) : gridt a1 b1 c' d' → a = a1 → b = b1 → PLift (c' = c) × PLift (d' = d) := by
  intro h2 a_is b_is
  rw [← a_is, ← b_is] at h2
  have H := unicity (grid_of_gridt h1) _ _ (grid_of_gridt h2)
  exact ⟨⟨H.1⟩, ⟨H.2⟩⟩

noncomputable def existence' : ∀ a b, ∃ c d, Nonempty (gridt a b c d) := by
  intro a b
  rcases common_right_mul_inf_mk a b with ⟨d1, c1, h⟩
  have big_grid : grid (a * c1) (b * d1) 1 1 := by
    apply grid_of_eq
    rw [h]
  rcases splittable_horizontally_of_grid big_grid _ _ rfl with ⟨_, c₁, c₂, top_grid, _, side_one⟩
  rw [(FreeMonoid.prod_eq_one side_one.symm).1] at top_grid
  rcases splittable_vertically_of_grid top_grid _ _ rfl with ⟨top_vert, m₁, m₂, top_left, _, _⟩
  use top_vert, m₁
  apply gridt_of_grid
  exact top_left

noncomputable def existence_s : ∀ a b, Σ c d, gridt a b c d :=
  fun a b => ⟨_, _, (existence' a b).choose_spec.choose_spec.some⟩

end Braid
