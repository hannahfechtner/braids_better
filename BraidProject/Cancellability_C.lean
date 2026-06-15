import BraidProject.Stability'
import BraidProject.Grids_C
import BraidProject.FlipBraid'
import BraidProject.Cancellability

namespace Braid
namespace GridData

def unicity {a b c d c' d'} (h1 : GridData a b c d) : GridData a1 b1 c' d' → a = a1 → b = b1 → PLift (c' = c) × PLift (d' = d) := by
  intro h2 a_is b_is
  rw [← a_is, ← b_is] at h2
  have H := Grid.unicity (to_grid h1) _ _ (to_grid h2)
  exact ⟨⟨H.1⟩, ⟨H.2⟩⟩

noncomputable def existence' : ∀ a b, ∃ c d, Nonempty (GridData a b c d) := by
  intro a b
  rcases common_right_mul_inf_mk a b with ⟨c1, d1, h⟩
  have big_grid : grid (a * c1) (b * d1) 1 1 := by
    apply Grid.of_mk_eq_mk
    rw [h]
    rfl
  rcases Grid.splittable_horizontally big_grid _ _ rfl with ⟨_, c₁, c₂, top_grid, _, side_one⟩
  rw [(FreeMonoid.prod_eq_one side_one.symm).1] at top_grid
  rcases Grid.splittable_vertically top_grid _ _ rfl with ⟨top_vert, m₁, m₂, top_left, _, _⟩
  use m₁, top_vert
  exact of_grid top_left

noncomputable def existence : ∀ a b, Σ c d, GridData a b c d :=
  fun a b => ⟨_, _, (existence' a b).choose_spec.choose_spec.some⟩

end GridData
end Braid
