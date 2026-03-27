import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.PresentedGroup
import BraidProject.Additions.FreeMonoid
import BraidProject.PresentedMonoid_mine

namespace PresentedGroup

theorem mk_eq_lift_of  (rels : Set (FreeGroup α)) :
  PresentedGroup.mk rels = FreeGroup.lift PresentedGroup.of :=
  FreeGroup.ext_hom _ _ (congrFun rfl)

def free_group_set_of_function (rels : FreeMonoid α → FreeMonoid α → Prop) : Set (FreeGroup α) :=
  {FreeMonoid.lift (FreeGroup.of) x.1 * (FreeMonoid.lift (FreeGroup.of) x.2)⁻¹ |
  x ∈ setOf (fun (a : FreeMonoid α × FreeMonoid α) => rels a.1 a.2)}

theorem free_group_set_of_function_lift_eq_one_iff {G₁ : Type} [Group G₁]
    {rels : FreeMonoid α → FreeMonoid α → Prop} (f : α → G₁) :
    (∀ r ∈ free_group_set_of_function rels, (FreeGroup.lift f) r = 1) ↔
    (∀ r₁ r₂, rels r₁ r₂ → FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂) := by
  constructor
  · intro h r₁ r₂ _
    have : FreeMonoid.lift FreeGroup.of r₁ * (FreeMonoid.lift FreeGroup.of r₂)⁻¹ ∈
        free_group_set_of_function rels := by
      use ⟨r₁, r₂⟩
      simpa only [Set.mem_setOf_eq, and_true]
    specialize h (FreeMonoid.lift FreeGroup.of r₁ * (FreeMonoid.lift FreeGroup.of r₂)⁻¹) this
    rw [map_mul, map_inv, ← FreeMonoid.lift_eq_FreeGroup_lift_comp_of_apply,
      ← FreeMonoid.lift_eq_FreeGroup_lift_comp_of_apply,
      ← mul_left_inj (FreeMonoid.lift f r₂), inv_mul_cancel_right, one_mul] at h
    exact h
  intro h r hr
  rcases hr with ⟨⟨a, b⟩, h1, rfl⟩
  simp only [map_mul, map_inv]
  rw [← FreeMonoid.lift_eq_FreeGroup_lift_comp_of_apply,
    ← FreeMonoid.lift_eq_FreeGroup_lift_comp_of_apply, h a b h1]
  exact mul_inv_cancel ((FreeMonoid.lift f) b)

theorem lift_of_eq_one_of_mem_free_group_set_of_function
    (r : FreeGroup α) (h : r ∈ free_group_set_of_function rels) :
    FreeGroup.lift PresentedGroup.of r =
    (1 : PresentedGroup (free_group_set_of_function rels)) := by
  rw [← PresentedGroup.mk_eq_lift_of]
  exact one_of_mem h

theorem mk_mul : PresentedGroup.mk rels (a * b) = PresentedGroup.mk rels a * PresentedGroup.mk rels b := by
  rw [map_mul]

-- @[simp]
-- theorem toGroup.mk {rels : FreeMonid α → FreeMonid α → Prop} {f : PresentedMonoid rels → G} [Group G]
--   (h : ∀ r ∈ free_group_set_of_function rels, @FreeGroup.lift (PresentedMonoid rels) G _ f r = 1) {x : FreeMonoid α} :
--   @toGroup (PresentedMonoid rels) G _ f (free_group_set_of_function rels) h (PresentedGroup.mk (free_group_set_of_function rels)
--    (FreeGroup.mk (List.map (fun x => (x, true)) a))) = f (PresentedMonoid.mk rels a) :=
--   sorry

end PresentedGroup
