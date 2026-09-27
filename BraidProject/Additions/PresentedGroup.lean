import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.PresentedGroup
import BraidProject.Additions.FreeMonoid
import BraidProject.Additions.PresentedMonoid

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

theorem eq_of_PresentedMonoid_eq {α : Type} {rels : FreeMonoid α → FreeMonoid α → Prop}
    {a b : FreeMonoid α} (h : PresentedMonoid.mk rels a = PresentedMonoid.mk rels b) :
    PresentedGroup.mk (free_group_set_of_function rels) (FreeMonoid.lift FreeGroup.of a) =
    PresentedGroup.mk (free_group_set_of_function rels) (FreeMonoid.lift FreeGroup.of b) := by
  rw [mk_eq_lift_of, ← FreeMonoid.lift_eq_FreeGroup_lift_comp_of_apply,
    ← FreeMonoid.lift_eq_FreeGroup_lift_comp_of_apply]
  exact congr_arg (@PresentedMonoid.lift _ _ _ (@PresentedGroup.of _ (free_group_set_of_function rels)) rels
    ((free_group_set_of_function_lift_eq_one_iff _).mp
     (fun r hr =>  lift_of_eq_one_of_mem_free_group_set_of_function _ hr))) h

theorem mk_eq_mk_of_subset {rels₁ rels₂ : Set (FreeGroup α)} (hsub : rels₁ ⊆ rels₂)
    {a b : FreeGroup α} (h : PresentedGroup.mk rels₁ a = PresentedGroup.mk rels₁ b) :
    PresentedGroup.mk rels₂ a = PresentedGroup.mk rels₂ b := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, mk_eq_one_iff] at h ⊢
  exact Subgroup.normalClosure_mono hsub h

theorem eq_of_PresentedMonoid_eq_rels_subset {α : Type}
    {rels : FreeMonoid α → FreeMonoid α → Prop} {group_rels : Set (FreeGroup α)}
    (hsub : free_group_set_of_function rels ⊆ group_rels) {a b : FreeMonoid α}
    (h : PresentedMonoid.mk rels a = PresentedMonoid.mk rels b) :
    PresentedGroup.mk group_rels (FreeMonoid.lift FreeGroup.of a) =
    PresentedGroup.mk group_rels (FreeMonoid.lift FreeGroup.of b) :=
  mk_eq_mk_of_subset hsub (eq_of_PresentedMonoid_eq h)

end PresentedGroup
