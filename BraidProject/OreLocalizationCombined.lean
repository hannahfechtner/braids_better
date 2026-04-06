import Mathlib.RingTheory.OreLocalization.Basic
import BraidProject.PresentedMonoid_mine
import Mathlib.Algebra.Group.Units.Equiv
import BraidProject.Additions.OreLocalization
import BraidProject.Additions.Mixins
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup
import BraidProject.Additions.PresentedGroup
import BraidProject.Additions.FreeMonoid
import BraidProject.Additions.List
import BraidProject.Additions.Hom

namespace OreLocalization
namespace Self

section Nonconstructive
variable {M : Type*} [Monoid M] [IsRightCancelMul M] [IsCommonLeftMultipleMul M]

open IsCommonLeftMultipleMul in
noncomputable instance : OreLocalization.OreSet (⊤ : Submonoid M) where
  ore_right_cancel  := by aesop
  oreNum r s := Classical.choose (Classical.choose_spec (common_left_multiple r s))
  oreDenom r s :=⟨(Classical.choose (common_left_multiple r s)), trivial⟩
  ore_eq := by
    intro r s
    rcases Classical.choose_spec (common_left_multiple r s) with ⟨d1, hd1⟩
    simp [hd1]

end Nonconstructive

section Constructive

variable {M : Type*} [Monoid M] [IsRightCancelMul M] [IsCommonLeftMultipleMul M]

open IsCommonLeftMultipleMul in
noncomputable instance : OreLocalization.OreSet (⊤ : Submonoid M) where
  ore_right_cancel  := by aesop
  oreNum r s := Classical.choose (Classical.choose_spec (common_left_multiple r s))
  oreDenom r s :=⟨(Classical.choose (common_left_multiple r s)), trivial⟩
  ore_eq := by
    intro r s
    rcases Classical.choose_spec (common_left_multiple r s) with ⟨d1, hd1⟩
    simp [hd1]
end Constructive

variable {M : Type} [Monoid M] [OreLocalization.OreSet (⊤ : Submonoid M)]

local notation "OreLocalizationSelf" => OreLocalization (⊤ : Submonoid M) M

/-- when localizing by the entire monoid, the result is a group -/
instance : Group OreLocalizationSelf where
  inv := OreLocalization.liftExpand (fun a b => b.val /ₒ ⟨a, trivial⟩)
    fun a b c d => by
      apply OreLocalization.oreDiv_eq_iff.mpr
      use 1, b
      simp
  inv_mul_cancel := OreLocalization.ind fun _ _ => OreLocalization.mul_inv _ _

/-- simplified universal property when localizing by the entire monoid -/
def universalMonoidHom {G₁ : Type} [Group G₁] (f : M →* G₁) :
    OreLocalizationSelf →* G₁ :=
  OreLocalization.universalMulHom f
  ⟨⟨(fun (x : ↥((⊤ : Submonoid M))) => toUnits (f x.val)),
  by simp only [OneMemClass.coe_one, map_one]⟩, by simp only
  [Submonoid.coe_mul, map_mul, implies_true]⟩ (by intro s ; simp)

/-- uniqueness of the simplified universal property when localizing by the entire monoid -/
theorem universalMonoidHom_unique {G₁ : Type} [Group G₁] (f : M →* G₁)
    (φ : OreLocalizationSelf →* G₁)
    (h : ∀ (r : M), (φ ∘ OreLocalization.numeratorHom) r = f r) : φ = universalMonoidHom f :=
  OreLocalization.universalMulHom_unique f _ _ _ h


namespace OreLocalization
variable {α : Type} (rels : FreeMonoid α → FreeMonoid α → Prop)
  [h1 : OreLocalization.OreSet (⊤ : Submonoid (PresentedMonoid rels))]

abbrev PresentedMonoidFullLocalization :=
  OreLocalization (⊤ : Submonoid (PresentedMonoid rels)) (PresentedMonoid rels)

namespace Presented

open PresentedMonoid in
def universalMonoidHom {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂)) :
    PresentedMonoidFullLocalization rels →* G₁ := by
  apply Self.universalMonoidHom
  apply PresentedMonoid.lift f (PresentedMonoid.freeMonoid_lift_eq_of_rel f universal_h)

open PresentedMonoid in
theorem universalMonoidHom_unique {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂))
    (φ : PresentedMonoidFullLocalization rels →* G₁)
    (hr : ∀ (r : α), φ (OreLocalization.numeratorHom (PresentedMonoid.of rels r)) = f r) :
    φ = universalMonoidHom rels f universal_h := by
  apply Self.universalMonoidHom_unique
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  intro pr
  induction pr with | h fr
  induction fr using FreeMonoid.inductionOn' with
  | one => grind [PresentedMonoid.one_def]
  | mul_of head tail ih =>
    simp only [PresentedMonoid.mk_mul]
    erw [(PresentedMonoid.lift f (freeMonoid_lift_eq_of_rel f universal_h)).map_mul, ← ih]
    rw [Function.comp_apply, ← OreLocalization.mul_div_one, φ.map_mul, Function.comp_apply,
      mul_left_inj]
    conv => rhs; erw [PresentedMonoid.lift_mk]
    rw [← hr head]
    rfl

open PresentedGroup

def PresentedMonoidFullLocalization_to_presented_group :
    PresentedMonoidFullLocalization rels →* PresentedGroup (free_group_set_of_function rels) :=
  universalMonoidHom rels (PresentedGroup.of) <|
  (free_group_set_of_function_lift_eq_one_iff PresentedGroup.of).mp
  lift_of_eq_one_of_mem_free_group_set_of_function

@[simp]
theorem PresentedMonoidFullLocalization_to_presented_group_apply_of (a : α) :
    PresentedMonoidFullLocalization_to_presented_group rels
    (OreLocalization.numeratorHom (PresentedMonoid.of rels a)) = PresentedGroup.of a :=
  rfl

theorem PresentedMonoidFullLocalization_to_presented_group_apply_mk (a : FreeMonoid α) :
    PresentedMonoidFullLocalization_to_presented_group rels
    (OreLocalization.numeratorHom (PresentedMonoid.mk rels a)) =
    PresentedGroup.mk (free_group_set_of_function rels)
    (FreeGroup.mk (List.map (fun x => (x, true)) a)) := by
  induction a using FreeMonoid.inductionOn'
  · rfl
  rename_i head tail ih
  rw [PresentedMonoid.mk_mul, map_mul, map_mul, ih]
  change _ = (PresentedGroup.mk _) (FreeGroup.mk ([(head, true)]) *
      FreeGroup.mk (List.map (fun x ↦ (x, true)) tail))
  rw [map_mul, mul_left_inj]
  rfl

open PresentedMonoid in
private theorem lift_numeratorHom_eq_one_of_mem_free_group_set_of_function (r : FreeGroup α)
    (r_in : r ∈ free_group_set_of_function rels) :
    (FreeGroup.lift fun x => OreLocalization.numeratorHom (PresentedMonoid.of rels x)) r =
    (1 : PresentedMonoidFullLocalization rels) := by
  rcases r_in with ⟨⟨a, b⟩, h1, rfl⟩
  rw [Set.mem_setOf_eq] at h1
  rw [map_mul, map_inv, ← FreeMonoid.lift_eq_FreeGroup_lift_comp_of_apply,
      ← FreeMonoid.lift_eq_FreeGroup_lift_comp_of_apply, freeMonoid_lift_of_eq_mk_of_mulHom,
      freeMonoid_lift_of_eq_mk_of_mulHom, PresentedMonoid.sound (PresentedMonoid.rels_alone h1)]
  exact mul_inv_cancel _

noncomputable def presentedGroup_to_PresentedMonoidFullLocalization :
    PresentedGroup (free_group_set_of_function rels) →* PresentedMonoidFullLocalization rels :=
  PresentedGroup.toGroup (lift_numeratorHom_eq_one_of_mem_free_group_set_of_function rels)

@[simp]
theorem presentedGroup_to_PresentedMonoidFullLocalization_apply_of (a : α) :
    presentedGroup_to_PresentedMonoidFullLocalization rels (PresentedGroup.of a) =
    OreLocalization.numeratorHom (PresentedMonoid.of rels a) := by
  unfold presentedGroup_to_PresentedMonoidFullLocalization
  simp only [PresentedGroup.toGroup.of]

theorem List.map_mul (a b : FreeMonoid α) : List.map f (a * b) = List.map f a ++ List.map f b := by
  rw [← List.map_append]
  congr

@[simp]
theorem presentedGroup_to_PresentedMonoidFullLocalization_apply_mk (a : FreeMonoid α) :
    presentedGroup_to_PresentedMonoidFullLocalization rels
    (PresentedGroup.mk (free_group_set_of_function rels) (FreeGroup.mk (List.map (fun x => (x, true)) a))) =
    OreLocalization.numeratorHom (PresentedMonoid.mk rels a) := by
  unfold presentedGroup_to_PresentedMonoidFullLocalization
  induction a using FreeMonoid.inductionOn' with
  | one =>
    erw [List.map_nil]
    change (toGroup _) 1 = 1 /ₒ 1
    simp [OreLocalization.one_def]
  | mul_of b a ih =>
    rw [PresentedMonoid.mk_mul]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk] at ih
    rw [← mul_div_one,← ih, List.map_mul, ← FreeGroup.mul_mk, map_mul, map_mul, mul_left_inj]
    apply presentedGroup_to_PresentedMonoidFullLocalization_apply_of

theorem presentedGroup_to_pmfl_comp_pmfl_to_presentedGroup :
    (presentedGroup_to_PresentedMonoidFullLocalization rels).comp
    (PresentedMonoidFullLocalization_to_presented_group rels) = MonoidHom.id _ := by
  have unique_map_to_self := universalMonoidHom_unique rels
    (fun a => OreLocalization.numeratorHom (PresentedMonoid.of rels a))
    ((free_group_set_of_function_lift_eq_one_iff _).mp <|
    lift_numeratorHom_eq_one_of_mem_free_group_set_of_function rels)
  have := unique_map_to_self (MonoidHom.comp (presentedGroup_to_PresentedMonoidFullLocalization rels)
    (PresentedMonoidFullLocalization_to_presented_group rels)) (fun x => by simp only [MonoidHom.coe_comp,
    Function.comp_apply, PresentedMonoidFullLocalization_to_presented_group_apply_of,
    presentedGroup_to_PresentedMonoidFullLocalization_apply_of])
  rw [this]
  exact (unique_map_to_self ⟨⟨id, rfl⟩, fun _ _ => rfl⟩
    (fun r => by simp only [MonoidHom.coe_mk, OneHom.coe_mk, id_eq])).symm

theorem pmfl_to_presentedGroup_comp_presentedGroup_to_pmfl :
    (PresentedMonoidFullLocalization_to_presented_group rels).comp
    (presentedGroup_to_PresentedMonoidFullLocalization rels) = MonoidHom.id _ := by
  ext x
  apply PresentedGroup.toGroup.unique lift_of_eq_one_of_mem_free_group_set_of_function
  intro y
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    presentedGroup_to_PresentedMonoidFullLocalization_apply_of,
    PresentedMonoidFullLocalization_to_presented_group_apply_of]

/-- the localization of a presented monoid is isomorphic to the presented group over the same
relations-/
noncomputable def presentedMonoidLocalizationEquivPresentedGroup :
    PresentedMonoidFullLocalization rels ≃* PresentedGroup (free_group_set_of_function rels) :=
  ⟨⟨PresentedMonoidFullLocalization_to_presented_group rels,
  presentedGroup_to_PresentedMonoidFullLocalization rels,
  Function.leftInverse_iff_comp.mpr <| MonoidHom.comp_toFun
  (presentedGroup_to_pmfl_comp_pmfl_to_presentedGroup rels),
  Function.rightInverse_iff_comp.mpr <| MonoidHom.comp_toFun
  (pmfl_to_presentedGroup_comp_presentedGroup_to_pmfl rels)⟩,
  map_mul (PresentedMonoidFullLocalization_to_presented_group rels)⟩

theorem PresentedMonoidFullLocalization_to_presented_group_injective :
    Function.Injective (PresentedMonoidFullLocalization_to_presented_group rels) :=
  Function.LeftInverse.injective <| congrFun (MonoidHom.comp_toFun
  (presentedGroup_to_pmfl_comp_pmfl_to_presentedGroup rels))

theorem PresentedMonoidFullLocalization_to_presented_group_surjective :
    Function.Surjective (PresentedMonoidFullLocalization_to_presented_group rels) :=
  Function.RightInverse.surjective <| congrFun (MonoidHom.comp_toFun
  (pmfl_to_presentedGroup_comp_presentedGroup_to_pmfl rels))

theorem presentedMonoid_mk_eq_of_presentedGroup_mk_eq_of_positive [IsLeftCancelMul (PresentedMonoid rels)]
    (h : PresentedGroup.mk (free_group_set_of_function rels) (FreeGroup.mk e) =
    PresentedGroup.mk (free_group_set_of_function rels) (FreeGroup.mk d))
    (hd : ∀ x ∈ d, x.2 = true) (he : ∀ x ∈ e, x.2 = true) :
    PresentedMonoid.mk rels (List.map (fun x ↦ x.1) e) =
    PresentedMonoid.mk rels (List.map (fun x ↦ x.1) d) := by
  rw [← List.reconstruct_from_projection hd, ← List.reconstruct_from_projection he,
      ← PresentedMonoidFullLocalization_to_presented_group_apply_mk,
      ← PresentedMonoidFullLocalization_to_presented_group_apply_mk] at h
  apply numeratorHom_injective_of_cancellative _ _
    (PresentedMonoidFullLocalization_to_presented_group_injective rels h)

theorem presentedGroup_exists_fraction_form
    (c : PresentedGroup (free_group_set_of_function rels)) : ∃ (a b : PresentedMonoid rels),
    c = (PresentedMonoidFullLocalization_to_presented_group rels (numeratorHom b))⁻¹ *
    PresentedMonoidFullLocalization_to_presented_group rels (numeratorHom a) := by
  rcases PresentedMonoidFullLocalization_to_presented_group_surjective rels c with ⟨c', hc⟩
  unfold PresentedMonoidFullLocalization at c'
  cases hc' : c' with
  | c r s =>
    use r, s
    rw [← hc, hc', ← map_inv, ← map_mul]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv]
    rw [← map_inv, ← map_mul]
    change _ = (PresentedMonoidFullLocalization_to_presented_group rels)
      ((1 /ₒ s : PresentedMonoidFullLocalization rels) * (r /ₒ 1 : PresentedMonoidFullLocalization rels))
    rw [mul_div_one]
    simp
