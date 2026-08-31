import Mathlib.RingTheory.OreLocalization.Basic
import BraidProject.PresentedMonoid_mine
import Mathlib.Algebra.Group.Units.Equiv

class HasCommonLeftMultipleData (M : Type*) [Mul M] where
  cl₁ : M → M → M
  cl₂ : M → M → M
  cl_spec : ∀ a b : M, cl₂ a b * a = cl₁ a b * b

namespace SelfC

open OreLocalization

variable {M : Type*} [Monoid M] [IsCancelMul M] [HasCommonLeftMultipleData M]

open HasCommonLeftMultipleData
instance : OreLocalization.OreSet (⊤ : Submonoid M) where
  ore_right_cancel  := by aesop
  oreNum := fun a b => cl₁ a b
  oreDenom := fun a b => ⟨cl₂ a b, trivial⟩
  ore_eq := by
    intro r s
    simp [cl_spec]

local notation "OreLocalizationSelf" => OreLocalization (⊤ : Submonoid M) M

/-- when localizing by the entire monoid, the result is a group -/
instance : Group (OreLocalizationSelf) where
  inv := by
    use OreLocalization.liftExpand
      (fun a b => b.val /ₒ ⟨a, trivial⟩)
      (fun a b c d => by
      apply OreLocalization.oreDiv_eq_iff.mpr
      use 1, b
      simp)
  inv_mul_cancel := by
    apply OreLocalization.ind
    intro a b
    apply OreLocalization.mul_inv

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
    (h : ∀ (r : M), (φ ∘ OreLocalization.numeratorHom) r = f r)
    : φ = universalMonoidHom f :=
  OreLocalization.universalMulHom_unique f _ _ _ h

end SelfC

section Presented

private theorem lift_eq_lift_of_rel {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂)) :
    ∀ (a b : FreeMonoid α), PresentedMonoid.rel rels a b → (FreeMonoid.lift f) a =
    (FreeMonoid.lift f) b :=
  fun _ _ r ↦ ConGen.Rel.rec (fun x y rxy ↦ universal_h x y rxy) (fun _ ↦ rfl)
  (fun _ ryx ↦ ryx.symm) (fun _ _ rab rbc ↦ rab.trans rbc)
  (fun  _ _ ih1 ih2 ↦ by rw [map_mul, map_mul, ih1, ih2]) r

/-- a homomorphism from elements of a presented monoid viewed as a submonoid of itself
(which will become denominators) into units of the group -/
private def map_denom_into_units {G₁ : Type} [Group G₁] (f : α → G₁)
  (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂)) :
  ↥(⊤ : Submonoid (PresentedMonoid rels)) →* G₁ˣ :=
  ⟨⟨toUnits ∘ (PresentedMonoid.lift f (lift_eq_lift_of_rel f universal_h)) ∘ (fun x => x.val),
    (Units.val_eq_one.mp rfl)⟩,
    (by
      simp only [Function.comp_apply, Submonoid.coe_mul, Subtype.forall]
      intro a _ b _
      grind) ⟩


abbrev pml {α : Type}
    (rels : FreeMonoid α → FreeMonoid α → Prop)
    [IsCancelMul (PresentedMonoid rels)]
    [HasCommonLeftMultipleData (PresentedMonoid rels)]
    := OreLocalization (⊤ : Submonoid (PresentedMonoid rels)) (PresentedMonoid rels)

variable {α : Type} {rels : FreeMonoid α → FreeMonoid α → Prop}

variable [h : IsCancelMul (PresentedMonoid rels)] [h1 : HasCommonLeftMultipleData (PresentedMonoid rels)]

/-- the universal property for the ore localization of a presented monoid by itself -/
noncomputable def presented_fraction_group_to_group {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂)) :
    (pml rels) →* G₁ :=
    OreLocalization.universalMulHom
  ⟨⟨PresentedMonoid.lift f (lift_eq_lift_of_rel f universal_h), rfl⟩,
  by intro x y; simp only; erw [(PresentedMonoid.lift f
  (lift_eq_lift_of_rel f universal_h)).map_mul x y]⟩ (map_denom_into_units f universal_h)
  (fun _ => rfl)

theorem presented_fraction_group_to_group_unique {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂))
    (φ : (pml rels) →* G₁) :
    (∀ (r : α), φ (OreLocalization.numeratorHom
    (PresentedMonoid.of rels r)) = f r) → φ =
    presented_fraction_group_to_group f universal_h := by
  intro hr
  apply SelfC.universalMonoidHom_unique
  intro r
  induction r with | h r'
  simp
  induction r' using FreeMonoid.inductionOn'
  · grind [PresentedMonoid.one_def]
  rename_i head tail ih
  simp only [PresentedMonoid.mk_mul]
  erw [(PresentedMonoid.lift f (lift_eq_lift_of_rel f universal_h)).map_mul]
  rw [← ih, ← OreLocalization.mul_div_one]
  rw [φ.map_mul]
  simp [mul_left_inj]
  conv => rhs; erw [PresentedMonoid.lift_mk]
  rw [← hr head]
  rfl

end Presented
