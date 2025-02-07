import Mathlib.RingTheory.OreLocalization.Basic
import BraidProject.PresentedMonoid_mine
import Mathlib.Algebra.Group.Units.Equiv
open Classical

-- section Self

class IsCommonLeftMultipleMul (M : Type u) [Mul M] where
  cl₁ : M → M → M
  cl₂ : M → M → M
  cl_spec : ∀ a b : M, cl₂ a b * a = cl₁ a b * b

-- class OreMonoid (M : Type*) extends CommonLeftMultipleMonoid M, CancelMonoid M

--open OreMonoid
-- open OreLocalization

-- variable {M : Type*} [Monoid M] [OreSet (⊤ : Submonoid M)]

-- instance oreSetSelf : OreLocalization.OreSet (⊤ : Submonoid M) where
--   ore_right_cancel  := by
--     intro r1 r2 s eq
--     use 1
--     simp only [OneMemClass.coe_one, one_mul]
--     exact mul_right_cancel eq
--   oreNum r s := CommonLeftMultipleMonoid.cl₁ r s
--   oreDenom r s := ⟨CommonLeftMultipleMonoid.cl₂ r s, trivial⟩
--   ore_eq := fun r s => CommonLeftMultipleMonoid.cl_spec _ _

-- local notation "OreLocalizationSelf" => @OreLocalization M _ (⊤ : Submonoid M) _ M _

-- /-- when localizing by the entire monoid, the result is a group -/
-- instance group_of_self : Group (OreLocalizationSelf) where
--   inv := OreLocalization.liftExpand (fun a b => b.val /ₒ ⟨a, trivial⟩)
--     fun a b c d => by
--       apply OreLocalization.oreDiv_eq_iff.mpr
--       use 1, b
--       simp
--   mul_left_inv := OreLocalization.ind fun _ _ => OreLocalization.mul_inv _ _

-- /-- simplified universal property when localizing by the entire monoid -/
-- def fraction_group_to_group {G₁ : Type} [Group G₁] (f : M →* G₁) :
--     OreLocalizationSelf →* G₁ :=
--   OreLocalization.universalMulHom f
--   ⟨⟨(fun (x : ↥((⊤ : Submonoid M))) => toUnits (f x.val)),
--   by simp only [OneMemClass.coe_one, map_one]⟩, by simp only
--   [Submonoid.coe_mul, map_mul, Subtype.forall, implies_true, forall_const]⟩
--   (by intro s ; simp)

-- /-- uniqueness of the simplified universal property when localizing by the entire monoid -/
-- theorem fraction_group_to_group_unique {G₁ : Type} [Group G₁] (f : M →* G₁)
--     (φ : OreLocalizationSelf →* G₁)
--     (h : ∀ (r : M), (φ ∘ OreLocalization.numeratorHom) r = f r)
--     : φ = fraction_group_to_group f :=
--   OreLocalization.universalMulHom_unique f _ _ _ h


-- end Self

section Presented

variable {α : Type} {rels : FreeMonoid' α → FreeMonoid' α → Prop}
--local notation "P" => PresentedMonoid rels

-- variable {cl₁ : PresentedMonoid rels → PresentedMonoid rels → PresentedMonoid rels}
--   {cl₂ : PresentedMonoid rels → PresentedMonoid rels → PresentedMonoid rels}
--   (cl_spec : ∀ a b : PresentedMonoid rels, cl₂ a b * a = cl₁ a b * b)
variable {h1 : IsCommonLeftMultipleMul (PresentedMonoid rels)} {h : IsRightCancelMul (PresentedMonoid rels)}

open IsCommonLeftMultipleMul
instance oreSetSelf' : OreLocalization.OreSet (⊤ : Submonoid (PresentedMonoid rels)) where
  ore_right_cancel := by
    intro r1 r2 s eq
    use 1
    simp only [OneMemClass.coe_one, one_mul]
    exact mul_right_cancel eq
  oreNum r s := cl₁ r s
  oreDenom r s := ⟨cl₂ r s, trivial⟩
  ore_eq := fun r s => cl_spec _ _

instance : DivInvMonoid (@OreLocalization ((PresentedMonoid rels)) _
    (⊤ : Submonoid (PresentedMonoid rels)) (@oreSetSelf' _ rels h1 h) ((PresentedMonoid rels)) _) where
  inv :=     let _ := (@oreSetSelf' _ rels h1 h)
    OreLocalization.liftExpand (fun a b => b.val /ₒ ⟨a, trivial⟩)
    fun a b c d => by
      apply OreLocalization.oreDiv_eq_iff.mpr
      use 1, b
      simp


/-- when localizing by the entire monoid, the result is a group -/
instance group_of_self' : Group (@OreLocalization ((PresentedMonoid rels)) _
    (⊤ : Submonoid (PresentedMonoid rels)) (@oreSetSelf' _ rels h1 h) ((PresentedMonoid rels)) _) where
  mul := fun a b => a * b --OreLocalization.smul
  mul_assoc := mul_assoc --OreLocalization.mul_assoc
  one :=
    @OreLocalization.oreDiv _ _ _ (oreSetSelf') _ _ 1 1
  one_mul := one_mul --OreLocalization.one_mul
  mul_one := mul_one -- OreLocalization.mul_one
  inv :=
    let _ := (@oreSetSelf' _ rels h1 h)
    OreLocalization.liftExpand (fun a b => b.val /ₒ ⟨a, trivial⟩)
    fun a b c d => by
      apply OreLocalization.oreDiv_eq_iff.mpr
      use 1, b
      simp
  mul_left_inv :=
    --have H := oreSetSelf' h1 h
    @OreLocalization.ind _ _ _ (oreSetSelf') _ _ _ (fun _ _ => @OreLocalization.mul_inv _ _ _ (oreSetSelf') _ _)

-- variable [Group (OreLocalization (submonoid_self (PresentedMonoid rels)) (PresentedMonoid rels))]
-- local notation "OreLocalizationSelf_Presented" =>  OreLocalization (submonoid_self (PresentedMonoid rels)) (PresentedMonoid rels)

private theorem lift_eq_lift_of_rel {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂)) :
    ∀ (a b : FreeMonoid' α), PresentedMonoid.rel rels a b → (FreeMonoid'.lift f) a =
    (FreeMonoid'.lift f) b :=
  fun _ _ r ↦ Con'Gen.Rel.rec (fun x y rxy ↦ universal_h x y rxy) (fun _ ↦ rfl)
  (fun _ ryx ↦ ryx.symm) (fun _ _ rab rbc ↦ rab.trans rbc)
  (fun  _ _ ih1 ih2 ↦ by rw [map_mul, map_mul, ih1, ih2]) r

/-- a homomorphism from elements of a presented monoid viewed as a submonoid of itself
(which will become denominators) into units of the group -/
private def map_denom_into_units {G₁ : Type} [Group G₁] (f : α → G₁)
  (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂)) :
  ↥(⊤ : Submonoid (PresentedMonoid rels)) →* G₁ˣ :=
  ⟨⟨toUnits ∘ (PresentedMonoid.lift_hom f (lift_eq_lift_of_rel f universal_h)) ∘ (fun x => x.val),
    (Units.val_eq_one.mp rfl)⟩,
    (by
      simp only [Function.comp_apply, Submonoid.coe_mul, Subtype.forall]
      intro a _ b _
      simp only [map_mul] ) ⟩

abbrev pml (h1 h) := @OreLocalization (PresentedMonoid rels) _ (⊤ : Submonoid (PresentedMonoid rels))
  (@oreSetSelf' _ rels h1 h) (PresentedMonoid rels) _

-- instance get_oreset [h : OreMonoid (PresentedMonoid rels)] :
--     @OreLocalization.OreSet (PresentedMonoid rels) _ (submonoid_self (PresentedMonoid rels)) := @oreSetSelf (PresentedMonoid rels) h
-- theorem pml_is_group [OreMonoid (PresentedMonoid rels)] : Group (@OreLocalization (PresentedMonoid rels) _ (submonoid_self (PresentedMonoid rels)) _ (PresentedMonoid rels) _)

/-- the universal property for the ore localization of a presented monoid by itself -/
def presented_fraction_group_to_group {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂)) :
    (pml h1 h) →* G₁ :=
    @OreLocalization.universalMulHom ((PresentedMonoid rels)) _
    (⊤ : Submonoid (PresentedMonoid rels))
    (@oreSetSelf' _ rels h1 h) G₁ _
  ⟨⟨PresentedMonoid.lift_hom f (lift_eq_lift_of_rel f universal_h), rfl⟩,
  by simp only [map_mul, implies_true]⟩ (map_denom_into_units f universal_h) (fun _ => rfl)

theorem presented_fraction_group_to_group_unique {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂))
    (φ : pml h1 h →* G₁) :
    (∀ (r : α), φ (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ rels h1 h)
    (PresentedMonoid.of rels r)) = f r) → φ =
    presented_fraction_group_to_group f universal_h := by
  intro hr
  let _ := @oreSetSelf' _ rels h1 h
  apply OreLocalization.universalMulHom_unique
  intro pr
  induction' pr with fr
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  induction fr using FreeMonoid'.inductionOn'
  · simp
  rename_i head tail ih
  simp only [PresentedMonoid.mul_mk, map_mul]
  rw [ih]
  simp only [mul_left_inj]
  conv => rhs; erw [PresentedMonoid.lift_hom_mk]
  rw [← hr head]
  rfl

end Presented
