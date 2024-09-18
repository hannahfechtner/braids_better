import Mathlib.RingTheory.OreLocalization.Basic
import BraidProject.PresentedMonoid_mine
import Mathlib.Algebra.Group.Units.Equiv
open Classical

section Self

-- I believe this should be because of the instance
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Submonoid/Basic.html#Submonoid.instTop
-- but I can't seem to get it to work
/-- a monoid M, viewed as a submonoid of itself -/
def submonoid_self (M : Type*) [Monoid M] : Submonoid M :=
  ⟨⟨(setOf (fun _ => True)), fun a _ => a⟩, trivial⟩

/-- the property that for every pair of elements in a monoid, there is another pair of elements in
that monoid serving as their common right multiples -/
--def has_common_left_mul (M : Type*) [Monoid M] := ∀ a b : M, ∃ c d : M, c * a = d * b

class CommonLeftMulMonoid (M : Type*) extends Monoid M where
  has_common_left_mul : ∀ a b : M, ∃ c d : M, c * a = d * b
  -- cl₁ : M → M → M
  -- cl₂ : M → M → M
  -- cl_spec : ∀ a b : M, cl₁ a b * a = cl₂ a b * b

class CommonLeftMulCancelMonoid (M : Type*) extends CommonLeftMulMonoid M, CancelMonoid M

open CommonLeftMulMonoid
/-- the special case in which the entire monoid satisfies the Ore conditions,
and we localize by itself -/
noncomputable instance to_OreSet (M : Type*) [CommonLeftMulCancelMonoid M] :
    OreLocalization.OreSet (submonoid_self M) :=
  ⟨fun _ _ _ eq => Exists.intro (1 : ↑(submonoid_self M)) ( by rw [mul_right_cancel eq] ),
  (fun a b => (choose (Prod.exists'.mpr (has_common_left_mul a ↑b))).2),
  (fun a b => ⟨(choose (Prod.exists'.mpr (has_common_left_mul a ↑b))).1, trivial⟩),
  fun a b => @choose_spec (M × M) _ (Prod.exists'.mpr (has_common_left_mul a ↑b))⟩
--mul_left_cancel (congr (congrArg (fun x => Eq (_ * x)) (mul_one _)) (congrArg _ (mul_one _))).mpr eq
--choose_spec (Prod.exists'.mpr (cml _ _))
--I cannot figure out why I need to explicitly give it the to_OreSet instance, like why it won't
--find it. I even have to give it again in the definition of fraction_group_to_group

variable {M : Type*} [CommonLeftMulCancelMonoid M]
--variable (cml : has_common_left_mul M)
--variable [OreLocalization.OreSet (submonoid_self M)]

local notation "OreLocalizationSelf" =>  @OreLocalization M _ (submonoid_self M) _ M _

/-- when localizing by the entire monoid, the result is a group -/
noncomputable instance : Group OreLocalizationSelf where
  mul := OreLocalization.smul
  mul_assoc := OreLocalization.mul_assoc
  one := 1 /ₒ 1
  one_mul := OreLocalization.one_mul
  mul_one := OreLocalization.mul_one
  inv := OreLocalization.liftExpand (fun a b => b.val /ₒ ⟨a, trivial⟩)
    fun a b c d => by
      simp
      apply OreLocalization.oreDiv_eq_iff.mpr
      use 1, b
      simp
  mul_left_inv := OreLocalization.ind fun _ _ => OreLocalization.mul_inv _ _

/-- simplified universal property when localizing by the entire monoid -/
def fraction_group_to_group {G₁ : Type} [Group G₁] (f : M →* G₁) : OreLocalizationSelf →* G₁ :=
  OreLocalization.universalMulHom f
  ⟨⟨(fun (x : ↥(submonoid_self M)) => toUnits (f x.val)),
  by simp only [OneMemClass.coe_one, map_one]⟩, by simp only
  [Submonoid.coe_mul, map_mul, Subtype.forall, implies_true, forall_const]⟩
  (by intro s ; simp)

/-- uniqueness of the simplified universal property when localizing by the entire monoid -/
theorem fraction_group_to_group_unique {G₁ : Type} [Group G₁] (f : M →* G₁)
    (φ : OreLocalizationSelf →* G₁)
    (h : ∀ (r : M), φ (@OreLocalization.numeratorHom _ _ _ (to_OreSet M) r) = f r)
    : φ = (fraction_group_to_group f : OreLocalizationSelf →* G₁) :=
  OreLocalization.universalMulHom_unique f _ _ _ (fun pr => h pr)
  --see how every time I need that darn (to_OreSet M cml) ... maddening

end Self

section Presented

-- okay, now in the context of a presented monoid. this should look more like a presented group
--first we need to update variables
variable {α : Type} {rels : FreeMonoid' α → FreeMonoid' α → Prop}
local notation "P" => PresentedMonoid rels

-- here I've just put it in as a variable, which isn't a good long-run strategy,
-- but makes the code run look more sleek for now
variable [OreLocalization.OreSet (submonoid_self (PresentedMonoid rels))]

variable [Group (OreLocalization (submonoid_self (PresentedMonoid rels)) (PresentedMonoid rels))]
local notation "OreLocalizationSelf_Presented" =>  OreLocalization (submonoid_self P) P

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
  ↥(submonoid_self P) →* G₁ˣ :=
  ⟨⟨toUnits ∘ (PresentedMonoid.lift_hom f (lift_eq_lift_of_rel f universal_h)) ∘ (fun x => x.val),
    (Units.val_eq_one.mp rfl)⟩,
    (by
      simp only [Function.comp_apply, Submonoid.coe_mul, Subtype.forall]
      intro a _ b _
      simp only [map_mul] ) ⟩

/-- the universal property for the ore localization of a presented monoid by itself -/
def presented_fraction_group_to_group {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂)) :
    OreLocalizationSelf_Presented →* G₁ :=
  @OreLocalization.universalMulHom (P) _ (submonoid_self P) _ G₁ _
  ⟨⟨PresentedMonoid.lift_hom f (lift_eq_lift_of_rel f universal_h), rfl⟩,
  by simp only [map_mul, implies_true]⟩ (map_denom_into_units f universal_h) (fun _ => rfl)

theorem presented_fraction_group_to_group_unique {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂))
    (φ : OreLocalization (submonoid_self P) P →* G₁) :
    (∀ (r : α), φ (OreLocalization.numeratorHom (PresentedMonoid.of rels r)) = f r) → φ =
    presented_fraction_group_to_group f universal_h := by
  intro hr
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
