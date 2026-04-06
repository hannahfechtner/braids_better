import Mathlib.RingTheory.OreLocalization.Basic
import BraidProject.PresentedMonoid_mine
import Mathlib.Algebra.Group.Units.Equiv
import BraidProject.Additions.OreLocalization
import BraidProject.Additions.Mixins

namespace OreLocalization
namespace Self

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

local notation "OreLocalizationSelf" => OreLocalization (⊤ : Submonoid M) M

/-- when localizing by the entire monoid, the result is a group -/
noncomputable instance : Group OreLocalizationSelf where
  inv := OreLocalization.liftExpand (fun a b => b.val /ₒ ⟨a, trivial⟩)
    fun a b c d => by
      apply OreLocalization.oreDiv_eq_iff.mpr
      use 1, b
      simp
  inv_mul_cancel := OreLocalization.ind fun _ _ => OreLocalization.mul_inv _ _

/-- simplified universal property when localizing by the entire monoid -/
noncomputable def universalMonoidHom {G₁ : Type} [Group G₁] (f : M →* G₁) :
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
