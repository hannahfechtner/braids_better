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

-- class CommonLeftMulMonoid (M : Type*) extends Monoid M where
--   cl₁ : M → M → M
--   cl₂ : M → M → M
--   cl_spec : ∀ a b : M, cl₂ a b * a = cl₁ a b * b

class CommonLeftMultipleMonoid (M : Type*) extends Monoid M where
  cl₁ : M → M → M
  cl₂ : M → M → M
  cl_spec : ∀ a b : M, cl₂ a b * a = cl₁ a b * b

class OreMonoid (M : Type*) extends CommonLeftMultipleMonoid M, CancelMonoid M


open OreMonoid
-- /-- the special case in which the entire monoid satisfies the Ore conditions,
-- and we localize by itself -/
-- instance to_OreSet (M : Type*) [CommonLeftMulCancelMonoid M] :
--     OreLocalization.OreSet (submonoid_self M) :=
--   ⟨fun _ _ _ eq => Exists.intro (1 : ↑(submonoid_self M)) ( by rw [mul_right_cancel eq] ),
--   fun a b => cl₁ a b, fun a b => ⟨(cl₂ a b), trivial⟩, fun a b => cl_spec a b⟩

--I cannot figure out why I need to explicitly give it the to_OreSet instance, like why it won't
--find it. I even have to give it again in the definition of fraction_group_to_group

variable {M : Type*} [OreMonoid M]
--variable (cml : has_common_left_mul M)
--variable [OreLocalization.OreSet (submonoid_self M)]

--local notation "OreLocalizationSelf" =>  @OreLocalization M _ (submonoid_self M) _ M _

instance oreSetSelf : OreLocalization.OreSet (submonoid_self M) where
  ore_right_cancel  := by
    intro r1 r2 s eq
    use 1
    simp only [OneMemClass.coe_one, one_mul]
    exact mul_right_cancel eq
  oreNum r s := CommonLeftMultipleMonoid.cl₁ r s
  oreDenom r s := ⟨CommonLeftMultipleMonoid.cl₂ r s, trivial⟩
  ore_eq := fun r s => CommonLeftMultipleMonoid.cl_spec _ _

/-- when localizing by the entire monoid, the result is a group -/
instance group_of_self : Group (@OreLocalization M _ (submonoid_self M) _ M _) where
  mul := fun a b => a * b --OreLocalization.smul
  mul_assoc := mul_assoc --OreLocalization.mul_assoc
  one := 1 /ₒ 1
  one_mul := one_mul --OreLocalization.one_mul
  mul_one := mul_one -- OreLocalization.mul_one
  inv := OreLocalization.liftExpand (fun a b => b.val /ₒ ⟨a, trivial⟩)
    fun a b c d => by
      apply OreLocalization.oreDiv_eq_iff.mpr
      use 1, b
      simp
  mul_left_inv := OreLocalization.ind fun _ _ => OreLocalization.mul_inv _ _

/-- simplified universal property when localizing by the entire monoid -/
def fraction_group_to_group {G₁ : Type} [Group G₁] (f : M →* G₁) :
    (@OreLocalization M _ (submonoid_self M) _ M _) →* G₁ :=
  OreLocalization.universalMulHom f
  ⟨⟨(fun (x : ↥(submonoid_self M)) => toUnits (f x.val)),
  by simp only [OneMemClass.coe_one, map_one]⟩, by simp only
  [Submonoid.coe_mul, map_mul, Subtype.forall, implies_true, forall_const]⟩
  (by intro s ; simp)

/-- uniqueness of the simplified universal property when localizing by the entire monoid -/
theorem fraction_group_to_group_unique {G₁ : Type} [Group G₁]
    (f : M →* G₁) (φ : (@OreLocalization M _ (submonoid_self M) _ M _) →* G₁)
    (h : ∀ (r : M), φ (@OreLocalization.numeratorHom _ _ _ _ r) = f r)
    : φ = (fraction_group_to_group f : (@OreLocalization M _ (submonoid_self M) _ M _) →* G₁) :=
  OreLocalization.universalMulHom_unique f _ _ _ (fun pr => h pr)

end Self

section Presented

-- okay, now in the context of a presented monoid. this should look more like a presented group
--first we need to update variables
variable {α : Type} {rels : FreeMonoid' α → FreeMonoid' α → Prop}
--local notation "P" => PresentedMonoid rels

-- here I've just put it in as a variable, which isn't a good long-run strategy,
-- but makes the code run look more sleek for now
--variable [CommonLeftMulCancelMonoid (PresentedMonoid rels)]

-- instance for_heavens_sake (cancel_left : ∀ (a b c : PresentedMonoid rels), a * b = a * c → b = c)
--   (cancel_right : ∀ (a b c : PresentedMonoid rels), a * b = c * b → a = c) :
--   CancelMonoid (PresentedMonoid rels) where
--   mul_left_cancel := cancel_left
--   mul_right_cancel := cancel_right
--   one_mul := one_mul
--   mul_one := mul_one

-- variable (cancel_left : ∀ (a b c : PresentedMonoid rels), a * b = a * c → b = c)
--   (cancel_right : ∀ (a b c : PresentedMonoid rels), a * b = c * b → a = c)

-- instance oy_gevalt (cancel_left : ∀ (a b c : PresentedMonoid rels), a * b = a * c → b = c)
--   (cancel_right : ∀ (a b c : PresentedMonoid rels), a * b = c * b → a = c)
--   (cl₁ : PresentedMonoid rels → PresentedMonoid rels → PresentedMonoid rels)
--   (cl₂ : PresentedMonoid rels → PresentedMonoid rels → PresentedMonoid rels)
--   (cl_spec : ∀ a b : PresentedMonoid rels, cl₂ a b * a = cl₁ a b * b) :
--   OreMonoid (PresentedMonoid rels) where
--   mul_left_cancel := cancel_left
--   mul_right_cancel := cancel_right
--   -- one_mul := one_mul
--   -- mul_one := mul_one
--   cl₁ := cl₁
--   cl₂ := cl₂
--   cl_spec := cl_spec

variable (cl₁ : PresentedMonoid rels → PresentedMonoid rels → PresentedMonoid rels)
  (cl₂ : PresentedMonoid rels → PresentedMonoid rels → PresentedMonoid rels)
  (cl_spec : ∀ a b : PresentedMonoid rels, cl₂ a b * a = cl₁ a b * b)
  (cancel_left : ∀ (a b c : PresentedMonoid rels), a * b = a * c → b = c)
  (cancel_right : ∀ (a b c : PresentedMonoid rels), a * b = c * b → a = c)

instance oreSetSelf' : OreLocalization.OreSet (submonoid_self (PresentedMonoid rels)) where
  ore_right_cancel  := by
    intro r1 r2 s eq
    use 1
    simp only [OneMemClass.coe_one, one_mul]
    let h2 :   LeftCancelSemigroup (PresentedMonoid rels) := ⟨cancel_left⟩
    let h4 :   LeftCancelMonoid (PresentedMonoid rels) := ⟨one_mul, mul_one, fun e b => b ^ e, by simp only [pow_zero,
      implies_true], fun n x => by simp [pow_succ]⟩
    let h0 : CancelMonoid (PresentedMonoid rels) := ⟨cancel_right⟩
    exact CancelMonoid.mul_right_cancel _ _ _ eq
  oreNum r s :=
    let h : CommonLeftMultipleMonoid (PresentedMonoid rels) := ⟨cl₁, cl₂, cl_spec⟩
    CommonLeftMultipleMonoid.cl₁ r s
  oreDenom r s :=
    let h : CommonLeftMultipleMonoid (PresentedMonoid rels) := ⟨cl₁, cl₂, cl_spec⟩
    ⟨CommonLeftMultipleMonoid.cl₂ r s, trivial⟩
  ore_eq :=
    let h : CommonLeftMultipleMonoid (PresentedMonoid rels) := ⟨cl₁, cl₂, cl_spec⟩
    (fun r s =>
      let H := CommonLeftMultipleMonoid.cl_spec r s
      by
      beta_reduce
      dsimp
      exact H)

/-- when localizing by the entire monoid, the result is a group -/
instance group_of_self' : Group (@OreLocalization ((PresentedMonoid rels)) _ (submonoid_self ((PresentedMonoid rels))) (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right) ((PresentedMonoid rels)) _) where
  mul := fun a b => a * b --OreLocalization.smul
  mul_assoc := mul_assoc --OreLocalization.mul_assoc
  one :=
    let _ := (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right)
    1 /ₒ 1
  one_mul := one_mul --OreLocalization.one_mul
  mul_one := mul_one -- OreLocalization.mul_one
  inv :=
    let _ := (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right)
    OreLocalization.liftExpand (fun a b => b.val /ₒ ⟨a, trivial⟩)
    fun a b c d => by
      apply OreLocalization.oreDiv_eq_iff.mpr
      use 1, b
      simp
  mul_left_inv :=
    let _ := (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right)
    OreLocalization.ind fun _ _ => OreLocalization.mul_inv _ _

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
  ↥(submonoid_self (PresentedMonoid rels)) →* G₁ˣ :=
  ⟨⟨toUnits ∘ (PresentedMonoid.lift_hom f (lift_eq_lift_of_rel f universal_h)) ∘ (fun x => x.val),
    (Units.val_eq_one.mp rfl)⟩,
    (by
      simp only [Function.comp_apply, Submonoid.coe_mul, Subtype.forall]
      intro a _ b _
      simp only [map_mul] ) ⟩

abbrev pml := @OreLocalization (PresentedMonoid rels) _ (submonoid_self (PresentedMonoid rels))
  (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right) (PresentedMonoid rels) _


#check pml
-- instance get_oreset [h : OreMonoid (PresentedMonoid rels)] :
--     @OreLocalization.OreSet (PresentedMonoid rels) _ (submonoid_self (PresentedMonoid rels)) := @oreSetSelf (PresentedMonoid rels) h
-- theorem pml_is_group [OreMonoid (PresentedMonoid rels)] : Group (@OreLocalization (PresentedMonoid rels) _ (submonoid_self (PresentedMonoid rels)) _ (PresentedMonoid rels) _)

/-- the universal property for the ore localization of a presented monoid by itself -/
def presented_fraction_group_to_group {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂)) :
    (pml cl₁ cl₂ cl_spec cancel_left cancel_right) →* G₁ :=
  @OreLocalization.universalMulHom ((PresentedMonoid rels)) _ (submonoid_self (PresentedMonoid rels))
    (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right) G₁ _
  ⟨⟨PresentedMonoid.lift_hom f (lift_eq_lift_of_rel f universal_h), rfl⟩,
  by simp only [map_mul, implies_true]⟩ (map_denom_into_units f universal_h) (fun _ => rfl)

theorem presented_fraction_group_to_group_unique {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂))
    (φ : pml cl₁ cl₂ cl_spec cancel_left cancel_right →* G₁) :
    (∀ (r : α), φ (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right)
    (PresentedMonoid.of rels r)) = f r) → φ =
    presented_fraction_group_to_group _ _ _ _ _ f universal_h := by
  intro hr
  let h := @oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right
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
