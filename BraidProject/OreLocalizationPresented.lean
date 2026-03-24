import BraidProject.PresentedMonoid_mine
import BraidProject.OreLocalizationSelf
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup
import BraidProject.Additions.PresentedGroup
import BraidProject.Additions.FreeMonoid
import BraidProject.Additions.List

theorem lift_eq_lift_lift_of {G₁ : Type} [Group G₁] (f : α → G₁) :
    FreeMonoid.lift f = (FreeGroup.lift f).comp (FreeMonoid.lift FreeGroup.of) := by
  rw [← (FreeMonoid.lift_comp FreeGroup.of (FreeGroup.lift f))]
  aesop

theorem lift_eq_lift_lift_of_apply {G₁ : Type} [Group G₁] (f : α → G₁) (a : FreeMonoid α) :
    FreeMonoid.lift f a = (FreeGroup.lift f) (FreeMonoid.lift FreeGroup.of a) := by
  simpa using congrArg (fun φ : FreeMonoid α →* G₁ => φ a)
    (lift_eq_lift_lift_of (f := f))

variable {α : Type} (rels : FreeMonoid α → FreeMonoid α → Prop)

open PresentedGroup

private theorem lift_eq_lift_of_rel {G₁ : Type} [Group G₁] (f : α → G₁)
    (h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂))
    (a b : FreeMonoid α) (hr : PresentedMonoid.rel rels a b) :
    (FreeMonoid.lift f) a = (FreeMonoid.lift f) b :=
  ConGen.Rel.rec (fun x y rxy ↦ h x y rxy) (fun _ ↦ rfl) (fun _ ryx ↦ ryx.symm)
  (fun _ _ rab rbc ↦ rab.trans rbc) (fun  _ _ ih1 ih2 ↦ by rw [map_mul, map_mul, ih1, ih2]) hr

variable [h1 : IsCommonLeftMultipleMul (PresentedMonoid rels)] [h2 : IsRightCancelMul (PresentedMonoid rels)]

open IsCommonLeftMultipleMul

abbrev pml := OreLocalization (⊤ : Submonoid (PresentedMonoid rels)) (PresentedMonoid rels)

-- /-- a homomorphism from elements of a presented monoid viewed as a submonoid of itself
-- (which will become denominators) into units of the group -/
-- private def map_denom_into_units {G₁ : Type} [Group G₁] (f : α → G₁)
--   (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂)) :
--   ↥(⊤ : Submonoid (PresentedMonoid rels)) →* G₁ˣ :=
--   ⟨⟨toUnits ∘ (PresentedMonoid.lift_hom f (lift_eq_lift_of_rel rels f universal_h)) ∘ (fun x => x.val),
--     (Units.val_eq_one.mp rfl)⟩,
--     (by
--       simp only [Function.comp_apply, Submonoid.coe_mul, Subtype.forall]
--       intro a _ b _
--       grind) ⟩

/-- the universal property for the ore localization of a presented monoid by itself -/
-- noncomputable def presented_fraction_group_to_group' {G₁ : Type} [Group G₁] (f : α → G₁)
--     (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂)) :
--     (pml rels) →* G₁ :=
--   OreLocalization.universalMulHom
--   ⟨⟨PresentedMonoid.lift_hom f (lift_eq_lift_of_rel rels f universal_h), rfl⟩,
--   by intro x y; simp only; erw [(PresentedMonoid.lift_hom f
--   (lift_eq_lift_of_rel rels f universal_h)).map_mul x y]⟩ (map_denom_into_units rels f universal_h)
--   (fun _ => rfl)

noncomputable def presented_fraction_group_to_group {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂)) :
    (pml rels) →* G₁ := by
    apply Self.universalMonoidHom
    apply PresentedMonoid.lift_hom f (lift_eq_lift_of_rel rels f universal_h)

theorem presented_fraction_group_to_group_unique {G₁ : Type} [Group G₁] (f : α → G₁)
    (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂))
    (φ : pml rels →* G₁) :
    (∀ (r : α), φ (OreLocalization.numeratorHom
    (PresentedMonoid.of rels r)) = f r) → φ =
    presented_fraction_group_to_group rels f universal_h := by
  intro hr
  apply Self.universalMonoidHom_unique
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  intro pr
  induction pr with | h fr
  induction fr using FreeMonoid.inductionOn' with
  | one => grind [PresentedMonoid.one_def]
  | mul_of head tail ih =>
    simp only [PresentedMonoid.mul_mk]
    erw [(PresentedMonoid.lift_hom f (lift_eq_lift_of_rel rels f universal_h)).map_mul, ← ih]
    rw [Function.comp_apply, ← OreLocalization.mul_div_one, φ.map_mul, Function.comp_apply,
      mul_left_inj]
    conv => rhs; erw [PresentedMonoid.lift_hom_mk]
    rw [← hr head]
    rfl

-- theorem presented_fraction_group_to_group_unique' {G₁ : Type} [Group G₁] (f : α → G₁)
--     (universal_h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂))
--     (φ : pml rels →* G₁) :
--     (∀ (r : α), φ (OreLocalization.numeratorHom
--     (PresentedMonoid.of rels r)) = f r) → φ =
--     presented_fraction_group_to_group' rels f universal_h := by
--   intro hr
--   apply OreLocalization.universalMulHom_unique
--   intro pr
--   induction pr with | h fr
--   simp only [MonoidHom.coe_mk, OneHom.coe_mk]
--   induction fr using FreeMonoid.inductionOn'
--   · grind [PresentedMonoid.one_def]
--   rename_i head tail ih
--   simp only [PresentedMonoid.mul_mk]
--   erw [(PresentedMonoid.lift_hom f (lift_eq_lift_of_rel rels f universal_h)).map_mul]
--   rw [← ih, ← OreLocalization.mul_div_one]
--   rw [φ.map_mul]
--   simp [mul_left_inj]
--   conv => rhs; erw [PresentedMonoid.lift_hom_mk]
--   rw [← hr head]
--   rfl

-- where do I put this
theorem rels_pg_iff_rels_pml {G₁ : Type} [Group G₁]
    {rels : FreeMonoid α → FreeMonoid α → Prop} (f : α → G₁) :
    (∀ r ∈ (free_group_set_of_function rels), ((FreeGroup.lift f) r ) = 1) ↔
    (∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂)) := by
  constructor
  · intro h r₁ r₂ _
    have : FreeMonoid.lift (FreeGroup.of) r₁ * (FreeMonoid.lift (FreeGroup.of) r₂)⁻¹ ∈
        free_group_set_of_function rels := by
      use ⟨r₁, r₂⟩
      simpa only [Set.mem_setOf_eq, and_true]
    specialize h (FreeMonoid.lift (FreeGroup.of) r₁ * (FreeMonoid.lift (FreeGroup.of) r₂)⁻¹) this
    rw [map_mul, map_inv, ← lift_eq_lift_lift_of_apply, ← lift_eq_lift_lift_of_apply,
      ← mul_left_inj ((FreeMonoid.lift f) r₂), inv_mul_cancel_right, one_mul] at h
    exact h
  intro h r hr
  rcases hr with ⟨⟨a, b⟩, h1, rfl⟩
  simp only [map_mul, map_inv]
  rw [← lift_eq_lift_lift_of_apply, ← lift_eq_lift_lift_of_apply, h a b h1]
  exact mul_inv_cancel ((FreeMonoid.lift f) b)

omit h1 h2 in
theorem presented_identity_works (r : FreeGroup α) (h : r ∈ free_group_set_of_function rels) :
    FreeGroup.lift PresentedGroup.of r =
    (1 : PresentedGroup (free_group_set_of_function rels)) := by
  rw [← PresentedGroup.mk_eq_lift_of]
  exact one_of_mem h

noncomputable def pml_to_presented_group : pml rels →*
    PresentedGroup (free_group_set_of_function rels) :=
  presented_fraction_group_to_group rels (PresentedGroup.of)
  ((rels_pg_iff_rels_pml PresentedGroup.of).mp (presented_identity_works rels))

@[simp]
theorem pml_to_presented_group_apply_of (a : α) : pml_to_presented_group rels
    (OreLocalization.numeratorHom (PresentedMonoid.of rels a)) =
    (PresentedGroup.of a : PresentedGroup (free_group_set_of_function rels)) :=
  rfl

theorem pml_to_presented_group_apply_mk (a : FreeMonoid α) : pml_to_presented_group rels
    (OreLocalization.numeratorHom (PresentedMonoid.mk rels a)) =
    (PresentedGroup.mk (free_group_set_of_function rels) (FreeGroup.mk (List.map (fun x => (x, true)) a)) :
    PresentedGroup (free_group_set_of_function rels)) := by
  induction a using FreeMonoid.inductionOn'
  · rfl
  rename_i head tail ih
  rw [PresentedMonoid.mul_mk, map_mul, map_mul, ih]
  change _ = (PresentedGroup.mk _) (FreeGroup.mk ([(head, true)]) *
      FreeGroup.mk (List.map (fun x ↦ (x, true)) tail))
  rw [map_mul, mul_left_inj]
  rfl

open PresentedMonoid in
private theorem fraction_identity_works (r : FreeGroup α)
    (r_in : r ∈ free_group_set_of_function rels) :
    (FreeGroup.lift fun x => OreLocalization.numeratorHom (PresentedMonoid.of rels x)) r =
    (1 : pml rels) := by
  rcases r_in with ⟨⟨a, b⟩, h1, rfl⟩
  rw [Set.mem_setOf_eq] at h1
  rw [map_mul, map_inv, ← lift_eq_lift_lift_of_apply, ← lift_eq_lift_lift_of_apply, lift_of_eq_mk_of_mulHom,
    lift_of_eq_mk_of_mulHom, PresentedMonoid.sound (PresentedMonoid.rel_alone h1)]
  exact mul_inv_cancel _

noncomputable def presented_group_to_pml : PresentedGroup (free_group_set_of_function rels) →* (pml rels) :=
  PresentedGroup.toGroup (fraction_identity_works rels)

@[simp]
theorem presented_group_to_pml_apply_of (a : α) : presented_group_to_pml rels (PresentedGroup.of a) =
    (OreLocalization.numeratorHom (PresentedMonoid.of rels a)) := by
  unfold presented_group_to_pml
  simp only [PresentedGroup.toGroup.of]

-- the following two should be inlined into presentedMonoidLocalizationEquivPresentedGroup
-- but i'm leaving them separate for now to improve readbility
theorem comp_pg_pml_pml_pg_eq_id : MonoidHom.comp (presented_group_to_pml rels)
    (pml_to_presented_group rels) = MonoidHom.id _ := by
  have unique_map_to_self := presented_fraction_group_to_group_unique rels
    (fun a => OreLocalization.numeratorHom (PresentedMonoid.of rels a))
    ((rels_pg_iff_rels_pml _).mp <| (fraction_identity_works rels))
  have Sh2 := unique_map_to_self (MonoidHom.comp (presented_group_to_pml rels)
    (pml_to_presented_group rels)) (fun x => by simp only [MonoidHom.coe_comp,
      Function.comp_apply, pml_to_presented_group_apply_of, presented_group_to_pml_apply_of])
  rw [Sh2]
  exact (unique_map_to_self ⟨⟨id, rfl⟩, fun _ _ => rfl⟩
    (fun r => by simp only [MonoidHom.coe_mk, OneHom.coe_mk, id_eq])).symm

theorem comp_pml_pg_pg_pml_eq_id : MonoidHom.comp (pml_to_presented_group rels)
    (presented_group_to_pml rels) = MonoidHom.id _ := by
  ext x
  apply PresentedGroup.toGroup.unique (presented_identity_works rels)
  intro y
  simp only [MonoidHom.coe_comp, Function.comp_apply, presented_group_to_pml_apply_of,
    pml_to_presented_group_apply_of]

theorem comp_eq_id_bijective (h1 : a ∘ b = id) :
  Function.Surjective a := by
  exact Function.RightInverse.surjective (congrFun h1)

--will go in the mul hom file
theorem comp_eq_of_hom_comp_eq_mul {α β γ : Type*} [Mul α] [Mul β] [Mul γ] {ab : MulHom α β}
    {bc : MulHom β γ} {ac : MulHom α γ} (h : MulHom.comp bc ab = ac) :
    bc.toFun ∘ ab.toFun = ac.toFun:=
  funext fun x ↦ ((congrArg (fun y ↦ (bc ∘ ab) x = y x) h.symm)).mpr rfl

--will go in the monoid hom file - it is true more generally, but it's convenient to have the MonoidHom form here
theorem comp_eq_of_hom_comp_eq {α β γ : Type*} [Monoid α] [Monoid β] [Monoid γ] {ab : MonoidHom α β}
    {bc : MonoidHom β γ} {ac : MonoidHom α γ} (h : MonoidHom.comp bc ab = ac) :
    bc.toFun ∘ ab.toFun = ac.toFun:=
  funext fun x ↦ ((congrArg (fun y ↦ (bc ∘ ab) x = y x) h.symm)).mpr rfl

/-- the localization of a presented monoid is isomorphic to the presented group over the same
relations-/
noncomputable def presentedMonoidLocalizationEquivPresentedGroup : pml rels ≃* PresentedGroup (free_group_set_of_function rels) :=
  ⟨⟨pml_to_presented_group rels, presented_group_to_pml rels,
  Function.leftInverse_iff_comp.mpr <| comp_eq_of_hom_comp_eq (comp_pg_pml_pml_pg_eq_id rels),
  Function.rightInverse_iff_comp.mpr <| comp_eq_of_hom_comp_eq (comp_pml_pg_pg_pml_eq_id rels)⟩,
  map_mul (pml_to_presented_group rels)⟩

theorem  pml_to_presented_group_injective : Function.Injective (pml_to_presented_group rels) :=
  Function.LeftInverse.injective <| congrFun (comp_eq_of_hom_comp_eq ((comp_pg_pml_pml_pg_eq_id rels)))

-- I do not yet know if i want the list version or the freemonoid version
theorem pg_to_pm_fg_mk [IsLeftCancelMul (PresentedMonoid rels)]
  (h : PresentedGroup.mk (free_group_set_of_function rels) (FreeGroup.mk e) =
  PresentedGroup.mk (free_group_set_of_function rels) (FreeGroup.mk d))
  (hd : ∀ x ∈ d, x.2 = true) (he : ∀ x ∈ e, x.2 = true) :
  PresentedMonoid.mk rels (List.map (fun x ↦ x.1) e) =
  PresentedMonoid.mk rels (List.map (fun x ↦ x.1) d) := by
  rw [← List.reconstruct_from_projection hd, ← List.reconstruct_from_projection he,
      ← pml_to_presented_group_apply_mk, ← pml_to_presented_group_apply_mk] at h
  exact numeratorHom_injective_of_cancellative _ _ (pml_to_presented_group_injective rels h)
