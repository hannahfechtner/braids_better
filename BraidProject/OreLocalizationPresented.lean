import BraidProject.PresentedMonoid_mine
import BraidProject.OreLocalizationSelf
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup


variable {α : Type} [Monoid α] {rels : FreeMonoid α → FreeMonoid α → Prop}

-- this should have a better name and be in a namespace
def pm_rels_to_pg_rels (rels : FreeMonoid α → FreeMonoid α → Prop) : Set (FreeGroup α) :=
  {FreeMonoid.lift (FreeGroup.of) x.1 * (FreeMonoid.lift (FreeGroup.of) x.2)⁻¹ |
  x ∈ setOf (fun (a : FreeMonoid α × FreeMonoid α) => rels a.1 a.2)} ∪ {1}

variable {α : Type} {rels : FreeMonoid α → FreeMonoid α → Prop}
-- variable [OreLocalization.OreSet (submonoid_self (PresentedMonoid rels))]
-- local notation "P" => PresentedMonoid rels
-- local notation "pml" =>  OreLocalization (submonoid_self P) P
-- variable [Group pml]

theorem presented_identity_works : ∀ r ∈ pm_rels_to_pg_rels rels, (FreeGroup.lift PresentedGroup.of r :
    PresentedGroup (pm_rels_to_pg_rels rels)) = 1 := by
  intro r h
  -- ought I add this? to the PresentedGroup API
  rw [← (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure h)]
  apply @FreeGroup.induction_on α _ r
  · rfl
  · exact fun _ => rfl
  · exact fun _ _ => rfl
  intro _ _ hx hy
  rw [map_mul, hx, hy]
  rfl

-- this should go somewhere else : either free monoid or free group
theorem lift_eq_lift_lift_of {G₁ : Type} {a : FreeMonoid α} [Group G₁] (f : α → G₁) :
    FreeMonoid.lift f a = (FreeGroup.lift f) (FreeMonoid.lift (FreeGroup.of) a) := by
  induction' a using FreeMonoid.inductionOn'
  · rfl
  rename_i ih
  simp only [map_mul, FreeMonoid.lift_eval_of, ih, FreeGroup.lift.of]

theorem rels_pg_iff_rels_pml {G₁ : Type} [Group G₁]
    {rels : FreeMonoid α → FreeMonoid α → Prop}
    (f : α → G₁) :
    (∀ r ∈ (pm_rels_to_pg_rels rels), ((FreeGroup.lift f) r ) = 1) ↔ (∀ r₁ r₂, rels r₁ r₂ →
    (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂)) := by
  constructor
  · intro one_version r1 r2 relsy
    have anty : FreeMonoid.lift (FreeGroup.of) r1 * (FreeMonoid.lift (FreeGroup.of) r2)⁻¹ ∈
        pm_rels_to_pg_rels rels := by
      left
      apply Prod.exists.mpr
      simp only [Set.mem_setOf_eq]
      use r1, r2
    specialize one_version ((FreeMonoid.lift (FreeGroup.of) r1) *
      (FreeMonoid.lift (FreeGroup.of) r2)⁻¹) anty
    rw [map_mul, map_inv, ← lift_eq_lift_lift_of, ← lift_eq_lift_lift_of, ← mul_left_inj ((FreeMonoid.lift f) r2),
      inv_mul_cancel_right, one_mul] at one_version
    exact one_version
  intro double_version r r_in
  rcases r_in with ⟨a, b, one, two⟩
  simp only [Set.mem_setOf_eq] at b
  simp only [map_mul, map_inv]
  rw [← lift_eq_lift_lift_of, ← lift_eq_lift_lift_of, double_version a.1 a.2 b]
  exact mul_inv_cancel ((FreeMonoid.lift f) a.2)
  rename_i h
  simp at h
  rw [h]
  rfl

variable {h : IsRightCancelMul (PresentedMonoid rels)} {h1 : IsCommonLeftMultipleMul (PresentedMonoid rels)}

def pml_to_presented_group : pml h1 h →*
    PresentedGroup (pm_rels_to_pg_rels rels) :=
  presented_fraction_group_to_group (PresentedGroup.of)
  ((rels_pg_iff_rels_pml PresentedGroup.of).mp presented_identity_works)

--@OreLocalization (PresentedMonoid rels) _ (⊤ : Submonoid (PresentedMonoid rels))
--  (@oreSetSelf' _ rels h1 h) (PresentedMonoid rels) _
theorem pml_to_presented_group_to_mk
    (a : α):
    @pml_to_presented_group _ _ h h1 (@OreLocalization.oreDiv _ _ _ ((@oreSetSelf' _ rels h1 h)) _ _ (PresentedMonoid.of rels a) (1 : (⊤ : Submonoid (PresentedMonoid rels)))) =
    (PresentedGroup.of a : PresentedGroup (pm_rels_to_pg_rels rels)) := by rfl
  -- unfold pml_to_presented_group
  -- unfold presented_fraction_group_to_group
  -- rw [@OreLocalization.universalMulHom_apply]
  -- simp only [map_one, inv_one, Units.val_one, MonoidHom.coe_mk, OneHom.coe_mk, one_mul]
  -- rfl

@[simp]
theorem pml_to_presented_group_apply_of (a : α) : pml_to_presented_group
    (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ rels h1 h)
    (PresentedMonoid.of rels a)) = (PresentedGroup.of a : PresentedGroup (pm_rels_to_pg_rels rels)) :=
  rfl

theorem lift_of_eq_mk_of_mulHom {β : Type} [Monoid β] (r : FreeMonoid α)
    (f : PresentedMonoid rels →* β) :
    (FreeMonoid.lift fun x => f (PresentedMonoid.of rels x)) r =
    (f (PresentedMonoid.mk rels r)) := by
  induction' r using FreeMonoid.inductionOn' with _ _ ih
  · exact f.map_one.symm
  rw [map_mul, ih, FreeMonoid.lift_eval_of, PresentedMonoid.mul_mk, map_mul]
  rfl


#check lift_of_eq_mk_of_mulHom
#check OreLocalization.numeratorHom
--(FreeMonoid.lift fun x ↦ f (PresentedMonoid.of rels x)) r = f (PresentedMonoid.mk rels r)
--set_option pp.all true in
private theorem fraction_identity_works
    : ∀ r ∈ pm_rels_to_pg_rels rels, ((@FreeGroup.lift _ _
    (group_of_self')
    (fun x => @OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ rels h1 h) (PresentedMonoid.of rels x))) r :
    @OreLocalization _ _ _ (@oreSetSelf' _ rels h1 h)
    (PresentedMonoid rels) _) = 1 := by
  intro r r_in
  rcases r_in with ⟨a, b, one, two⟩
  simp only [Set.mem_setOf_eq] at b
  rw [map_mul, map_inv, ← lift_eq_lift_lift_of, ← lift_eq_lift_lift_of]
  have H := @lift_of_eq_mk_of_mulHom α rels _ _ a.1 ((@OreLocalization.numeratorHom _ _ ⊤
    (@oreSetSelf' _ rels h1 h)))
  have H1 : (FreeMonoid.lift fun x ↦ @OreLocalization.numeratorHom _ _ ⊤ (@oreSetSelf' _ rels h1 h) (PresentedMonoid.of rels x)) a.1 =
    ((FreeMonoid.lift fun x ↦ @OreLocalization.numeratorHom _ _ ⊤ (@oreSetSelf' _ rels h1 h) (PresentedMonoid.of rels x)) a.2) := by sorry



  sorry
  rename_i h2
  simp at h2
  rw [h2]
  change (FreeGroup.lift fun x ↦ (@OreLocalization.numeratorHom _ _ _ (@oreSetSelf' _ rels h1 h) (PresentedMonoid.of rels x))) (FreeGroup.mk []) = 1
  simp only [FreeGroup.lift.mk, List.map_nil, List.prod_nil]
  sorry

  -- lift_of_eq_mk_of_mulHom a.1,
    --lift_of_eq_mk_of_mulHom a.2, PresentedMonoid.sound (PresentedMonoid.rel_alone b), mul_right_inv]

-- private def presented_group_to_pml : PresentedGroup (pm_rels_to_pg_rels rels) →* (pml h1 h) :=
--   --let _ := @group_of_self'
--   by convert PresentedGroup.toGroup fraction_identity_works

-- @[simp]
-- private theorem presented_group_to_pml_apply_of (a : α) : presented_group_to_pml
--     (PresentedGroup.of a : PresentedGroup (pm_rels_to_pg_rels rels)) =
--     (@OreLocalization.numeratorHom _ _ _
--     (@oreSetSelf' _ rels h1 h)
--     (PresentedMonoid.of rels a)) := by
--   unfold presented_group_to_pml
--   simp only [PresentedGroup.toGroup.of]

-- -- the following two should be inlined into presentedMonoidLocalizationEquivPresentedGroup
-- -- but i'm leaving them separate for now to improve readbility
-- private theorem comp_pg_pml_pml_pg_eq_id : MonoidHom.comp presented_group_to_pml
--     (@pml_to_presented_group α rels h h1) = ⟨⟨id, rfl⟩, fun _ _ => rfl⟩ := by
--   let _ := @oreSetSelf' _ rels h1 h
--   have unique_map_to_self := @presented_fraction_group_to_group_unique α rels h1 h _ _
--     (fun a => @OreLocalization.numeratorHom _ _ _ _ (PresentedMonoid.of rels a))
--     ((rels_pg_iff_rels_pml _).mp <| fraction_identity_works)
--   have Sh2 := unique_map_to_self (MonoidHom.comp presented_group_to_pml
--     (@pml_to_presented_group α rels h h1)) (fun x => by simp only [MonoidHom.coe_comp,
--       Function.comp_apply, pml_to_presented_group_apply_of, presented_group_to_pml_apply_of])
--   exact Sh2.trans (unique_map_to_self ⟨⟨id, rfl⟩, fun _ _ => rfl⟩
--     (fun r => by simp only [MonoidHom.coe_mk, OneHom.coe_mk, id_eq])).symm

-- private theorem comp_pml_pg_pg_pml_eq_id : MonoidHom.comp pml_to_presented_group
--     (@presented_group_to_pml α rels h h1) = ⟨⟨id, rfl⟩, fun _ _ => rfl⟩ := by
--   apply PresentedGroup.ext
--   intro x
--   apply PresentedGroup.toGroup.unique presented_identity_works
--   intro y
--   simp only [MonoidHom.coe_comp, Function.comp_apply, presented_group_to_pml_apply_of,
--     pml_to_presented_group_apply_of]

-- --will go in the monoid hom file - it is true more generally, but it's convenient to have the MulHom form here
-- theorem comp_eq_of_hom_comp_eq {α β γ : Type*} [Monoid α] [Monoid β] [Monoid γ] {ab : MonoidHom α β}
--     {bc : MonoidHom β γ} {ac : MonoidHom α γ} (h : MonoidHom.comp bc ab = ac) :
--     bc.toFun ∘ ab.toFun = ac.toFun:=
--   funext fun x ↦ ((congrArg (fun y ↦ (bc ∘ ab) x = y x) h.symm)).mpr rfl

-- /-- the localization of a presented monoid is isomorphic to the presented group over the same
-- relations-/
-- def presentedMonoidLocalizationEquivPresentedGroup : pml h1 h ≃* PresentedGroup (pm_rels_to_pg_rels rels) :=
--   ⟨⟨pml_to_presented_group, presented_group_to_pml,
--   Function.leftInverse_iff_comp.mpr <| comp_eq_of_hom_comp_eq comp_pg_pml_pml_pg_eq_id,
--   Function.rightInverse_iff_comp.mpr <| comp_eq_of_hom_comp_eq comp_pml_pg_pg_pml_eq_id⟩,
--   map_mul pml_to_presented_group⟩
