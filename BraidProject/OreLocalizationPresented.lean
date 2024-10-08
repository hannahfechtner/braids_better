import BraidProject.PresentedMonoid_mine
import BraidProject.OreLocalizationSelf
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup


variable {α : Type} [Monoid α] {rels : FreeMonoid' α → FreeMonoid' α → Prop}

-- this should have a better name and be in a namespace
def convert_rels (rels : FreeMonoid' α → FreeMonoid' α → Prop) : Set (FreeGroup α) :=
  {FreeMonoid'.lift (FreeGroup.of) x.1 * (FreeMonoid'.lift (FreeGroup.of) x.2)⁻¹ |
  x ∈ setOf (fun (a : FreeMonoid' α × FreeMonoid' α) => rels a.1 a.2)}

variable {α : Type} {rels : FreeMonoid' α → FreeMonoid' α → Prop}
-- variable [OreLocalization.OreSet (submonoid_self (PresentedMonoid rels))]
-- local notation "P" => PresentedMonoid rels
-- local notation "pml" =>  OreLocalization (submonoid_self P) P
-- variable [Group pml]

theorem presented_identity_works : ∀ r ∈ convert_rels rels, (FreeGroup.lift PresentedGroup.of r :
    PresentedGroup (convert_rels rels)) = 1 := by
  intro r h
  -- ought I add this? to the PresentedGroup API
  rw [← (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure h)]
  apply @FreeGroup.induction_on α _ r
  · rfl
  · exact fun x => rfl
  · exact fun x _ => rfl
  intro _ _ hx hy
  rw [map_mul, hx, hy]
  rfl

-- this should go somewhere else : either free monoid or free group
theorem lift_eq_lift_lift_of {G₁ : Type} {a : FreeMonoid' α} [Group G₁] (f : α → G₁) :
    FreeMonoid'.lift f a = (FreeGroup.lift f) (FreeMonoid'.lift (FreeGroup.of) a) := by
  induction' a using FreeMonoid'.inductionOn'
  · rfl
  rename_i ih
  simp only [map_mul, FreeMonoid'.lift_eval_of, ih, FreeGroup.lift.of]

theorem rels_pg_iff_rels_pml {G₁ : Type} [Group G₁]
    {rels : FreeMonoid' α → FreeMonoid' α → Prop}
    (f : α → G₁) :
    (∀ r ∈ (convert_rels rels), ((FreeGroup.lift f) r ) = 1) ↔ (∀ r₁ r₂, rels r₁ r₂ →
    (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂)) := by
  constructor
  · intro one_version r1 r2 relsy
    have anty : FreeMonoid'.lift (FreeGroup.of) r1 * (FreeMonoid'.lift (FreeGroup.of) r2)⁻¹ ∈
        convert_rels rels := by
      apply Prod.exists.mpr
      simp only [Set.mem_setOf_eq]
      use r1, r2
    specialize one_version ((FreeMonoid'.lift (FreeGroup.of) r1) *
      (FreeMonoid'.lift (FreeGroup.of) r2)⁻¹) anty
    rw [map_mul, map_inv, ← lift_eq_lift_lift_of, ← lift_eq_lift_lift_of, ← mul_left_inj ((FreeMonoid'.lift f) r2),
      inv_mul_cancel_right, one_mul] at one_version
    exact one_version
  intro double_version r r_in
  rcases r_in with ⟨a, b, one, two⟩
  simp only [Set.mem_setOf_eq] at b
  simp only [map_mul, map_inv]
  rw [← lift_eq_lift_lift_of, ← lift_eq_lift_lift_of, double_version a.1 a.2 b, mul_right_inv]

variable (cl₁ : PresentedMonoid rels → PresentedMonoid rels → PresentedMonoid rels)
  (cl₂ : PresentedMonoid rels → PresentedMonoid rels → PresentedMonoid rels)
  (cl_spec : ∀ a b : PresentedMonoid rels, cl₂ a b * a = cl₁ a b * b)
  (cancel_left : ∀ (a b c : PresentedMonoid rels), a * b = a * c → b = c)
  (cancel_right : ∀ (a b c : PresentedMonoid rels), a * b = c * b → a = c)

private def pml_to_presented_group : pml cl₁ cl₂ cl_spec cancel_left cancel_right →*
    PresentedGroup (convert_rels rels) :=
  presented_fraction_group_to_group cl₁ cl₂ cl_spec cancel_left cancel_right (PresentedGroup.of)
  ((rels_pg_iff_rels_pml PresentedGroup.of).mp presented_identity_works)

@[simp]
private theorem pml_to_presented_group_apply_of (a : α) :
    pml_to_presented_group cl₁ cl₂ cl_spec cancel_left cancel_right
    (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right)
    (PresentedMonoid.of rels a)) = (PresentedGroup.of a : PresentedGroup (convert_rels rels)) :=
  rfl

theorem lift_of_eq_mk_of_mulHom {β : Type} [Monoid β] (r : FreeMonoid' α)
    (f : PresentedMonoid rels →* β) :
    (FreeMonoid'.lift fun x => f (PresentedMonoid.of rels x)) r =
    (f (PresentedMonoid.mk rels r)) := by
  induction' r using FreeMonoid'.inductionOn' with _ _ ih
  · exact f.map_one.symm
  rw [map_mul, ih, FreeMonoid'.lift_eval_of, PresentedMonoid.mul_mk, map_mul]
  rfl

private theorem fraction_identity_works
    : ∀ r ∈ convert_rels rels, ((@FreeGroup.lift _ _
    (group_of_self' cl₁ cl₂ cl_spec cancel_left cancel_right)
    (fun x => @OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right) (PresentedMonoid.of rels x))) r :
    @OreLocalization _ _ _ (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right)
    (PresentedMonoid rels) _) = 1 := by
  intro r r_in
  rcases r_in with ⟨a, b, one, two⟩
  simp only [Set.mem_setOf_eq] at b
  rw [map_mul, map_inv, ← lift_eq_lift_lift_of, ← lift_eq_lift_lift_of, lift_of_eq_mk_of_mulHom a.1,
    lift_of_eq_mk_of_mulHom a.2, PresentedMonoid.sound (PresentedMonoid.rel_alone b), mul_right_inv]

private def presented_group_to_pml : PresentedGroup (convert_rels rels) →* (
      pml cl₁ cl₂ cl_spec cancel_left cancel_right) :=
  let _ := group_of_self' cl₁ cl₂ cl_spec cancel_left cancel_right
  PresentedGroup.toGroup (fraction_identity_works cl₁ cl₂ cl_spec cancel_left cancel_right)

@[simp]
private theorem presented_group_to_pml_apply_of (a : α) :
    presented_group_to_pml cl₁ cl₂ cl_spec cancel_left cancel_right
    (PresentedGroup.of a : PresentedGroup (convert_rels rels)) =
    (@OreLocalization.numeratorHom _ _ _
    (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right)
    (PresentedMonoid.of rels a)) := by
  unfold presented_group_to_pml
  simp only [PresentedGroup.toGroup.of]

-- the following two should be inlined into presentedMonoidLocalizationEquivPresentedGroup
-- but i'm leaving them separate for now to improve readbility
private theorem comp_pg_pml_pml_pg_eq_id : MonoidHom.comp (presented_group_to_pml cl₁ cl₂ cl_spec cancel_left cancel_right)
    (@pml_to_presented_group α rels cl₁ cl₂ cl_spec cancel_left cancel_right) = ⟨⟨id, rfl⟩, fun _ _ => rfl⟩ := by
  let _ := @oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right
  have unique_map_to_self := @presented_fraction_group_to_group_unique α rels cl₁ cl₂ cl_spec cancel_left cancel_right
    (pml cl₁ cl₂ cl_spec cancel_left cancel_right) (group_of_self' cl₁ cl₂ cl_spec cancel_left cancel_right)
    (fun a => @OreLocalization.numeratorHom _ _ _ (@oreSetSelf' _ rels cl₁ cl₂ cl_spec cancel_left cancel_right) (PresentedMonoid.of rels a))
    ((rels_pg_iff_rels_pml _).mp <| fraction_identity_works cl₁ cl₂ cl_spec cancel_left cancel_right)
  have Sh2 := unique_map_to_self (MonoidHom.comp (presented_group_to_pml cl₁ cl₂ cl_spec cancel_left cancel_right)
    (@pml_to_presented_group α rels cl₁ cl₂ cl_spec cancel_left cancel_right)) (fun x => by simp only [MonoidHom.coe_comp,
      Function.comp_apply, pml_to_presented_group_apply_of, presented_group_to_pml_apply_of])
  exact Sh2.trans (unique_map_to_self ⟨⟨id, rfl⟩, fun _ _ => rfl⟩
    (fun r => by simp only [MonoidHom.coe_mk, OneHom.coe_mk, id_eq])).symm

private theorem comp_pml_pg_pg_pml_eq_id : MonoidHom.comp (pml_to_presented_group cl₁ cl₂ cl_spec cancel_left cancel_right)
    (@presented_group_to_pml α rels cl₁ cl₂ cl_spec cancel_left cancel_right) = ⟨⟨id, rfl⟩, fun _ _ => rfl⟩ := by
  apply PresentedGroup.ext
  intro x
  apply PresentedGroup.toGroup.unique presented_identity_works
  intro y
  simp only [MonoidHom.coe_comp, Function.comp_apply, presented_group_to_pml_apply_of,
    pml_to_presented_group_apply_of]

--should go in the monoid hom file - it is true more generally, but it's convenient to have the MulHom form here
theorem comp_eq_of_hom_comp_eq {α β γ : Type*} [Monoid α] [Monoid β] [Monoid γ] {ab : MonoidHom α β}
    {bc : MonoidHom β γ} {ac : MonoidHom α γ} (h : MonoidHom.comp bc ab = ac) :
    bc.toFun ∘ ab.toFun = ac.toFun:=
  funext fun x ↦ ((congrArg (fun y ↦ (bc ∘ ab) x = y x) h.symm)).mpr rfl

/-- the localization of a presented monoid is isomorphic to the presented group over the same
relations-/
def presentedMonoidLocalizationEquivPresentedGroup : pml cl₁ cl₂ cl_spec cancel_left cancel_right ≃* PresentedGroup (convert_rels rels) :=
  ⟨⟨pml_to_presented_group cl₁ cl₂ cl_spec cancel_left cancel_right, presented_group_to_pml cl₁ cl₂ cl_spec cancel_left cancel_right,
  Function.leftInverse_iff_comp.mpr <| comp_eq_of_hom_comp_eq (comp_pg_pml_pml_pg_eq_id cl₁ cl₂ cl_spec cancel_left cancel_right),
  Function.rightInverse_iff_comp.mpr <| comp_eq_of_hom_comp_eq (comp_pml_pg_pg_pml_eq_id cl₁ cl₂ cl_spec cancel_left cancel_right)⟩,
  map_mul (pml_to_presented_group cl₁ cl₂ cl_spec cancel_left cancel_right)⟩
