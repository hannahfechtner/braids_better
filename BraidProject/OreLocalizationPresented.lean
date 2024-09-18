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
variable [OreLocalization.OreSet (submonoid_self (PresentedMonoid rels))]
local notation "P" => PresentedMonoid rels
local notation "pml" =>  OreLocalization (submonoid_self P) P
variable [Group pml]

theorem presented_identity_works : ∀ r ∈ convert_rels rels, (FreeGroup.lift PresentedGroup.of r :
    PresentedGroup (convert_rels rels)) = 1 := by
  intro r h
  -- ought I add this? to the PresentedGroup API
  rw [← (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure h)]
  -- because FreeGroup.induction_on isn't tagged induction_eliminator in the FreeGroup file, using apply
  -- instead of induction' makes my life much easier
  apply @FreeGroup.induction_on α _ r
  · rfl
  · exact fun x => rfl
  · exact fun x _ => rfl
  intro _ _ hx hy
  rw [map_mul, hx, hy]
  rfl

-- this should go somewhere else : either free monoid or free group
theorem lift_eq_lift_lift_of {G₁ : Type} {a : FreeMonoid' α} [Group G₁] (f : α → G₁) : FreeMonoid'.lift f a = (FreeGroup.lift f)
    (FreeMonoid'.lift (FreeGroup.of) a) := by
  induction' a using FreeMonoid'.inductionOn'
  · rfl
  rename_i ih
  simp [ih]

theorem rels_pg_iff_rels_pml {G₁ : Type} [Group G₁] (f : α → G₁) :
    (∀ r ∈ (convert_rels rels), ((FreeGroup.lift f) r ) = 1) ↔ (∀ r₁ r₂, rels r₁ r₂ →
    (FreeMonoid'.lift f r₁ = FreeMonoid'.lift f r₂)) := by
  constructor
  · intro one_version r1 r2 relsy
    specialize one_version ((FreeMonoid'.lift (FreeGroup.of) r1) *
      (FreeMonoid'.lift (FreeGroup.of) r2)⁻¹)
    have anty : FreeMonoid'.lift (FreeGroup.of) r1 * (FreeMonoid'.lift (FreeGroup.of) r2)⁻¹ ∈
        convert_rels rels := by
      apply Prod.exists.mpr
      simp only [Set.mem_setOf_eq]
      use r1, r2
    specialize one_version anty
    simp only [map_mul, map_inv] at one_version
    rw [← lift_eq_lift_lift_of, ← lift_eq_lift_lift_of, ← mul_left_inj ((FreeMonoid'.lift f) r2)]
      at one_version
    simp only [inv_mul_cancel_right, one_mul] at one_version
    exact one_version
  intro double_version r r_in
  rcases r_in with ⟨a, b, one, two⟩
  simp only [Set.mem_setOf_eq] at b
  simp only [map_mul, map_inv]
  erw [← lift_eq_lift_lift_of, ← lift_eq_lift_lift_of]
  rw [double_version a.1 a.2 b, mul_right_inv]

private def pml_to_presented_group : pml →* PresentedGroup (convert_rels rels) :=
  presented_fraction_group_to_group (PresentedGroup.of)
  ((rels_pg_iff_rels_pml PresentedGroup.of).mp presented_identity_works)

@[simp]
private theorem pml_to_presented_group_apply_of (a : α) : pml_to_presented_group
    (OreLocalization.numeratorHom (PresentedMonoid.of rels a)) =
    (PresentedGroup.of a : PresentedGroup (convert_rels rels)) :=
  rfl

theorem lift_of_eq_mk_of_mulHom {β : Type} [Monoid β] (r : FreeMonoid' α) (f : P →* β) :
    (FreeMonoid'.lift fun x => f (PresentedMonoid.of rels x)) r =
    (f (PresentedMonoid.mk rels r)) := by
  induction' r using FreeMonoid'.inductionOn' with _ _ ih
  · exact f.map_one.symm
  rw [map_mul, ih, FreeMonoid'.lift_eval_of, PresentedMonoid.mul_mk, map_mul]
  rfl

--set_option pp.explicit true
private theorem fraction_identity_works [Group pml]:  ∀ r ∈ convert_rels rels, ((FreeGroup.lift
    (fun x => OreLocalization.numeratorHom (PresentedMonoid.of rels x))) r : OreLocalization (submonoid_self P) P) = 1 := by
  sorry
  -- have H := (rels_pg_iff_rels_pml (fun x => OreLocalization.numeratorHom (PresentedMonoid.of rels x))).mpr
  -- intro r1 r2 hr
  -- rw [lift_of_eq_mk_of_mulHom r1, lift_of_eq_mk_of_mulHom r2]
  -- apply OreLocalization.oreDiv_eq_iff.mpr
  -- use 1, 1
  -- constructor
  -- · simp only [OneMemClass.coe_one, mul_one]
  --   exact (PresentedMonoid.sound hr).symm
  -- rfl

private def presented_group_to_pml [Group pml] : PresentedGroup (convert_rels rels) →* pml :=
  PresentedGroup.toGroup fraction_identity_works

@[simp]
private theorem presented_group_to_pml_apply_of (a : α) [Group pml]: presented_group_to_pml
    (PresentedGroup.of a : PresentedGroup (convert_rels rels)) =
    (OreLocalization.numeratorHom (PresentedMonoid.of rels a)) := by
  unfold presented_group_to_pml
  sorry
  --simp only [PresentedGroup.toGroup.of]

-- the following two should be inlined into presentedMonoidLocalizationEquivPresentedGroup
-- but i'm leaving them separate for now to improve readbility
private theorem comp_pg_pml_pml_pg_eq_id [Group pml] : MonoidHom.comp presented_group_to_pml
    (@pml_to_presented_group α rels _) = ⟨⟨id, rfl⟩, fun _ _ => rfl⟩ :=
  (presented_fraction_group_to_group_unique _ ((rels_pg_iff_rels_pml _).mp fraction_identity_works)
  _ (fun _ => by simp)).trans <| (presented_fraction_group_to_group_unique _
  ((rels_pg_iff_rels_pml _).mp fraction_identity_works) ⟨⟨id, rfl⟩, fun _ _ => rfl⟩
  (fun x => rfl)).symm

private theorem comp_pml_pg_pg_pml_eq_id : MonoidHom.comp pml_to_presented_group
    (@presented_group_to_pml α rels _) = ⟨⟨id, rfl⟩, fun _ _ => rfl⟩ :=
  PresentedGroup.ext fun x ↦ (PresentedGroup.toGroup.unique presented_identity_works
  (MonoidHom.comp pml_to_presented_group _) (fun _ => by simp)).trans <|
  (PresentedGroup.toGroup.unique presented_identity_works ⟨⟨id, rfl⟩, fun _ _ => rfl⟩ (fun x => rfl)).symm

--should go in the monoid hom file - it is true more generally, but it's convenient to have the MulHom form here
theorem comp_eq_of_hom_comp_eq {α β γ : Type*} [Monoid α] [Monoid β] [Monoid γ] {ab : MonoidHom α β}
    {bc : MonoidHom β γ} {ac : MonoidHom α γ} (h : MonoidHom.comp bc ab = ac) :
    bc.toFun ∘ ab.toFun = ac.toFun:=
  funext fun x ↦ ((congrArg (fun y ↦ (bc ∘ ab) x = y x) h.symm)).mpr rfl

/-- the localization of a presented monoid is isomorphic to the presented group over the same
relations-/
def presentedMonoidLocalizationEquivPresentedGroup : pml ≃* PresentedGroup (convert_rels rels) :=
  ⟨⟨pml_to_presented_group, presented_group_to_pml,
  Function.leftInverse_iff_comp.mpr <| comp_eq_of_hom_comp_eq comp_pg_pml_pml_pg_eq_id,
  Function.rightInverse_iff_comp.mpr <| comp_eq_of_hom_comp_eq comp_pml_pg_pg_pml_eq_id⟩,
  map_mul pml_to_presented_group⟩
