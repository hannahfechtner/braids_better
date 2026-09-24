import BraidProject.BraidGroup
import BraidProject.ToEdge
import BraidProject.Additions.NatDist
import BraidProject.BraidMonoidInf
import BraidProject.Grid.Properties
import BraidProject.Additions.Mixins
import BraidProject.OreLocalizationCombined

namespace Braid

open Nat

open FreeMonoid in
inductive braid_monoid_rels_inf_one_refl_symm : FreeMonoid ℕ → FreeMonoid ℕ → Prop
  | adjacent (i j : ℕ) (h : i.dist j = 1) :
      braid_monoid_rels_inf_one_refl_symm (of i * of j * of i) (of j * of i * of j)
  | separated (i j : ℕ) (h : i.dist j ≥ 2) :
      braid_monoid_rels_inf_one_refl_symm (of i * of j) (of j * of i)
  | basic : braid_monoid_rels_inf_one_refl_symm 1 1

theorem connect_monoid_group_braid_rels :
    PresentedGroup.free_group_set_of_function braid_monoid_rels_inf_one_refl_symm =
    Braid.braidRelationInf := by
  unfold PresentedGroup.free_group_set_of_function
  ext y
  constructor
  · intro h
    simp only [Set.mem_setOf_eq, Prod.exists] at h
    rcases h with ⟨a, b, hbr, hl⟩
    rw [← hl, freeMonoid_lift_freeGroup_of, freeMonoid_lift_freeGroup_of]
    cases hbr with
    | adjacent i j hd =>
      simp only [to_horizontal_edge_no_epsilon, FreeGroup.mul_mk,
        FreeGroup.inv_mk]
      use (i, j)
      simp only [Function.uncurry_apply_pair, ArtinTits.Group.relation, BraidMatrixInf_adjacent, Monoid.alternate, hd]
      rfl
    | separated i j h =>
      use (i, j)
      simp only [Function.uncurry_apply_pair, ArtinTits.Group.relation, BraidMatrixInf_separated h,
        Monoid.alternate_two, mul_inv_rev, to_horizontal_edge_no_epsilon, FreeGroup.inv_mk,
        FreeGroup.mul_mk]
      rfl
    | basic =>
      use (1,1)
      simp [ArtinTits.Group.relation]
      rfl
  intro h
  simp only [Set.mem_setOf_eq, Prod.exists]
  unfold Braid.braidRelationInf ArtinTits.Group.relation_set at h
  simp only [Set.mem_range, Prod.exists, Function.uncurry_apply_pair] at h
  rcases h with ⟨a, b, br⟩
  unfold ArtinTits.Group.relation at br
  cases hab : a.dist b with
  | zero =>
    simp only [Nat.eq_of_dist_eq_zero hab, mul_inv_cancel] at br
    rw [← br]
    use 1, 1
    constructor
    · apply braid_monoid_rels_inf_one_refl_symm.basic
    simp
  | succ n =>
    cases hn : n with
    | zero =>
      rw [← br]
      use [a, b, a], [b, a, b]
      constructor
      · rw [hn, zero_add] at hab
        exact braid_monoid_rels_inf_one_refl_symm.adjacent _ _ hab
      simp only [hab, hn, zero_add, BraidMatrixInf_adjacent, Monoid.alternate_three, mul_inv_rev]
      rfl
    | succ n2 =>
      have : a.dist b > 1 := by linarith
      rw [← br]
      use [a, b], [b, a]
      constructor
      · apply braid_monoid_rels_inf_one_refl_symm.separated
        aesop
      simp [BraidMatrixInf_separated this]
      rfl

open PresentedMonoid in
theorem one_symm_is_really_the_same : mk braid_monoid_rels_inf a = mk braid_monoid_rels_inf b ↔
  mk braid_monoid_rels_inf_one_refl_symm a = mk braid_monoid_rels_inf_one_refl_symm b := by
  constructor
  · intro h
    apply PresentedMonoid.exact at h
    apply PresentedMonoid.sound
    induction h with
    | of x y h2 =>
      cases h2 with
      | adjacent i =>
        exact PresentedMonoid.rels_alone <| braid_monoid_rels_inf_one_refl_symm.adjacent _ _ dist_self_add_one
      | separated i j h =>
        exact PresentedMonoid.rels_alone <| braid_monoid_rels_inf_one_refl_symm.separated _ _ (le_dist_iff.mpr (Or.inl h))
    | refl x => exact PresentedMonoid.refl
    | symm _ ih => exact PresentedMonoid.symm ih
    | trans _ _ ih1 ih2 => exact PresentedMonoid.trans ih1 ih2
    | mul _ _ ih1 ih2 => exact mul ih1 ih2
  intro h
  apply PresentedMonoid.exact at h
  apply PresentedMonoid.sound
  induction h with
  | of x y h =>
    cases h with
    | adjacent i j h =>
      rcases eq_dist_iff.mp h with ⟨rfl⟩ | ⟨rfl⟩
      · exact rels_alone (braid_monoid_rels_inf.adjacent _)
      exact PresentedMonoid.symm (rels_alone (braid_monoid_rels_inf.adjacent j))
    | separated i j h =>
      rcases le_dist_iff.mp h with h | h
      · exact rels_alone <| braid_monoid_rels_inf.separated _ _ h
      exact PresentedMonoid.symm <| rels_alone <| braid_monoid_rels_inf.separated _ _ h
    | basic => exact BraidMonoidInf.exact rfl
  | refl x => exact BraidMonoidInf.exact rfl
  | symm _ ih => exact PresentedMonoid.symm ih
  | trans _ _ ih1 ih2 => exact PresentedMonoid.trans ih1 ih2
  | mul _ _ ih1 ih2 => exact mul ih1 ih2

noncomputable def PresentedMonoid.hom_two_rels_of_mk_imp {α : Type*}
    {rels₁ rels₂ : FreeMonoid α → FreeMonoid α → Prop}
    (h : ∀ a b, PresentedMonoid.mk rels₁ a = PresentedMonoid.mk rels₁ b →
                PresentedMonoid.mk rels₂ a = PresentedMonoid.mk rels₂ b) :
    PresentedMonoid rels₁ →* PresentedMonoid rels₂ :=
  PresentedMonoid.lift (PresentedMonoid.of rels₂) fun a b hab => by
    rw [PresentedMonoid.mkfreeMonoid_lift_presentedMonoid_of,
        PresentedMonoid.mkfreeMonoid_lift_presentedMonoid_of]
    exact h a b (PresentedMonoid.sound (PresentedMonoid.rels_alone hab))

noncomputable def map_to_one_symm : (PresentedMonoid braid_monoid_rels_inf) →*
    PresentedMonoid braid_monoid_rels_inf_one_refl_symm :=
  PresentedMonoid.hom_two_rels_of_mk_imp fun _ _ => one_symm_is_really_the_same.mp

noncomputable def map_from_one_symm : (PresentedMonoid braid_monoid_rels_inf_one_refl_symm) →*
    PresentedMonoid braid_monoid_rels_inf :=
  PresentedMonoid.hom_two_rels_of_mk_imp fun _ _ => one_symm_is_really_the_same.mpr

noncomputable def one_symm_type_iso_me : (PresentedMonoid braid_monoid_rels_inf_one_refl_symm) ≃*
    PresentedMonoid braid_monoid_rels_inf :=
  MonoidHom.toMulEquiv map_from_one_symm map_to_one_symm (PresentedMonoid.ext_iff.mpr (fun _ => rfl))
   (PresentedMonoid.ext_iff.mpr (fun _ => rfl))

instance : IsCommonLeftMultipleMul (PresentedMonoid braid_monoid_rels_inf_one_refl_symm) := by
    have : IsCommonLeftMultipleMul (PresentedMonoid braid_monoid_rels_inf) := by
      change IsCommonLeftMultipleMul BraidMonoidInf
      infer_instance
    apply left_multiple_iso one_symm_type_iso_me.symm

instance : IsCancelMul (PresentedMonoid braid_monoid_rels_inf_one_refl_symm) := by
    have : IsCancelMul (PresentedMonoid braid_monoid_rels_inf) := by
      change IsCancelMul BraidMonoidInf
      infer_instance
    apply cancel_mul_iso one_symm_type_iso_me.symm

theorem braidMonoid_mk_eq_of_braidGroup_mk_eq_of_positive {e d : List (ℕ × Bool)}
    (h : BraidGroupInf.mk (FreeGroup.mk e) =
    BraidGroupInf.mk (FreeGroup.mk d))
    (hd : ∀ x ∈ d, x.2 = true) (he : ∀ x ∈ e, x.2 = true) :
    BraidMonoidInf.mk (List.map (fun x ↦ x.1) e) =
    BraidMonoidInf.mk (List.map (fun x ↦ x.1) d) := by
  unfold BraidGroupInf.mk at h
  rw [← connect_monoid_group_braid_rels] at h
  apply one_symm_is_really_the_same.mpr
  exact OreLocalization.Presented.presentedMonoid_mk_eq_of_presentedGroup_mk_eq_of_positive _ h hd he
