import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Fin.Basic
import BraidProject.BraidMonoid

namespace Braid

variable (M : α → α → ℕ)

def alternate (s t : α) (k : ℕ) :=
  match k with
  | 0 => 1
  | Nat.succ n => FreeGroup.of s * alternate t s n

def artin_tits_rel (s t : α) : FreeGroup (α) :=
  alternate s t (M s t) * (alternate t s (M s t))⁻¹

@[simp]
theorem alternate_one (a b : α) : alternate a b 1 = .of a := rfl

@[simp]
theorem alternate_two (a b : α) : alternate a b 2 = .of a * .of b := rfl

@[simp]
theorem alternate_three (a b : α) : alternate a b 3 = .of a * .of b * .of a := rfl

def M_braid_inf (i j : ℕ) : ℕ :=
  match i.dist j with
  | 0 => 0
  | 1 => 3
  | _ => 2

def M_braid_fin {n : ℕ} (i j : Fin n) : ℕ :=
  M_braid_inf i.val j.val

theorem M_braid_separated {i j : ℕ} (h : i.dist j ≥ 2) : M_braid_inf i j = 2 := by
  unfold M_braid_inf
  aesop

theorem M_braid_fin_separated (i j : Fin n) (h : i.val.dist j ≥ 2) : M_braid_fin i j = 2 := by
  apply M_braid_separated
  simp only [ge_iff_le, h]

theorem M_braid_adjacent {i : ℕ} : M_braid_inf i (i + 1) = 3 := by
  unfold M_braid_inf
  simp [Nat.dist, add_tsub_cancel_left]

theorem M_braid_fin_adjacent (i : Fin n) : M_braid_fin i.castSucc i.succ = 3 := by
  unfold M_braid_fin
  simp only [Fin.val_succ]
  exact M_braid_adjacent

def artin_tits_rel_set (M : α → α → ℕ) : Set (FreeGroup α) :=
  Set.range (Function.uncurry (artin_tits_rel M))

def ArtinTitsGroup (M : α → α → ℕ) := PresentedGroup (artin_tits_rel_set M)

def BraidGroupInf := ArtinTitsGroup (M_braid_inf)

def BraidGroupFin (n : ℕ) := ArtinTitsGroup (@M_braid_fin n.pred)

def braid_rels_coexeter : Set (FreeGroup ℕ) :=
  Set.range (Function.uncurry (artin_tits_rel M_braid_inf))

def braid_rels_fin_coexeter (n : ℕ): Set (FreeGroup (Fin n)) := Set.range (Function.uncurry (artin_tits_rel M_braid_fin))

instance : Group (ArtinTitsGroup rels ):= by
  unfold ArtinTitsGroup; infer_instance

instance (n : ℕ) : Group (BraidGroupFin n) := by
  unfold BraidGroupFin; infer_instance

instance : Group BraidGroupInf := by
  unfold BraidGroupInf; infer_instance

def σ {n : ℕ} (k : Fin n) : BraidGroupFin (n+1) := PresentedGroup.of k

def σi (k : ℕ) : BraidGroupInf := PresentedGroup.of k

theorem braid_group_inf.braid {i j : ℕ} (hd : i.dist j = 1):
    σi i * σi j * σi i = σi j * σi i * σi j := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, j)
  simp only [Function.uncurry_apply_pair, artin_tits_rel, M_braid_inf, hd, alternate_three,
    mul_inv_rev, inv_inv, mul_one]

theorem braid_group.braid {i j : Fin n} (hd : i.val.dist j.val = 1):
    σ i * σ j * σ i = σ j * σ i * σ j := by
  have is_three : M_braid_fin i j = 3 := by
    unfold M_braid_fin M_braid_inf
    grind [Nat.dist]
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, j)
  simp only [Nat.pred_eq_sub_one, Nat.add_one_sub_one, Function.uncurry_apply_pair, artin_tits_rel,
    is_three, alternate_three, mul_inv_rev]
  rfl

theorem separated (h : 2 ≤ e.dist g) : FreeGroup.of e * .of g * (.of e)⁻¹ * (.of g)⁻¹ ∈
    braid_rels_coexeter := by
  refine Set.mem_range.mpr ?_
  use (e, g)
  rw [Function.uncurry_apply_pair, artin_tits_rel, M_braid_separated h]
  simp only [alternate_two, mul_inv_rev]
  rfl

theorem braid_group_inf.comm {i j : ℕ} (h : 2 ≤ i.dist j) :
    σi i * σi j = σi j * σi i := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, j)
  simp only [Function.uncurry_apply_pair, artin_tits_rel, M_braid_separated h, alternate_two, mul_inv_rev,
    inv_inv, mul_one]

theorem braid_group.comm {i j : Fin n} (h : 2 ≤ i.val.dist j.val) :
    σ i * σ j = σ j * σ i := by
  have is_two : M_braid_fin i j = 2 := by
    unfold M_braid_fin M_braid_inf
    grind [Nat.dist]
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, j)
  simp only [Nat.pred_eq_sub_one, Nat.add_one_sub_one, Function.uncurry_apply_pair, artin_tits_rel,
    is_two, alternate_two, mul_inv_rev]
  rfl

theorem generated_by (H : Subgroup BraidGroupInf) (h : ∀ i : ℕ, σi i ∈ H) :
    ∀ x : BraidGroupInf, x ∈ H := by
  intro x
  apply QuotientGroup.induction_on
  intro z
  apply FreeGroup.induction_on (C := fun z => ⟦z⟧ ∈ H) _ (one_mem H)
  . exact fun i => h i
  . exact fun i h => (Subgroup.inv_mem_iff H).mp h
  intro i j h1 h2
  change QuotientGroup.mk _ ∈ H.carrier
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ h1 h2

  theorem generated_by_fin (H : Subgroup (BraidGroupFin (n+1))) (h : ∀ i : Fin n, σ i ∈ H) :
    ∀ x : BraidGroupFin (n+1), x ∈ H := by
  intro x
  apply QuotientGroup.induction_on
  intro z
  apply FreeGroup.induction_on (C := fun z => ⟦z⟧ ∈ H) _ (one_mem H)
  . exact fun i => h i
  . intro i h
    apply (Subgroup.inv_mem_iff H).mp
    exact h
  intro i j h1 h2
  change QuotientGroup.mk _ ∈ H.carrier
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ h1 h2


theorem braid_group_2.is_cyclic : ∃ g : (BraidGroupFin 2), ∀ x, x ∈ Subgroup.zpowers g := by
  use (σ 0)
  intro x
  apply generated_by_fin
  intro i
  rw [Subgroup.mem_zpowers_iff]
  use 1
  have h : i=0 := by
    omega
  rw [h]
  rfl

theorem embed_helper (n : ℕ) : ∀ (a b : FreeMonoid (Fin (n.pred))),
    (braid_rels_m (n.pred)) a b → ((FreeMonoid.lift fun a => σ a) a : BraidGroupFin n)=
    (FreeMonoid.lift fun a => σ a) b := by
  repeat
    rcases n
    · exact fun _ _ h => h.elim
    rename_i n
  intro a b h
  rcases h
  · rename_i j
    simp only [map_mul, FreeMonoid.lift_eval_of, Nat.pred_succ]
    apply braid_group.braid
    unfold Nat.dist
    aesop
  simp only [map_mul, FreeMonoid.lift_eval_of, Nat.pred_succ]
  apply braid_group.comm
  unfold Nat.dist Fin.castSucc Fin.castAdd Fin.castLE Fin.succ
  simp only
  omega

def embed {n : ℕ} : (BraidMonoid n) →* (BraidGroupFin (n)) :=
  PresentedMonoid.toMonoid (fun a => @σ (n.pred) a) (embed_helper n)

theorem embed_inf_helper (a b : FreeMonoid ℕ) (h : braid_rels_m_inf a b) :
    (FreeMonoid.lift fun a => σi a) a = (FreeMonoid.lift fun a => σi a) b := by
  cases h
  · apply braid_group_inf.braid
    unfold Nat.dist
    omega
  simp
  apply braid_group_inf.comm
  unfold Nat.dist
  omega

def embed_inf : BraidMonoidInf →* BraidGroupInf :=
  PresentedMonoid.toMonoid (fun a => σi a) embed_inf_helper

/-
We need a theorem that says that we can define a function from the braid group by giving any
function on the generators that satisfies the relations.

This should just be a nicer repackaging of `PresentedGroup.toGroup`.
-/
