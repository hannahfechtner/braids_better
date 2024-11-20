import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Maps
import Mathlib.Data.Fin.Basic
import BraidProject.BraidMonoid

--set_option autoImplicit false
namespace Braid

section
local instance (S : Type _) : Coe S (FreeGroup S) := ⟨FreeGroup.of⟩

def comm_rel {S : Type _} (i j : S) : FreeGroup S :=
  i * j * (↑i)⁻¹ * (↑j)⁻¹

def braid_rel {S : Type _} (i j : S) : FreeGroup S :=
  i * j * i * (↑j)⁻¹ * (↑i)⁻¹ * (↑j)⁻¹

end

def braid_rels : (n : ℕ) → Set (FreeGroup (Fin n))
  | 0     => ∅
  | 1     => ∅
  | n + 2 =>
    { r | ∃ i : Fin (n + 1), r = braid_rel (i.castSucc) (i.succ) } ∪
    { r | ∃ i j : Fin n, i ≤ j ∧ r = comm_rel (i.castSucc.castSucc) (j.succ.succ) }

def braid_rels_inf : Set (FreeGroup ℕ) :=
  { r | ∃ i : ℕ , r = .of i * (.of (i + 1)) * .of i *
    (.of (i + 1))⁻¹ * (.of i)⁻¹ * (.of (i + 1))⁻¹} ∪
  { r | ∃ i j : ℕ, i + 2 ≤ j ∧ r = .of i * .of j * (.of i)⁻¹ * (.of j)⁻¹}

/-
The predecessor in the next definition is annoying, but hopefully not too bad.
Most of the time we will write `braid_group (n + 1)`, which corresponds to `B_{n + 1}`.
-/

def braid_group (n : ℕ) := PresentedGroup (braid_rels n.pred)

def braid_group_inf := PresentedGroup braid_rels_inf

instance (n : ℕ) : Group (braid_group n) := by
  unfold braid_group; infer_instance

instance : Group braid_group_inf := by
  unfold braid_group_inf; infer_instance

def braid_group.rel := PresentedGroup braid_rels_inf

def σ {n : ℕ} (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k

def σi (k : ℕ) : braid_group_inf := PresentedGroup.of k


/-
This version makes n explicit. Note that `σ' n k` is an element of
`braid group (n + 1).`
-/
abbrev σ' (n : ℕ) (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k

theorem braid_group.braid {n : ℕ} {i j : Fin n} (h : i ≤ j) :
    σ' (n + 2) i.castSucc.castSucc * σ j.succ.succ = σ j.succ.succ * σ i.castSucc.castSucc := by
  symm; rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  left; use i
  simp [braid_rels, braid_rel, mul_assoc]
  sorry

theorem braid_group_inf.braid (i : ℕ) :
    σi i * σi i.succ * σi i = σi i.succ * σi i * σi i.succ := by
  symm; rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  left; use i
  simp [braid_rels, braid_rel, mul_assoc]

theorem braid_group.comm {n : ℕ} {i j : Fin n} (h : i ≤ j) :
    σ' (n + 2) i.castSucc.castSucc * σ j.succ.succ = σ j.succ.succ * σ i.castSucc.castSucc := by
  symm; rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  cases n
  . next => apply i.elim0
  . next n =>
    right; use i, j, h; simp [braid_rels, comm_rel, mul_assoc]

theorem braid_group_inf.comm {i j : ℕ} (h : i + 2 ≤ j) :
    σi i * σi j = σi j * σi i := by
  symm; rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  right
  simp
  use i
  use j
  constructor
  · exact h
  simp only [mul_assoc]

theorem generated_by (n : ℕ) (H : Subgroup (braid_group (n + 1))) (h : ∀ i : Fin n, σ' n i ∈ H) :
    ∀ x : braid_group (n + 1), x ∈ H := by
  intro x
  apply QuotientGroup.induction_on
  intro z
  change ⟦z⟧ ∈ H
  apply FreeGroup.induction_on (C := fun z => ⟦z⟧ ∈ H) _ (one_mem H) (fun _ => h _)
  . intro i
    change σ i ∈ H.carrier → (σ i)⁻¹ ∈ H.carrier
    simp only [Nat.pred_succ, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      Subgroup.mem_toSubmonoid, inv_mem_iff, imp_self]
  . intro i j h1 h2
    change QuotientGroup.mk _ ∈ H.carrier
    rw [QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ h1 h2

theorem braid_group_2.is_cyclic : ∃ g : (braid_group 2), ∀ x, x ∈ Subgroup.zpowers g := by
  use (σ 0)
  intro x
  apply generated_by
  intro i
  rw [Subgroup.mem_zpowers_iff]
  have h : i=0 := by
    apply Fin.eq_of_val_eq
    simp
  use 1
  rw [h]
  rfl

theorem embed_helper (n : ℕ) : ∀ (a b : FreeMonoid' (Fin (n.pred))),
    (braid_rels_m (n.pred)) a b → ((FreeMonoid'.lift fun a => σ a) a : braid_group n)=
    (FreeMonoid'.lift fun a => σ a) b := by
  repeat
    rcases n
    · intro _ _ h
      exfalso
      apply h
    rename_i n
  intro a b h
  rcases h
  · rename_i j
    simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
    sorry --apply braid_group.braid
  simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
  apply braid_group.comm
  next ih => exact ih

def embed {n : ℕ} : (BraidMonoid n) →* (braid_group (n)) :=
  PresentedMonoid.toMonoid (fun a => @σ (n.pred) a) (embed_helper n)

theorem embed_inf_helper : ∀ (a b : FreeMonoid' ℕ),
    (braid_rels_m_inf a b → ((FreeMonoid'.lift fun a => σi a) a : braid_group_inf)=
    (FreeMonoid'.lift fun a => σi a) b) := by
  intro a b h
  rcases h
  · rename_i j
    simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
    apply braid_group_inf.braid
  simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
  apply braid_group_inf.comm
  next ih => exact ih

def embed_inf : BraidMonoidInf →* braid_group_inf :=
  PresentedMonoid.toMonoid (fun a => σi a) embed_inf_helper

/-
We need a theorem that says that we can define a function from the braid group by giving any
function on the generators that satisfies the relations.

This should just be a nicer repackaging of `PresentedGroup.toGroup`.
-/
