import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Maps
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
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
    { r | ∃ i : ℕ , r = (FreeGroup.of i) * (FreeGroup.of (i + 1)) * FreeGroup.of i * (FreeGroup.of (i + 1))⁻¹ * (FreeGroup.of i)⁻¹ * (FreeGroup.of (i + 1))⁻¹} ∪
    { r | ∃ i j : ℕ, i ≤ j ∧ r = (FreeGroup.of i) * (FreeGroup.of j) * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹}

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

def σ {n : ℕ} (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k

def σi (k : ℕ) : braid_group_inf := PresentedGroup.of k


/-
This version makes n explicit. Note that `σ' n k` is an element of
`braid group (n + 1).`
-/
abbrev σ' (n : ℕ) (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k

-- #check σ' 5 2
-- #check (σ 2 : braid_group 6)

-- example : σ' 5 2 = σ 2 := rfl

/-
This says that σ i * σ (i + 1) * σ i = σ (i + 1) * σ i * σ (i + 1) in `braid_group (n + 2)`,
the smallest group in which there are any generators at all.
Notice that this means that `i` and `i + 1` must be `Fin (n + 1)`.
To make type checking work, we take `i` in `Fin n`, and use
`i.castSucc` and `i.succ` to interpret `i` and `i + 1` as elements of `Fin (n + 1)`.
-/
theorem braid_group.braid {n : ℕ} (i : Fin n) :
    σ' (n + 1) i.castSucc * σ i.succ * σ i.castSucc = σ i.succ * σ i.castSucc * σ i.succ := by
  symm; rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  cases n
  . next => apply i.elim0
  . next n =>
    left; use i; simp [braid_rels, braid_rel, mul_assoc]

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

theorem generated_by (n : ℕ) (H : Subgroup (braid_group (n + 1))) (h : ∀ i : Fin n, σ' n i ∈ H) :
    ∀ x : braid_group (n + 1), x ∈ H := by
  intro x
  apply QuotientGroup.induction_on
  intro z
  change ⟦z⟧ ∈ H
  apply FreeGroup.induction_on (C := fun z => ⟦z⟧ ∈ H)
  . exact one_mem H
  . intro i
    apply h
  . intro i
    change σ i ∈ H.carrier → (σ i)⁻¹ ∈ H.carrier
    simp only [Nat.pred_succ, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
      inv_mem_iff, imp_self]
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

--basic braids to try to visualize

def french : braid_group 3 := σ 0 * (σ 1)⁻¹
def dutch : braid_group 3 := (σ 0)⁻¹ * σ 1
def empty (n: ℕ) : braid_group n := 1
def challah_start (n : ℕ) (k: Fin n): braid_group (n + 2) := σ' (n + 1) k
def challah_granular (n: ℕ) : ℕ →  braid_group (n+2)
  | 0 => 1
  | k+1 => challah_granular n k * (σ (k+1))⁻¹
def challah_repeat (n : ℕ) : braid_group (n + 2) := challah_granular n n
def challah_end (n : ℕ) : braid_group (n + 2) := σ 0

def challah (n : ℕ) (k : Fin n) : braid_group (n + 2) := challah_start n k * (challah_repeat n)^(k : ℕ) * challah_end n

/-
We need a theorem that says that we can define a function from the braid group by giving any
function on the generators that satisfies the relations.

This should just be a nicer repackaging of `PresentedGroup.toGroup`.
-/
