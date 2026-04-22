import Mathlib.Algebra.Group.SubGroup.ZPowers.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Dist
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric
import BraidProject.ArtinTits

namespace Braid

open ArtinTits
/-- The Artin-Tits matrix for Artin's braid group on n strands -/
def BraidMatrixFin {n : ℕ} : ArtinTitsMatrix (Fin n.pred) where
  M := Matrix.of fun i j : Fin n.pred ↦
    if i = j then 0
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2)
  isSymm := by unfold Matrix.IsSymm; aesop
  off_diagonal := by aesop

/-- The Artin-Tits matrix for Artin's infinite braid group -/
def BraidMatrixInf : ArtinTitsMatrix ℕ where
  M := Matrix.of fun i j : ℕ ↦
    if i = j then 0
      else (if i.dist j = 1 then 3 else 2)
  isSymm := by
    grind [Matrix.IsSymm, Matrix.transpose, Matrix.of_apply, EmbeddingLike.apply_eq_iff_eq,
      Nat.dist]
  off_diagonal := by aesop

def BraidGroupInf := ArtinTitsGroup BraidMatrixInf

def BraidGroupFin (n : ℕ) := ArtinTitsGroup (@BraidMatrixFin n)

instance : Group BraidGroupInf := by
  unfold BraidGroupInf; infer_instance

instance (n : ℕ) : Group (BraidGroupFin n) := by
  unfold BraidGroupFin; infer_instance

def BraidGroupInf.mk := PresentedGroup.mk (ArtinTits.Group.relation_set BraidMatrixInf)

def BraidGroupFin.mk (n : ℕ) := PresentedGroup.mk (ArtinTits.Group.relation_set (@BraidMatrixFin n))

def σ (k : ℕ) : BraidGroupInf := PresentedGroup.of k

def σₙ {n : ℕ} (k : Fin n.pred) : BraidGroupFin n := PresentedGroup.of k

-- def M_braid_inf (i j : ℕ) : ℕ :=
--   match i.dist j with
--   | 0 => 0
--   | 1 => 3
--   | _ => 2

-- def M_braid_fin {n : ℕ} (i j : Fin n) : ℕ :=
--   M_braid_inf i.val j.val

-- theorem M_braid_separated {i j : ℕ} (h : i.dist j ≥ 2) : M_braid_inf i j = 2 := by
--   unfold M_braid_inf
--   aesop

-- theorem M_braid_fin_separated (i j : Fin n) (h : i.val.dist j ≥ 2) : M_braid_fin i j = 2 := by
--   apply M_braid_separated
--   simp only [ge_iff_le, h]

-- theorem M_braid_adjacent {i : ℕ} : M_braid_inf i (i + 1) = 3 := by
--   unfold M_braid_inf
--   simp [Nat.dist, add_tsub_cancel_left]

-- theorem M_braid_fin_adjacent (i : Fin n) : M_braid_fin i.castSucc i.succ = 3 := by
--   unfold M_braid_fin
--   simp only [Fin.val_succ]
--   exact M_braid_adjacent

theorem BraidMatrixInf_separated {i j : ℕ} (h : i.dist j ≥ 2) : BraidMatrixInf.1 i j = 2 := by
  unfold BraidMatrixInf
  aesop

theorem M_braid_fin_separated {n : ℕ} (i j : Fin n.pred) (h : i.val.dist j ≥ 2) :
    BraidMatrixFin.1 i j = 2 := by
  unfold BraidMatrixFin
  grind [Matrix.of_apply, Nat.dist]

theorem BraidMatrixInf_adjacent {i j : ℕ} (h : i.dist j = 1) : BraidMatrixInf.1 i j = 3 := by
  unfold BraidMatrixInf
  aesop

theorem BraidMatrixInf_adjacent' {i : ℕ} : BraidMatrixInf.1 i (i + 1) = 3 := by
  unfold BraidMatrixInf
  simp [Nat.dist, add_tsub_cancel_left]

theorem M_braid_fin_adjacent {n : ℕ} (i j : Fin n.pred) (h : i.val.dist j = 1)  : BraidMatrixFin.1 i j = 3 := by
  unfold BraidMatrixFin
  grind [Matrix.of_apply, Nat.dist]

variable {α : Type*}

theorem BraidGroupInf.braid {i j : ℕ} (hd : i.dist j = 1):
    σ i * σ j * σ i = σ j * σ i * σ j := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, j)
  simp only [Function.uncurry_apply_pair, Group.relation, BraidMatrixInf_adjacent, hd,
    Monoid.alternate_three, mul_inv_rev, inv_inv, mul_one]

theorem BraidGroupFin.braid {n : ℕ} {i j : Fin n.pred} (hd : i.val.dist j.val = 1):
    σₙ i * σₙ j * σₙ i = σₙ j * σₙ i * σₙ j := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, j)
  simp only [Nat.pred_eq_sub_one, M_braid_fin_adjacent _ _ hd, Function.uncurry_apply_pair,
    Group.relation, mul_inv_rev]
  rfl

theorem BraidGroupInf.comm {i j : ℕ} (h : 2 ≤ i.dist j) :
    σ i * σ j = σ j * σ i := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, j)
  simp only [Function.uncurry_apply_pair, Group.relation, BraidMatrixInf_separated h,
    Monoid.alternate_two, mul_inv_rev, inv_inv, mul_one]

theorem BraidGroupFin.comm {n : ℕ} {i j : Fin n.pred} (h : 2 ≤ i.val.dist j.val) :
    σₙ i * σₙ j = σₙ j * σₙ i := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, j)
  simp only [Nat.pred_eq_sub_one, M_braid_fin_separated _ _ h, Function.uncurry_apply_pair,
    Group.relation, mul_inv_rev]
  rfl

theorem BraidGroupInf.generated_by (H : Subgroup BraidGroupInf) (h : ∀ i : ℕ, σ i ∈ H) :
    ∀ x : BraidGroupInf, x ∈ H := PresentedGroup.generated_by _ _ h

theorem BraidGroupFin.generated_by (H : Subgroup (BraidGroupFin n))
    (h : ∀ i : Fin n.pred, σₙ i ∈ H) : ∀ x : BraidGroupFin n, x ∈ H :=
  PresentedGroup.generated_by _ _ h

@[induction_eliminator]
theorem BraidGroupInf.induction_on {C : BraidGroupInf → Prop}
    (H : ∀ z : FreeGroup ℕ, C (BraidGroupInf.mk z)) (x : BraidGroupInf) : C x :=
  PresentedGroup.induction_on x H

@[induction_eliminator]
theorem BraidGroupFin.induction_on {n : ℕ} {C : BraidGroupFin n → Prop}
    (H : ∀ z : FreeGroup (Fin n.pred), C (BraidGroupFin.mk n z)) (x : BraidGroupFin n) : C x :=
  PresentedGroup.induction_on x H

theorem braid_group_2.is_cyclic : ∃ g : (BraidGroupFin 2), ∀ x, x ∈ Subgroup.zpowers g := by
  use (σₙ ⟨0, by aesop⟩)
  intro x
  apply BraidGroupFin.generated_by
  intro i
  rw [Subgroup.mem_zpowers_iff]
  use 1
  have : i = ⟨0, by aesop⟩ := by aesop
  aesop

/-- A map out of the generators of the infinite braid group is liftable
precisely when it satisfies the braid and commutation relations. -/
def BraidGroupInf.IsLiftable {G : Type*} [Group G] (f : ℕ → G) : Prop :=
  (∀ i j : ℕ, i.dist j = 1 → f i * f j * f i = f j * f i * f j) ∧
  (∀ i j : ℕ, 2 ≤ i.dist j → f i * f j = f j * f i)

/-- The braid relations imply the general Artin-Tits liftability condition
for the infinite braid Group. -/
theorem BraidGroupInf.isLiftable_iff {G : Type*} [Group G] {f : ℕ → G} :
    BraidGroupInf.IsLiftable f ↔ ArtinTits.IsLiftable BraidMatrixInf f := by
  constructor
  · intro hf
    rcases hf with ⟨hbraid, hcomm⟩
    intro i j
    by_cases h1 : i.dist j = 1
    · rw [BraidMatrixInf_adjacent h1]
      simp [Monoid.alternate_three, hbraid i j h1, mul_assoc]
    by_cases h2 : 2 ≤ i.dist j
    · rw [BraidMatrixInf_separated h2]
      simp [Monoid.alternate_two, hcomm i j h2]
    grind [Nat.dist]
  intro hf
  constructor
  · intro i j h
    grind [Monoid.alternate_three, BraidMatrixInf_adjacent, hf i j]
  intro i j h
  grind [Monoid.alternate_two, BraidMatrixInf_separated, hf i j]

/-- The universal map out of the infinite braid Group. -/
def BraidGroupInf.toGroup {G : Type*} [Group G] {f : ℕ → G}
    (hf : BraidGroupInf.IsLiftable f) : BraidGroupInf →* G :=
  ArtinTits.toGroup BraidMatrixInf ((BraidGroupInf.isLiftable_iff).mp hf)

/-- The universal map sends the standard generator `σ i` to `f i`. -/
theorem BraidGroupInf.toGroup_of {G : Type*} [Group G] {f : ℕ → G}
    (hf : BraidGroupInf.IsLiftable f) (i : ℕ) :
    BraidGroupInf.toGroup hf (σ i) = f i :=
  ArtinTits.toGroup_of BraidMatrixInf ((BraidGroupInf.isLiftable_iff).mp hf)

/-- Uniqueness in the universal property of the infinite braid Group. -/
theorem BraidGroupInf.toGroup_unique {G : Type*} [Group G] {f : ℕ → G}
    (hf : BraidGroupInf.IsLiftable f) (g : BraidGroupInf →* G)
    (hg : ∀ i : ℕ, g (σ i) = f i) : BraidGroupInf.toGroup hf = g :=
  ArtinTits.toGroup_unique BraidMatrixInf g hg _

/-- A map out of the generators of the finite braid group is liftable
precisely when it satisfies the braid and commutation relations. -/
def BraidGroupFin.IsLiftable (n : ℕ) {G : Type*} [Group G] (f : Fin n.pred → G) : Prop :=
  (∀ i j : Fin n.pred, i.val.dist j.val = 1 → f i * f j * f i = f j * f i * f j) ∧
  (∀ i j : Fin n.pred, 2 ≤ i.val.dist j.val → f i * f j = f j * f i)

/-- The braid relations imply the general Artin-Tits liftability condition
for the finite braid Group. -/
theorem BraidGroupFin.isLiftable_iff (n : ℕ) {G : Type*} [Group G] {f : Fin n.pred → G} :
    BraidGroupFin.IsLiftable n f ↔ ArtinTits.IsLiftable (BraidMatrixFin) f := by
  constructor
  · intro hf
    rcases hf with ⟨hbraid, hcomm⟩
    intro i j
    by_cases h1 : i.val.dist j.val = 1
    · rw [M_braid_fin_adjacent i j h1]
      simp [Monoid.alternate_three, hbraid i j h1, mul_assoc]
    · by_cases h2 : 2 ≤ i.val.dist j.val
      · rw [M_braid_fin_separated i j h2]
        simp [Monoid.alternate_two, hcomm i j h2]
      grind [Nat.dist]
  · intro hf
    constructor
    · intro i j h
      grind [Monoid.alternate_three, M_braid_fin_adjacent, hf i j]
    intro i j h
    grind [Monoid.alternate_two, M_braid_fin_separated, hf i j]

/-- The universal map out of the finite braid Group. -/
def BraidGroupFin.toGroup (n : ℕ) {G : Type*} [Group G] {f : Fin n.pred → G}
    (hf : BraidGroupFin.IsLiftable n f) : BraidGroupFin n →* G :=
  ArtinTits.toGroup (BraidMatrixFin) ((BraidGroupFin.isLiftable_iff n).mp hf)

/-- The universal map sends the standard generator `σₙ i` to `f i`. -/
theorem BraidGroupFin.toGroup_of (n : ℕ) {G : Type*} [Group G] {f : Fin n.pred → G}
    (hf : BraidGroupFin.IsLiftable n f) (i : Fin n.pred) :
    BraidGroupFin.toGroup n hf (σₙ i) = f i := by
  exact ArtinTits.toGroup_of (BraidMatrixFin) ((BraidGroupFin.isLiftable_iff n).mp hf)

/-- Uniqueness in the universal property of the finite braid Group. -/
theorem BraidGroupFin.toGroup_unique (n : ℕ) {G : Type*} [Group G] {f : Fin n.pred → G}
    (hf : BraidGroupFin.IsLiftable n f) (g : BraidGroupFin n →* G)
    (hg : ∀ i : Fin n.pred, g (σₙ i) = f i) :
    BraidGroupFin.toGroup n hf = g := by
  apply ArtinTits.toGroup_unique (BraidMatrixFin) g hg
  
end Braid

/-
We need a theorem that says that we can define a function from the braid group by giving any
function on the generators that satisfies the relations.
-/
