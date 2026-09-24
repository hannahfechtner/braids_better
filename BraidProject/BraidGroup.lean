import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Dist
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric
import BraidProject.ArtinTits
import BraidProject.Additions.FreeGroup
import BraidProject.SignedListBounded

namespace Braid

open ArtinTits
/-- The Artin-Tits matrix for Artin's braid group on n strands -/
def BraidMatrixFin {n : ℕ} : ArtinTitsMatrix (Fin n.pred) where
  M := Matrix.of fun i j : Fin n.pred ↦
    if i = j then 0
      else (if Nat.dist i.val j.val = 1 then 3 else 2)
  isSymm := by
    unfold Matrix.IsSymm
    aesop (add simp Nat.dist_comm)
  off_diagonal := by aesop
  diagonal := by aesop

/-- The Artin-Tits matrix for Artin's infinite braid group -/
def BraidMatrixInf : ArtinTitsMatrix ℕ where
  M := Matrix.of fun i j : ℕ ↦
    if i = j then 0
      else (if i.dist j = 1 then 3 else 2)
  isSymm := by
    grind [Matrix.IsSymm, Matrix.transpose, Matrix.of_apply, EmbeddingLike.apply_eq_iff_eq,
      Nat.dist]
  off_diagonal := by aesop
  diagonal := by aesop

def BraidGroupInf := ArtinTitsGroup BraidMatrixInf

def BraidGroupFin (n : ℕ) := ArtinTitsGroup (@BraidMatrixFin n)

instance : Group BraidGroupInf := by
  unfold BraidGroupInf; infer_instance

instance (n : ℕ) : Group (BraidGroupFin n) := by
  unfold BraidGroupFin; infer_instance

def braidRelationInf := (ArtinTits.Group.relation_set BraidMatrixInf)

def braidRelationFin (n : ℕ) := (ArtinTits.Group.relation_set (@BraidMatrixFin n))

def BraidGroupInf.mk := PresentedGroup.mk braidRelationInf

def BraidGroupFin.mk (n : ℕ) := PresentedGroup.mk (braidRelationFin n)

def σ (k : ℕ) : BraidGroupInf := PresentedGroup.of k

def σₙ {n : ℕ} (k : Fin n.pred) : BraidGroupFin n := PresentedGroup.of k

theorem BraidMatrixInf_separated {i j : ℕ} (h : i.dist j ≥ 2) : BraidMatrixInf.1 i j = 2 := by
  unfold BraidMatrixInf
  aesop

theorem BraidMatrixFin_separated {n : ℕ} (i j : Fin n.pred) (h : i.val.dist j ≥ 2) :
    BraidMatrixFin.1 i j = 2 := by
  unfold BraidMatrixFin
  grind [Matrix.of_apply, Nat.dist]

theorem BraidMatrixInf_adjacent {i j : ℕ} (h : i.dist j = 1) : BraidMatrixInf.1 i j = 3 := by
  unfold BraidMatrixInf
  aesop

theorem BraidMatrixInf_adjacent' {i : ℕ} : BraidMatrixInf.1 i (i + 1) = 3 := by
  unfold BraidMatrixInf
  simp [Nat.dist, add_tsub_cancel_left]

theorem BraidMatrixFin_adjacent {n : ℕ} (i j : Fin n.pred) (h : i.val.dist j = 1)  : BraidMatrixFin.1 i j = 3 := by
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
  simp only [Nat.pred_eq_sub_one, BraidMatrixFin_adjacent _ _ hd, Function.uncurry_apply_pair,
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
  simp only [Nat.pred_eq_sub_one, BraidMatrixFin_separated _ _ h, Function.uncurry_apply_pair,
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

-- f satisfies the infinite braid group relations and thus can be lifted to the infinite braid group
def BraidGroupInf.IsLiftable {G : Type*} [Group G] (f : ℕ → G) : Prop :=
  (∀ i j : ℕ, i.dist j = 1 → f i * f j * f i = f j * f i * f j) ∧
  (∀ i j : ℕ, 2 ≤ i.dist j → f i * f j = f j * f i)

private theorem BraidGroupInf.isLiftable_iff {G : Type*} [Group G] {f : ℕ → G} :
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

def BraidGroupInf.toGroup {G : Type*} [Group G] {f : ℕ → G}
    (hf : BraidGroupInf.IsLiftable f) : BraidGroupInf →* G :=
  ArtinTits.toGroup BraidMatrixInf ((BraidGroupInf.isLiftable_iff).mp hf)

theorem BraidGroupInf.toGroup_of {G : Type*} [Group G] {f : ℕ → G}
    (hf : BraidGroupInf.IsLiftable f) (i : ℕ) :
    BraidGroupInf.toGroup hf (σ i) = f i :=
  ArtinTits.toGroup_of BraidMatrixInf ((BraidGroupInf.isLiftable_iff).mp hf)

theorem BraidGroupInf.toGroup_unique {G : Type*} [Group G] {f : ℕ → G}
    (hf : BraidGroupInf.IsLiftable f) (g : BraidGroupInf →* G)
    (hg : ∀ i : ℕ, g (σ i) = f i) : BraidGroupInf.toGroup hf = g :=
  ArtinTits.toGroup_unique BraidMatrixInf g hg _

-- f satisfies finite braid group relations and thus can be lifted to said finite braid group
def BraidGroupFin.IsLiftable (n : ℕ) {G : Type*} [Group G] (f : Fin n.pred → G) : Prop :=
  (∀ i j : Fin n.pred, i.val.dist j.val = 1 → f i * f j * f i = f j * f i * f j) ∧
  (∀ i j : Fin n.pred, 2 ≤ i.val.dist j.val → f i * f j = f j * f i)

private theorem BraidGroupFin.isLiftable_iff (n : ℕ) {G : Type*} [Group G] {f : Fin n.pred → G} :
    BraidGroupFin.IsLiftable n f ↔ ArtinTits.IsLiftable (BraidMatrixFin) f := by
  constructor
  · intro hf
    rcases hf with ⟨hbraid, hcomm⟩
    intro i j
    by_cases h1 : i.val.dist j.val = 1
    · rw [BraidMatrixFin_adjacent i j h1]
      simp [Monoid.alternate_three, hbraid i j h1, mul_assoc]
    · by_cases h2 : 2 ≤ i.val.dist j.val
      · rw [BraidMatrixFin_separated i j h2]
        simp [Monoid.alternate_two, hcomm i j h2]
      grind [Nat.dist]
  · intro hf
    constructor
    · intro i j h
      grind [Monoid.alternate_three, BraidMatrixFin_adjacent, hf i j]
    intro i j h
    grind [Monoid.alternate_two, BraidMatrixFin_separated, hf i j]

def BraidGroupFin.toGroup (n : ℕ) {G : Type*} [Group G] {f : Fin n.pred → G}
    (hf : BraidGroupFin.IsLiftable n f) : BraidGroupFin n →* G :=
  ArtinTits.toGroup (BraidMatrixFin) ((BraidGroupFin.isLiftable_iff n).mp hf)

theorem BraidGroupFin.toGroup_of (n : ℕ) {G : Type*} [Group G] {f : Fin n.pred → G}
    (hf : BraidGroupFin.IsLiftable n f) (i : Fin n.pred) :
    BraidGroupFin.toGroup n hf (σₙ i) = f i :=
  ArtinTits.toGroup_of (BraidMatrixFin) ((BraidGroupFin.isLiftable_iff n).mp hf)

theorem BraidGroupFin.toGroup_unique (n : ℕ) {G : Type*} [Group G] {f : Fin n.pred → G}
    (hf : BraidGroupFin.IsLiftable n f) (g : BraidGroupFin n →* G)
    (hg : ∀ i : Fin n.pred, g (σₙ i) = f i) : BraidGroupFin.toGroup n hf = g :=
  ArtinTits.toGroup_unique (BraidMatrixFin) g hg _

theorem BraidGroupFin.toBraidGroupInf_helper : BraidGroupFin.IsLiftable n (fun x => σ x.1) := by
  constructor
  · intro i j h
    apply BraidGroupInf.braid
    exact h
  intro i j h
  apply BraidGroupInf.comm
  exact h

def BraidGroupFin.toBraidGroupInf (n : ℕ) : BraidGroupFin n →* BraidGroupInf :=
  BraidGroupFin.toGroup n BraidGroupFin.toBraidGroupInf_helper

theorem BraidGroupFin.toBraidGroupInf_one (n : ℕ) : BraidGroupFin.toBraidGroupInf n 1 = 1 := rfl

theorem BraidGroupFin.toBraidGroupInf_of (n : ℕ) (i : Fin n.pred) :
    BraidGroupFin.toBraidGroupInf n (σₙ i) = σ i.1 := rfl

theorem BraidGroupFin.toBraidGroupInf_mk_mk (n : ℕ) (w : List (Fin n.pred × Bool)) :
    BraidGroupFin.toBraidGroupInf n (BraidGroupFin.mk n (FreeGroup.mk w)) =
    BraidGroupInf.mk (FreeGroup.mk (List.map (fun i => (i.1.val, i.2)) w)) := by
  induction w with
  | nil => rfl
  | cons head tail ih =>
    rw [List.map_cons, FreeGroup.mk_cons, map_mul]
    erw [map_mul, ih]
    conv => rhs; rw [FreeGroup.mk_cons, map_mul]
    match head with
    | ⟨hh, true⟩ => rfl
    | (hh, false) => rfl

theorem BraidGroupInf.eq_of_BraidGroupFin_eq_word {n : ℕ} {a b : List (Fin n.pred × Bool)}
    (h : BraidGroupFin.mk n (FreeGroup.mk a) = BraidGroupFin.mk n (FreeGroup.mk b)) :
    BraidGroupInf.mk (FreeGroup.mk (List.map (fun i => (i.1.1, i.2)) a)) =
    BraidGroupInf.mk (FreeGroup.mk (List.map (fun i => (i.1.1, i.2)) b)) := by
  apply congr_arg (BraidGroupFin.toBraidGroupInf n) at h
  rw [BraidGroupFin.toBraidGroupInf_mk_mk, BraidGroupFin.toBraidGroupInf_mk_mk] at h
  exact h

theorem BraidGroupInf.eq_of_BraidGroupFin_eq_word'
    {a b : List (ℕ × Bool)} {n : ℕ} (ha : SignedList.bounded n.pred a) (hb : SignedList.bounded n.pred b)
    (h1 : BraidGroupFin.mk n (.mk (SignedList.mapNatToFin a n.pred ha)) =
      BraidGroupFin.mk n (.mk (SignedList.mapNatToFin b n.pred hb))) :
    BraidGroupInf.mk (.mk a) = BraidGroupInf.mk (.mk b) := by
  rw [← SignedList.mapNatToFin_map_val a ha, ← SignedList.mapNatToFin_map_val b hb]
  exact BraidGroupInf.eq_of_BraidGroupFin_eq_word h1

theorem BraidGroupInf.eq_of_BraidGroupFin_eq_free_group_elem {n : ℕ}
    {a b : FreeGroup (Fin n.pred)}
    (h : BraidGroupFin.mk n a = BraidGroupFin.mk n b) :
    BraidGroupInf.mk (FreeGroup.map Fin.val a) =
    BraidGroupInf.mk (FreeGroup.map Fin.val b) := by
  rcases FreeGroup.exists_rep a with ⟨a', rfl⟩
  rcases FreeGroup.exists_rep b with ⟨b', rfl⟩
  exact BraidGroupInf.eq_of_BraidGroupFin_eq_word h

theorem BraidGroupFin.toLargerBraidGroupFin_helper (h : n.pred < m.pred) : BraidGroupFin.IsLiftable n (fun x => (σₙ ⟨x.1, Nat.lt_trans x.2 h⟩ : BraidGroupFin m)) := by
  constructor
  · intro i j h
    apply BraidGroupFin.braid
    exact h
  intro i j h
  apply BraidGroupFin.comm
  exact h

def BraidGroupFin.toLargerBraidGroupFin {n m : ℕ} (h : n.pred < m.pred) : BraidGroupFin n →* BraidGroupFin m :=
  BraidGroupFin.toGroup n (BraidGroupFin.toLargerBraidGroupFin_helper h)

theorem BraidGroupFin.toLargerBraidGroupFin_one  {n m : ℕ} (h : n.pred < m.pred) : BraidGroupFin.toLargerBraidGroupFin h 1 = 1 := rfl

theorem BraidGroupFin.toLargerBraidGroupFin_of {n m : ℕ} (h : n.pred < m.pred) (i : Fin n.pred) :
    BraidGroupFin.toLargerBraidGroupFin h (σₙ i) = σₙ (⟨i.1, Nat.lt_trans i.2 h⟩ : Fin m.pred) := rfl

theorem BraidGroupFin.toLargerBraidGroupFin_mk_mk {n m : ℕ} (h : n.pred < m.pred) (w : List (Fin n.pred × Bool)) :
    BraidGroupFin.toLargerBraidGroupFin h (BraidGroupFin.mk n (FreeGroup.mk w)) =
    BraidGroupFin.mk m (FreeGroup.mk (List.map (fun i => (⟨i.1.val, Nat.lt_trans i.1.2 h⟩, i.2)) w)) := by
  induction w with
  | nil => rfl
  | cons head tail ih =>
    rw [List.map_cons, FreeGroup.mk_cons, map_mul]
    erw [map_mul, ih]
    conv => rhs; rw [FreeGroup.mk_cons, map_mul]
    match head with
    | ⟨hh, true⟩ => rfl
    | (hh, false) => rfl

theorem BraidGroupFin.eq_of_SmallerBraidGroupFin_eq {n m : ℕ} (h : n.pred < m.pred) {a b : List (Fin n.pred × Bool)}
    (h1 : BraidGroupFin.mk n (FreeGroup.mk a) = BraidGroupFin.mk n (FreeGroup.mk b)) :
    BraidGroupFin.mk m (FreeGroup.mk (List.map (fun i => (⟨i.1.val, Nat.lt_trans i.1.2 h⟩, i.2)) a)) =
    BraidGroupFin.mk m (FreeGroup.mk (List.map (fun i => (⟨i.1.val, Nat.lt_trans i.1.2 h⟩, i.2)) b)) := by
  apply congr_arg (BraidGroupFin.toLargerBraidGroupFin h) at h1
  rw [BraidGroupFin.toLargerBraidGroupFin_mk_mk, BraidGroupFin.toLargerBraidGroupFin_mk_mk] at h1
  exact h1

theorem BraidGroupFin.eq_of_SmallerBraidGroupFin_eq' {n m : ℕ} (h : n.pred < m.pred) {a b : List (ℕ × Bool)}
    (ha : SignedList.bounded n.pred a) (hb : SignedList.bounded n.pred b)
    (h1 : BraidGroupFin.mk n (.mk (SignedList.mapNatToFin a n.pred ha)) =
      BraidGroupFin.mk n (.mk (SignedList.mapNatToFin b n.pred hb))) :
    BraidGroupFin.mk m (.mk (SignedList.mapNatToFin
      (a) m.pred
      (SignedList.bounded_trans ha h)) ) =
    BraidGroupFin.mk m (.mk (SignedList.mapNatToFin
      (b) m.pred (SignedList.bounded_trans hb h)) ) := by
  have := BraidGroupFin.eq_of_SmallerBraidGroupFin_eq h h1
  convert this
  · clear b hb h1 this
    induction a with
    | nil => rfl
    | cons head tail ih =>
      rw [SignedList.mapNatToFin_cons (SignedList.bounded_trans ha h)
        (SignedList.bounded_trans ((SignedList.bounded_tail ha)) h), SignedList.mapNatToFin_cons ha,
        List.map_cons, ih (SignedList.bounded_tail ha)]
  clear a ha h1 this
  induction b with
  | nil => rfl
  | cons head tail ih =>
    rw [SignedList.mapNatToFin_cons (SignedList.bounded_trans hb h)
      (SignedList.bounded_trans ((SignedList.bounded_tail hb)) h), SignedList.mapNatToFin_cons hb,
      List.map_cons, ih (SignedList.bounded_tail hb)]


end Braid
