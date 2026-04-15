import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Dist
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric
import BraidProject.Additions.Group

namespace ArtinTits

/-- An *Artin-Tits matrix* is a symmetric matrix of natural numbers whose diagonal entries are equal to
0 and whose off-diagonal entries are not equal to 1. -/
@[ext]
structure ArtinTitsMatrix (α : Type*) where
  M : Matrix α α ℕ
  isSymm : M.IsSymm := by decide
  off_diagonal i i' : i ≠ i' → M i i' ≠ 1 := by decide

variable {α : Type*}

/-- An Artin-Tits matrix can be coerced to a matrix. -/
instance : CoeFun (ArtinTitsMatrix α) fun _ ↦ (Matrix α α ℕ) := ⟨ArtinTitsMatrix.M⟩

variable (M : ArtinTitsMatrix α)

theorem symmetric (i i' : α) : M i i' = M i' i := M.isSymm.apply i' i

def relation (s t : α) : FreeGroup (α) :=
  Group.alternate (.of s) (.of t) (M s t) * (Group.alternate (.of t) (.of s) (M s t))⁻¹

def relation_set : Set (FreeGroup α) :=
  Set.range (Function.uncurry (relation M))

theorem mem_relation_set_iff {r : FreeGroup α} :
    r ∈ relation_set M ↔ ∃ i j, relation M i j = r := by
  constructor
  · intro hr
    rcases hr with ⟨⟨i, j⟩, h⟩
    grind
  rintro ⟨i, j, rfl⟩
  exact ⟨⟨i, j⟩, rfl⟩

def ArtinTitsGroup := PresentedGroup (relation_set M)

instance {M : ArtinTitsMatrix α} : Group (ArtinTitsGroup M):= by
  unfold ArtinTitsGroup; infer_instance

/-- A map `f : α → G` is *liftable* if it satisfies all Artin-Tits relations determined by `M`. -/
def IsLiftable {G : Type*} [Group G] (f : α → G) : Prop :=
  ∀ i j, Group.alternate (f i) (f j) (M i j) = Group.alternate (f j) (f i) (M i j)

private theorem relations_liftable {G : Type*} [Group G] {f : α → G} (hf : IsLiftable M f)
    (r : FreeGroup α) (hr : r ∈ relation_set M) : (FreeGroup.lift f) r = 1 := by
  rcases hr with ⟨⟨i, j⟩, rfl⟩
  rw [Function.uncurry, relation, map_mul, map_inv, Group.lift_alternate, Group.lift_alternate,
      FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, hf i j, mul_inv_cancel]

/-- The extension of a map `f : α → G` that satisfies the given relations to a group homomorphism
from `ArtinTitsGroup rels → G`. -/
def toGroup  {G : Type*} [Group G] {f : α → G} (M : ArtinTitsMatrix α) (hf : IsLiftable M f) :
  ArtinTitsGroup M →* G := (PresentedGroup.toGroup (relations_liftable M hf))

theorem toGroup_of {G : Type*} [Group G] {f : α → G} (M : ArtinTitsMatrix α)
    (hf : IsLiftable M f)  : toGroup M hf (.of i) = f i := PresentedGroup.toGroup.of _

theorem toGroup_unique {G : Type*} [Group G] {f : α → G} (M : ArtinTitsMatrix α)
    (g : ArtinTitsGroup M →* G) (hg : ∀ (x : α), g (PresentedGroup.of x) = f x)
    (hf : IsLiftable M f) : toGroup M hf = g :=
  MonoidHom.ext fun _ ↦ (PresentedGroup.toGroup.unique (relations_liftable M hf) g hg).symm
