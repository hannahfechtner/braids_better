import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Dist
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric
import BraidProject.Additions.Monoid
import BraidProject.PresentedMonoid_mine

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

def Group.relation (s t : α) : FreeGroup (α) :=
  Monoid.alternate (.of s) (.of t) (M s t) * (Monoid.alternate (.of t) (.of s) (M s t))⁻¹

def Group.relation_set : Set (FreeGroup α) :=
  Set.range (Function.uncurry (Group.relation M))

theorem Group.mem_relation_set_iff {r : FreeGroup α} :
    r ∈ Group.relation_set M ↔ ∃ i j, Group.relation M i j = r := by
  constructor
  · intro hr
    rcases hr with ⟨⟨i, j⟩, h⟩
    grind
  rintro ⟨i, j, rfl⟩
  exact ⟨⟨i, j⟩, rfl⟩

def ArtinTitsGroup := PresentedGroup (Group.relation_set M)

instance {M : ArtinTitsMatrix α} : Group (ArtinTitsGroup M):= by
  unfold ArtinTitsGroup; infer_instance

/-- A map `f : α → G` is *liftable* if it satisfies all Artin-Tits relations determined by `M`. -/
def IsLiftable {G : Type*} [Group G] (f : α → G) : Prop :=
  ∀ i j, Monoid.alternate (f i) (f j) (M i j) = Monoid.alternate (f j) (f i) (M i j)

private theorem relations_liftable {G : Type*} [Group G] {f : α → G} (hf : IsLiftable M f)
    (r : FreeGroup α) (hr : r ∈ Group.relation_set M) : (FreeGroup.lift f) r = 1 := by
  rcases hr with ⟨⟨i, j⟩, rfl⟩
  rw [Function.uncurry, Group.relation, map_mul, map_inv, Monoid.lift_group_alternate, Monoid.lift_group_alternate,
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

def Monoid.relation (M : ArtinTitsMatrix α) (s t : α) :
    FreeMonoid α × FreeMonoid α :=
  (Monoid.alternate (.of s) (.of t) (M s t),
   Monoid.alternate (.of t) (.of s) (M s t))

def Monoid.relations (M : ArtinTitsMatrix α) :
    FreeMonoid α → FreeMonoid α → Prop :=
  fun a b => ∃ i j, Monoid.relation M i j = (a, b)

def ArtinTitsMonoid (M : ArtinTitsMatrix α) :=
  PresentedMonoid (Monoid.relations M)

instance {M : ArtinTitsMatrix α} : Monoid (ArtinTitsMonoid M):= by
  unfold ArtinTitsMonoid; infer_instance

/-- A map `f : α → G` is *liftable* if it satisfies all Artin-Tits relations determined by `M`. -/
def Monoid.IsLiftable {G : Type*} [Monoid G] (f : α → G) : Prop :=
  ∀ i j, Monoid.alternate (f i) (f j) (M i j) = Monoid.alternate (f j) (f i) (M i j)

private theorem Monoid.relations_liftable {G : Type*} [Monoid G] {f : α → G} (hf : Monoid.IsLiftable M f)
    (r₁ r₂ : FreeMonoid α) (hr : Monoid.relations M r₁ r₂) : (FreeMonoid.lift f) r₁ = FreeMonoid.lift f r₂ := by
  rcases hr with ⟨i, j, hij⟩
  specialize hf i j
  grind [Monoid.lift_monoid_alternate, FreeMonoid.lift_eval_of, Monoid.relation]

/-- The extension of a map `f : α → G` that satisfies the given relations to a group homomorphism
from `ArtinTitsGroup rels → G`. -/
def toMonoid  {G : Type*} [Monoid G] {f : α → G} (M : ArtinTitsMatrix α) (hf : Monoid.IsLiftable M f) :
  ArtinTitsMonoid M →* G := (PresentedMonoid.toMonoid _ (Monoid.relations_liftable M hf))

theorem toMonoid_of {G : Type*} [Monoid G] {f : α → G} (M : ArtinTitsMatrix α)
    (hf : Monoid.IsLiftable M f)  : toMonoid M hf (PresentedMonoid.of _ i) = f i := PresentedMonoid.toMonoid.of _ _

theorem toMonoid_unique {G : Type*} [Monoid G] {f : α → G} (M : ArtinTitsMatrix α)
    (g : ArtinTitsMonoid M →* G) (hg : ∀ (x : α), g (PresentedMonoid.of _ x) = f x)
    (hf : Monoid.IsLiftable M f) : toMonoid M hf = g :=
    (PresentedMonoid.toMonoid.unique _ (Monoid.relations_liftable M hf) g hg).symm
