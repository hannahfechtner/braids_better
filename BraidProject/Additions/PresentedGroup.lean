import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.PresentedGroup
namespace PresentedGroup

def free_group_set_of_function (rels : FreeMonoid α → FreeMonoid α → Prop) : Set (FreeGroup α) :=
  {FreeMonoid.lift (FreeGroup.of) x.1 * (FreeMonoid.lift (FreeGroup.of) x.2)⁻¹ |
  x ∈ setOf (fun (a : FreeMonoid α × FreeMonoid α) => rels a.1 a.2)}

theorem mk_eq_lift_of  (rels : Set (FreeGroup α)) :
  PresentedGroup.mk rels = FreeGroup.lift PresentedGroup.of :=
  FreeGroup.ext_hom _ _ (congrFun rfl)

end PresentedGroup
