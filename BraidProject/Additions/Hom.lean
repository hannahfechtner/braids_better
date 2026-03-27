import Mathlib.Algebra.Group.Hom.Defs

namespace MulHom
theorem comp_toFun {α β γ : Type*} [Mul α] [Mul β] [Mul γ] {ab : MulHom α β}
    {bc : MulHom β γ} {ac : MulHom α γ} (h : MulHom.comp bc ab = ac) :
    bc.toFun ∘ ab.toFun = ac.toFun:=
  funext fun x ↦ ((congrArg (fun y ↦ (bc ∘ ab) x = y x) h.symm)).mpr rfl

end MulHom

namespace MonoidHom
theorem comp_toFun {α β γ : Type*} [Monoid α] [Monoid β] [Monoid γ] {ab : MonoidHom α β}
    {bc : MonoidHom β γ} {ac : MonoidHom α γ} (h : MonoidHom.comp bc ab = ac) :
    bc.toFun ∘ ab.toFun = ac.toFun:=
  funext fun x ↦ ((congrArg (fun y ↦ (bc ∘ ab) x = y x) h.symm)).mpr rfl

end MonoidHom
