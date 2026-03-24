import Mathlib.GroupTheory.OreLocalization.Basic

theorem numeratorHom_injective_of_cancellative (R : Type*) [Monoid R] [IsLeftCancelMul R]
  (S : Submonoid R) [OreLocalization.OreSet S] : Function.Injective
  (OreLocalization.numeratorHom : R → OreLocalization S R) := by
    intro x y hxy
    rcases Quotient.exact hxy with ⟨a, b, hab⟩
    aesop
