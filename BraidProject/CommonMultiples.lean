import BraidProject.FlipBraid'
import BraidProject.Additions.Mixins

open FreeMonoid Braid

theorem common_right_mul_inf (u v : BraidMonoidInf) : ∃ v' u', u * v' = v * u' := by
  induction u with | h u
  induction v with | h v
  rcases (FreeMonoid.bounded u) with ⟨k1, hk1⟩
  rcases (FreeMonoid.bounded v) with ⟨k2, hk2⟩
  rcases (equiv_multiple_delta_braid u (Nat.max (FreeMonoid.length u) (FreeMonoid.length v)) (Nat.max k1 k2)
    (by aesop) (by aesop)) with ⟨v', hv', _⟩
  rcases (equiv_multiple_delta_braid v (Nat.max (FreeMonoid.length u) (FreeMonoid.length v)) (Nat.max k1 k2)
    (by aesop) (by aesop)) with ⟨u', hu', _⟩
  exact .intro ⟦v'⟧ (.intro ⟦u'⟧ (hv'.trans hu'.symm))

theorem common_right_mul_inf_mk (u v) : ∃ v' u', BraidMonoidInf.mk (u*v') = ⟦v*u'⟧ := by
  rcases common_right_mul_inf ⟦u⟧ ⟦v⟧ with ⟨u', v', huv⟩
  induction u' with | h u''
  induction v' with | h v''
  use u'', v''
  exact huv

theorem common_left_mul_inf (u v : BraidMonoidInf) : ∃ u' v', u' * u = v' * v := by
  rcases common_right_mul_inf (BraidMonoidInf.reverse_braid u)
    (BraidMonoidInf.reverse_braid v) with ⟨a, b, hab⟩
  use BraidMonoidInf.reverse_braid a, BraidMonoidInf.reverse_braid b
  have := congr_arg BraidMonoidInf.reverse_braid hab
  simp only [BraidMonoidInf.reverse_braid_mul, BraidMonoidInf.reverse_reverse] at this
  simp [this]

instance : IsCommonLeftMultipleMul (BraidMonoidInf) where
  common_left_multiple := common_left_mul_inf

instance : IsCommonRightMultipleMul (BraidMonoidInf) where
  common_right_multiple := common_right_mul_inf
