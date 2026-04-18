import BraidProject.ConvertToFin
import BraidProject.FlipBraid'

open Braid

theorem BraidMonoidFin.eq_of_BraidMonoidInf_mul_eq {n : ℕ} (u v : FreeMonoid (Fin n)) (u' v' : FreeMonoid ℕ)
    (u'_bound : ∀ x ∈ u', x < n) (v'_bound : ∀ x ∈ v', x < n)
    (br_inf_holds : BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) u * v') =
    BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) v  *  u')) :
    BraidMonoidFin.mk _ (u  *  FreeMonoid.mapNatToFin n v' v'_bound) =
    BraidMonoidFin.mk _ (v  *  FreeMonoid.mapNatToFin n u' u'_bound) := by
  rw [← FreeMonoid.mapNatToFin_map_val_mul_right, ← FreeMonoid.mapNatToFin_map_val_mul_right]
  apply BraidMonoidFin.eq_of_BraidMonoidInf_eq _ _ _ _ _ br_inf_holds
  all_goals grind [FreeMonoid.mem_mul, FreeMonoid.mem_map]

theorem common_right_mul_souped_two {a : ℕ} (u v : FreeMonoid (Fin a)) :
    ∃ (u' v' : FreeMonoid ℕ ), (BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) u) * v') = BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) v) * u')) ∧
    (∀ x, (x∈ u' ∨ x ∈ v') →  x < a) := by
  have bound : ∀ x : ℕ, (x∈ FreeMonoid.map (λ i : Fin a => i.val) (u) ∨ x ∈ (FreeMonoid.map (λ i : Fin a => i.val) v)) →  x< a := by grind [FreeMonoid.mem_map]
  let new_u := (FreeMonoid.map (λ i : Fin a => i.val) u)
  let new_v := (FreeMonoid.map (λ i : Fin a => i.val) v)
  rcases (equiv_multiple_delta_braid new_u (Nat.max (FreeMonoid.length new_u) (FreeMonoid.length new_v))
    a (by aesop) (by grind)) with ⟨u', hu', u'_bound⟩
  rcases (equiv_multiple_delta_braid new_v (Nat.max (FreeMonoid.length new_u) (FreeMonoid.length new_v))
    a (by aesop) (by grind)) with ⟨v', hv', v'_bound⟩
  use v', u'
  grind

theorem common_right_mul_fin {n : ℕ} (u v : FreeMonoid (Fin n)) :
    ∃ u' v', (BraidMonoidFin.mk _ (u * v') = BraidMonoidFin.mk _ (v * u')) := by
  rcases common_right_mul_souped_two u v with ⟨u', v', huv'⟩
  use (FreeMonoid.mapNatToFin n u' (fun t t_h => huv'.right t (Or.inl t_h)))
  use (FreeMonoid.mapNatToFin n v' (fun t t_h => huv'.right t (Or.inr t_h)))
  exact BraidMonoidFin.eq_of_BraidMonoidInf_mul_eq _ _ _ _ _ _ huv'.1
