import BraidProject.ConvertToFin
import BraidProject.CommonMultiples

open Braid

theorem BraidMonoidFin.eq_of_BraidMonoidInf_mul_eq {n : ℕ} (u v : FreeMonoid (Fin n.pred)) (u' v' : FreeMonoid ℕ)
    (u'_bound : ∀ x ∈ u', x < n.pred) (v'_bound : ∀ x ∈ v', x < n.pred)
    (br_inf_holds : BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) u * v') =
    BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) v  *  u')) :
    BraidMonoidFin.mk _ (u  *  FreeMonoid.mapNatToFin n.pred v' v'_bound) =
    BraidMonoidFin.mk _ (v  *  FreeMonoid.mapNatToFin n.pred u' u'_bound) := by
  rw [← FreeMonoid.mapNatToFin_map_val_mul_right, ← FreeMonoid.mapNatToFin_map_val_mul_right]
  apply BraidMonoidFin.eq_of_BraidMonoidInf_eq _ _ _ _ _ br_inf_holds
  all_goals grind [FreeMonoid.mem_mul, FreeMonoid.mem_map]

theorem common_right_mul_inf_of_fin {a : ℕ} (u v : FreeMonoid (Fin a)) :
    ∃ (u' v' : FreeMonoid ℕ ),
    (BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) u) * v') =
    BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) v) * u')) ∧
    (∀ x, (x ∈ u' ∨ x ∈ v') →  x < a) := by
  have bound : ∀ x : ℕ, (x∈ FreeMonoid.map (λ i : Fin a => i.val) (u) ∨ x ∈ (FreeMonoid.map (λ i : Fin a => i.val) v)) →  x< a := by grind [FreeMonoid.mem_map]
  let new_u := (FreeMonoid.map (λ i : Fin a => i.val) u)
  let new_v := (FreeMonoid.map (λ i : Fin a => i.val) v)
  rcases (equiv_multiple_delta_braid new_u (Nat.max (FreeMonoid.length new_u) (FreeMonoid.length new_v))
    a (by aesop) (by grind)) with ⟨u', hu', u'_bound⟩
  rcases (equiv_multiple_delta_braid new_v (Nat.max (FreeMonoid.length new_u) (FreeMonoid.length new_v))
    a (by aesop) (by grind)) with ⟨v', hv', v'_bound⟩
  use v', u'
  grind

theorem BraidMonoidFin.common_right_mul_mk {n : ℕ} (u v : FreeMonoid (Fin n.pred)) :
    ∃ u' v', (BraidMonoidFin.mk _ (u * v') = BraidMonoidFin.mk _ (v * u')) := by
  rcases common_right_mul_inf_of_fin u v with ⟨u', v', huv'⟩
  use (FreeMonoid.mapNatToFin n.pred u' (fun t t_h => huv'.right t (Or.inl t_h)))
  use (FreeMonoid.mapNatToFin n.pred v' (fun t t_h => huv'.right t (Or.inr t_h)))
  exact BraidMonoidFin.eq_of_BraidMonoidInf_mul_eq _ _ _ _ _ _ huv'.1

theorem BraidMonoidFin.common_right_mul {n : ℕ} (u v : BraidMonoidFin n) :
      ∃ u' v', u * u' = v * v' := by
  induction u with | h u =>
  induction v with | h v =>
  rcases BraidMonoidFin.common_right_mul_mk u v with ⟨v', u', huv'⟩
  use (PresentedMonoid.mk (braid_monoid_rels_fin n)) u', (PresentedMonoid.mk (braid_monoid_rels_fin n)) v'
  exact huv'

theorem BraidMonoidFin.common_left_mul {n : ℕ} (u v : BraidMonoidFin n) :
      ∃ u' v', u' * u = v' * v := by
  rcases BraidMonoidFin.common_right_mul u.reverse_braid v.reverse_braid with ⟨u', v', huv'⟩
  use u'.reverse_braid, v'.reverse_braid
  apply congr_arg BraidMonoidFin.reverse_braid at huv'
  simp only [BraidMonoidFin.reverse_braid_mul, BraidMonoidFin.reverse_reverse] at huv'
  exact huv'

instance {n : ℕ} : IsCommonRightMultipleMul (BraidMonoidFin n) := ⟨fun _ _ => BraidMonoidFin.common_right_mul _ _⟩

instance {n : ℕ} : IsCommonLeftMultipleMul (BraidMonoidFin n) := ⟨fun _ _ => BraidMonoidFin.common_left_mul _ _⟩

theorem BraidMonoidFin'.eq_of_BraidMonoidInf_mul_eq {n : ℕ} (u v : FreeMonoid (Fin n.pred)) (u' v' : FreeMonoid ℕ)
    (u'_bound : ∀ x ∈ u', x < n.pred) (v'_bound : ∀ x ∈ v', x < n.pred)
    (br_inf_holds : BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) u * v') =
    BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) v  *  u')) :
    BraidMonoidFin'.mk _ (u  *  FreeMonoid.mapNatToFin n.pred v' v'_bound) =
    BraidMonoidFin'.mk _ (v  *  FreeMonoid.mapNatToFin n.pred u' u'_bound) := by
  rw [← FreeMonoid.mapNatToFin_map_val_mul_right, ← FreeMonoid.mapNatToFin_map_val_mul_right]
  apply BraidMonoidFin'.eq_of_BraidMonoidInf_eq _ _ _ _ _ br_inf_holds
  all_goals grind [FreeMonoid.mem_mul, FreeMonoid.mem_map]

theorem common_right_mul_inf_of_fin' {a : ℕ} (u v : FreeMonoid (Fin a)) :
    ∃ (u' v' : FreeMonoid ℕ ),
    (BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) u) * v') =
    BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) v) * u')) ∧
    (∀ x, (x ∈ u' ∨ x ∈ v') →  x < a) := by
  have bound : ∀ x : ℕ, (x∈ FreeMonoid.map (λ i : Fin a => i.val) (u) ∨ x ∈ (FreeMonoid.map (λ i : Fin a => i.val) v)) →  x< a := by grind [FreeMonoid.mem_map]
  let new_u := (FreeMonoid.map (λ i : Fin a => i.val) u)
  let new_v := (FreeMonoid.map (λ i : Fin a => i.val) v)
  rcases (equiv_multiple_delta_braid new_u (Nat.max (FreeMonoid.length new_u) (FreeMonoid.length new_v))
    a (by aesop) (by grind)) with ⟨u', hu', u'_bound⟩
  rcases (equiv_multiple_delta_braid new_v (Nat.max (FreeMonoid.length new_u) (FreeMonoid.length new_v))
    a (by aesop) (by grind)) with ⟨v', hv', v'_bound⟩
  use v', u'
  grind

theorem BraidMonoidFin'.common_right_mul_mk {n : ℕ} (u v : FreeMonoid (Fin n.pred)) :
    ∃ u' v', (BraidMonoidFin'.mk _ (u * v') = BraidMonoidFin'.mk _ (v * u')) := by
  rcases common_right_mul_inf_of_fin u v with ⟨u', v', huv'⟩
  use (FreeMonoid.mapNatToFin n.pred u' (fun t t_h => huv'.right t (Or.inl t_h)))
  use (FreeMonoid.mapNatToFin n.pred v' (fun t t_h => huv'.right t (Or.inr t_h)))
  exact BraidMonoidFin'.eq_of_BraidMonoidInf_mul_eq _ _ _ _ _ _ huv'.1

theorem BraidMonoidFin'.common_right_mul {n : ℕ} (u v : BraidMonoidFin' n) :
      ∃ u' v', u * u' = v * v' := by
  induction u with | h u =>
  induction v with | h v =>
  rcases BraidMonoidFin'.common_right_mul_mk u v with ⟨v', u', huv'⟩
  use (PresentedMonoid.mk (braid_monoid_rels_fin' n)) u', (PresentedMonoid.mk (braid_monoid_rels_fin' n)) v'
  exact huv'

theorem BraidMonoidFin'.common_left_mul {n : ℕ} (u v : BraidMonoidFin' n) :
      ∃ u' v', u' * u = v' * v := by
  rcases BraidMonoidFin'.common_right_mul u.reverse_braid v.reverse_braid with ⟨u', v', huv'⟩
  use u'.reverse_braid, v'.reverse_braid
  apply congr_arg BraidMonoidFin'.reverse_braid at huv'
  simp only [BraidMonoidFin'.reverse_braid_mul, BraidMonoidFin'.reverse_reverse] at huv'
  exact huv'

instance {n : ℕ} : IsCommonRightMultipleMul (BraidMonoidFin' n) := ⟨fun _ _ => BraidMonoidFin'.common_right_mul _ _⟩

instance {n : ℕ} : IsCommonLeftMultipleMul (BraidMonoidFin' n) := ⟨fun _ _ => BraidMonoidFin'.common_left_mul _ _⟩
