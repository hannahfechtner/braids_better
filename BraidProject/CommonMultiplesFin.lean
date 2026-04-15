import BraidProject.ConvertToFin
import BraidProject.FlipBraid'

theorem FreeMonoid.mapNatToFin_map_val_mul_right :
    FreeMonoid.mapNatToFin n (FreeMonoid.map (fun i => i.val) u  *  v') bounded_a =
    u * FreeMonoid.mapNatToFin n v' v'_bound := by
  conv =>
  {
    enter [1]
    apply FreeMonoid.mapNatToFin_mul (FreeMonoid.map (fun i => i.val) u) v'
      (FreeMonoid.lt_of_mem_map_val u) v'_bound
  }
  simp only [mul_left_inj]
  apply FreeMonoid.mapNatToFin_map_val

theorem rel_restriction {n : ℕ} (u v : FreeMonoid (Fin n)) (u' v' : FreeMonoid ℕ)
    (u'_bound : ∀ x ∈ u', x < n) (v'_bound : ∀ x ∈ v', x < n)
    (br_inf_holds : BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) u * v') =
    BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) v  *  u')) :
    BraidMonoid.mk _ (u  *  FreeMonoid.mapNatToFin n v' v'_bound) =
    BraidMonoid.mk _ (v  *  FreeMonoid.mapNatToFin n u' u'_bound) := by
  rw [← FreeMonoid.mapNatToFin_map_val_mul_right, ← FreeMonoid.mapNatToFin_map_val_mul_right]
  apply braid_rel_inf_to_fin n (FreeMonoid.map (fun i => i.val) u  *  v') (FreeMonoid.map (fun i => i.val) v  *  u') _ _ br_inf_holds
  · intro x is_in
    simp only [FreeMonoid.mem_mul, FreeMonoid.mem_map] at is_in
    rcases is_in
    · next exists_thing =>
      rcases exists_thing with ⟨m, hm⟩
      rw [← hm.2]
      exact m.isLt
    exact v'_bound _ (by assumption)
  intro x is_in
  simp only [FreeMonoid.mem_mul] at is_in
  rcases is_in
  · next h =>
    rcases FreeMonoid.mem_map.mp h with ⟨a, eq_x⟩
    rw [← eq_x.2]
    exact a.isLt
  exact u'_bound _ (by assumption)

theorem common_right_mul_souped_two {a : ℕ} (u v : FreeMonoid (Fin a)) (n : ℕ)
  (bound : ∀ x : ℕ, (x∈ FreeMonoid.map (λ i : Fin a => i.val) (u) ∨ x ∈ (FreeMonoid.map (λ i : Fin a => i.val) v)) →  x<n) :
    ∃ (u' v' : FreeMonoid ℕ ), (BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) u) * v') = BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) v) * u')) ∧
    (∀ x, (x∈ u' ∨ x ∈ v') →  x < n) := by
  let new_u := (FreeMonoid.map (λ i : Fin a => i.val) u)
  let new_v := (FreeMonoid.map (λ i : Fin a => i.val) v)
  have u_length := Nat.le_max_left (FreeMonoid.length new_u) (FreeMonoid.length new_v)
  have v_length := Nat.le_max_right (FreeMonoid.length new_u) (FreeMonoid.length new_v)
  rcases (equiv_multiple_delta_braid new_u (Nat.max (FreeMonoid.length new_u) (FreeMonoid.length new_v)) n
    u_length (fun x h => bound x (Or.inl h))) with ⟨u', hu', u'_bound⟩
  rcases (equiv_multiple_delta_braid new_v (Nat.max (FreeMonoid.length new_u) (FreeMonoid.length new_v)) n
    v_length (fun x h => bound x (Or.inr h))) with ⟨v', hv', v'_bound⟩
  use v', u'
  grind

theorem common_right_mul_souped_three {a : ℕ} (u v : FreeMonoid (Fin a)) :
    ∃ (u' v' : FreeMonoid ℕ), (BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) u) * v')
    = BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a => i.val) v) * u')) ∧
    (∀ x, (x∈ u' ∨ x ∈ v') →  x < a) := by
  have bounded_helper : ∀ x : ℕ, (x ∈ FreeMonoid.map (λ i => i.val) u ∨
      x ∈ FreeMonoid.map (λ i => i.val) v) → x < a := by
    intro x h
    rcases h
    · next in_u =>
      rcases FreeMonoid.mem_map.mp in_u with ⟨a', _, bound_a⟩
      rw [← bound_a]
      exact a'.isLt
    next in_v =>
    rcases FreeMonoid.mem_map.mp in_v with ⟨b', _, bound_b⟩
    rw [← bound_b]
    exact b'.isLt
  exact common_right_mul_souped_two u v a bounded_helper

theorem common_right_mul_fin {n : ℕ} (u v : FreeMonoid (Fin n)) :
    ∃ u' v', (BraidMonoid.mk _ (u * v') = BraidMonoid.mk _ (v * u')) := by
  rcases common_right_mul_souped_three u v with ⟨u', v', huv'⟩
  use (FreeMonoid.mapNatToFin n u' (fun t t_h => huv'.right t (Or.inl t_h)))
  use (FreeMonoid.mapNatToFin n v' (fun t t_h => huv'.right t (Or.inr t_h)))
  exact rel_restriction _ _ _ _ _ _ huv'.1
