import BraidProject.Cancellability
import BraidProject.ConvertToFin

theorem braid_rels_fininf {x y : FreeMonoid (Fin n)} (br : BraidMonoid.braid_monoid_rels_fin n x y) :
    braid_monoid_rels_inf ((FreeMonoid.map fun i ↦ ↑i) x) ((FreeMonoid.map fun i ↦ ↑i) y) := by
  cases n with
  | zero => exact br.elim
  | succ n =>
    cases n with
    | zero => exact br.elim
    | succ n =>
      rcases br with h1 | h2
      · exact braid_monoid_rels_inf.adjacent ↑h1
      rename_i j j_is
      refine braid_monoid_rels_inf.separated (↑h2) (j + 1 + 1) <| Nat.add_le_add_right j_is 2

theorem braid_rel_fin_to_inf (n : ℕ) (a b : FreeMonoid (Fin n))
    (h : BraidMonoid.mk _ a = BraidMonoid.mk _ b) :
    BraidMonoidInf.mk (FreeMonoid.map (λ i : Fin n => i.val) a) =
    BraidMonoidInf.mk (FreeMonoid.map (λ i : Fin n => i.val) b) := by
  induction (BraidMonoid.exact h) with
  | of x y br =>
    apply BraidMonoidInf.sound
    apply PresentedMonoid.rels_alone
    exact braid_rels_fininf br
  | refl x => rfl
  | symm _ ih =>
    specialize ih h.symm
    exact ih.symm
  | trans xy yz ih1 ih2 =>
    rename_i x y z
    apply BraidMonoid.sound at xy
    apply BraidMonoid.sound at yz
    specialize ih1 xy
    specialize ih2 yz
    exact ih1.trans ih2
  | mul wx yz ih1 ih2 =>
    apply BraidMonoid.sound at wx
    apply BraidMonoid.sound at yz
    specialize ih1 wx
    specialize ih2 yz
    rw [map_mul, map_mul, map_mul]
    exact BraidMonoidInf.concat_mk ih1 ih2

theorem cancel_souped_three {a : ℕ} (c d e : FreeMonoid (Fin a.pred))
    (h : BraidMonoid.mk _ (c * e) = BraidMonoid.mk _ (d * e)) :
    (BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a.pred => i.val) c))
    = BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a.pred => i.val) d))) := by
  have := braid_rel_fin_to_inf _ _ _ h
  rw [map_mul, map_mul, map_mul] at this
  apply right_cancellative this

theorem rel_restriction_wider {n : ℕ} (c d : FreeMonoid (Fin n))
    (br_inf_holds : BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) c) =
    BraidMonoidInf.mk (FreeMonoid.map (fun i => i.val) d)) :
    BraidMonoid.mk _ c = BraidMonoid.mk _ d := by
  rw [← FreeMonoid.mapNatToFin_map_val c, ← FreeMonoid.mapNatToFin_map_val d]
  exact braid_rel_inf_to_fin n (FreeMonoid.map (fun i => i.val) c)
    (FreeMonoid.map (fun i => i.val) d) (FreeMonoid.lt_of_mem_map_val c)
    (FreeMonoid.lt_of_mem_map_val d) br_inf_holds

theorem cancel_fin {n : ℕ} (a b c : FreeMonoid (Fin n.pred)) (h : BraidMonoid.mk _ (a * c) =
    BraidMonoid.mk _ (b * c)) : BraidMonoid.mk _ a  = BraidMonoid.mk _ b :=
  rel_restriction_wider a b (cancel_souped_three a b c h)
