import BraidProject.Solver.GroupCorrectnessHardDirection
import BraidProject.ConvertMonoidInfToFin
import BraidProject.SignedListBounded

namespace Braid

open Relations

theorem reversing_bounded (h : SignedList.bounded n a) (hr : reversing a b) : SignedList.bounded n b := by
  cases hr with
  | basic h => intro x hx; simp at hx
  | apart h =>
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    cases hx ; all_goals apply h; aesop
  | close h =>
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h3 | ⟨rfl⟩ | ⟨rfl⟩ | h6
    · apply h
      aesop
    · rename_i i j hij
      apply h (i, false)
      aesop
    · rename_i i j hij
      apply h (j, true)
      aesop
    apply h
    aesop

theorem SemiThueData_reversing_bounded (h : SignedList.bounded n L) (h2 : SemiThueData reversing L L1) :
  SignedList.bounded n L1 := by
  induction h2 with
  | refl => exact h
  | step h2 h1 =>
    rw [SignedList.bounded_append, SignedList.bounded_append]
    rw [SignedList.bounded_append, SignedList.bounded_append] at h
    rename_i h3
    have h3 := reversing_bounded h.1.2 h3
    aesop
  | trans a b c _ => aesop

theorem reverse_word_bounded (ha : SignedList.bounded n a) : SignedList.bounded n (reverse_word a).1 := by
  exact SemiThueData_reversing_bounded ha (reverse_word a).derivation

theorem BraidGroupFin.eq_of_SemiThueData_reversing (h : SemiThueData reversing a b) (ha : SignedList.bounded n.pred a)
  (hb : SignedList.bounded n.pred b) :
  BraidGroupFin.mk n (FreeGroup.mk (SignedList.mapNatToFin a n.pred ha)) =
  BraidGroupFin.mk n (FreeGroup.mk (SignedList.mapNatToFin b n.pred hb)) := by
  induction h with
  | refl => rfl
  | step h =>
    rename_i e f g i
    rw [SignedList.mapNatToFin_append', ← FreeGroup.mul_mk, SignedList.mapNatToFin_append', ← FreeGroup.mul_mk,
      SignedList.mapNatToFin_append', ← FreeGroup.mul_mk, SignedList.mapNatToFin_append', ← FreeGroup.mul_mk,
      map_mul, map_mul, map_mul, map_mul, mul_left_inj, mul_right_inj]
    cases i with
    | basic =>
      rename_i i j hij
      apply Nat.eq_of_dist_eq_zero at hij
      subst hij
      change BraidGroupFin.mk n
        (FreeGroup.mk ([((⟨i, ha (i, true) (by simp)⟩ : Fin n.pred ), false)] ++
        [((⟨i, ha (i, true) (by simp)⟩ : Fin n.pred ), true)])) = _
      rw [← FreeGroup.mul_mk]
      congr
      exact eq_div_iff_mul_eq'.mp rfl
    | apart h =>
      rename_i i j
      change (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)⁻¹ * Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩ =
        Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩ * (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)⁻¹
      apply (mul_right_inj (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)).mp
      apply (mul_left_inj (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)).mp
      group
      exact (BraidGroupFin.comm (by linarith)).symm
    | close h =>
      rename_i i j
      change (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)⁻¹ * (Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩) =
        (Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩) *  (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩) * (Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩)⁻¹ * (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)⁻¹
      apply (mul_right_inj (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)).mp
      apply (mul_left_inj (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)).mp
      apply (mul_left_inj (Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩)).mp
      group
      exact (BraidGroupFin.braid h).symm
  | trans a c ih1 ih2 =>
    have hc := SemiThueData_reversing_bounded ha a
    exact (ih1 ha hc).trans (ih2 hc hb)

theorem BraidMonoidFin.eq_of_monoid_solver_true {n : ℕ} (ha : ∀ x ∈ a, x < n.pred) (hb : ∀ x ∈ b, x < n.pred)
    (h : monoid_solver a b) : BraidMonoidFin.mk n (FreeMonoid.mapNatToFin n.pred a ha) =
    BraidMonoidFin.mk n (FreeMonoid.mapNatToFin n.pred b hb) :=
  BraidMonoidFin.eq_of_BraidMonoidInf_eq _ a b ha hb (BraidMonoidInf.eq_of_monoid_solver h)

theorem BraidGroupFin.eq_of_braid_word_solver_true {n : ℕ} (ha : SignedList.bounded n.pred a) (hb : SignedList.bounded n.pred b) :
    braid_word_solver a b = true →
    BraidGroupFin.mk n (FreeGroup.mk (SignedList.mapNatToFin a n.pred ha)) =
    BraidGroupFin.mk n (FreeGroup.mk (SignedList.mapNatToFin b n.pred hb)) := by
  intro h
  unfold braid_word_solver at h
  rcases dede : (reverse_word (a ++ (FreeGroup.invRev b))).2 with ⟨d, e, hde⟩
  have hinvb : SignedList.bounded n.pred (FreeGroup.invRev b) := SignedList.bounded_invRev hb
  have hainvb : SignedList.bounded n.pred (a ++ FreeGroup.invRev b) :=
    SignedList.bounded_append.mpr ⟨ha, hinvb⟩
  have hout := reverse_word_bounded hainvb
  have hde_out : (reverse_word (a ++ FreeGroup.invRev b)).out = d ++ e := hde.1.2.2
  have hde_b : SignedList.bounded n.pred (d ++ e) := hde_out ▸ hout
  have hd : SignedList.bounded n.pred d := (SignedList.bounded_append.mp hde_b).1
  have he : SignedList.bounded n.pred e := (SignedList.bounded_append.mp hde_b).2
  have hd_map : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) d, x < n.pred := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact hd p hp
  have he_rev_map : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) e.reverse, x < n.pred := by
    intro x hx
    simp only [List.mem_map, List.mem_reverse] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact he p hp
  -- the monoid solver must have returned true at the last step
  have monoid_solver_true : monoid_solver (List.map (fun x => x.1) e.reverse) (List.map (fun x => x.1) d) = true := by
    rw [dede] at h; exact h
  -- thus d and e are equiv in the finite braid monoid
  have H := @BraidMonoidFin.eq_of_monoid_solver_true _ _ n he_rev_map hd_map monoid_solver_true
  -- so they are equiv in the finite braid GROUP
  apply BraidGroupFin.eq_of_BraidMonoidFin_eq at H
  -- separately, from the first part of the solver, a∘verline{b} reverses to d e,
  -- so they are Semi-Thue equiv under reversing, and hence
  -- equal in the finite braid monoid bc they are appropriately bounded
  have semi_thue_ab_de : SemiThueData reversing (a ++ FreeGroup.invRev b) (d ++ e) := by
    -- we need to get rid of hde.out here to avoid dtt hell
    have := (reverse_word (a ++ FreeGroup.invRev b)).3
    rw [hde_out] at this; exact this
  have H2 := BraidGroupFin.eq_of_SemiThueData_reversing (n := n) semi_thue_ab_de hainvb hde_b
  rw [SignedList.mapNatToFin_append' hainvb, SignedList.mapNatToFin_append' hde_b,
      ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul, SignedList.mapNatToFin_invRev hb hinvb] at H2
  rw [← SignedList.mapNatToFin_of_is_true d n.pred hde.1.1 hd hd_map] at H
  rw [← H, SignedList.mapNatToFin_of_is_false e n.pred hde.1.2.1 he he_rev_map,
    ← FreeGroup.inv_mk, ← FreeGroup.inv_mk, map_inv, map_inv, mul_inv_cancel] at H2
  exact mul_inv_eq_one.mp H2

theorem braid_word_solver_correct_fin {n : ℕ} (ha : SignedList.bounded n.pred a) (hb : SignedList.bounded n.pred b) :
  braid_word_solver a b ↔
  BraidGroupFin.mk n (FreeGroup.mk (SignedList.mapNatToFin a n.pred ha)) =
  BraidGroupFin.mk n (FreeGroup.mk (SignedList.mapNatToFin b n.pred hb)) := by
  constructor
  · intro sgt
    exact BraidGroupFin.eq_of_braid_word_solver_true ha hb sgt
  intro h1
  apply braid_word_solver_true_of_BraidGroupInf_eq
  apply BraidGroupInf.eq_of_BraidGroupFin_eq_word' ha hb h1

def solver_fin {n : ℕ} (a b : List (Fin n.pred × Bool)) : Bool :=
  braid_word_solver (List.map (fun p => (p.1.val, p.2)) a) (List.map (fun p => (p.1.val, p.2)) b)

theorem solver_fin_correct {a b : List (Fin n.pred × Bool)} : solver_fin a b ↔ BraidGroupFin.mk n (FreeGroup.mk a) =
    BraidGroupFin.mk n (FreeGroup.mk b) := by
  unfold solver_fin
  let a' := (List.map (fun p ↦ (p.1.val, p.2)) a)
  let b' := (List.map (fun p ↦ (p.1.val, p.2)) b)
  have ha : SignedList.bounded n.pred a' := by
    intro x hx
    grind
  have hb : SignedList.bounded n.pred b' := by
    intro x hx
    grind
  rw [braid_word_solver_correct_fin ha hb, SignedList.map_val_mapNatToFin a ha, SignedList.map_val_mapNatToFin b hb]

theorem BraidGroupFin.eq_of_BraidGroupInf_eq {a b : List (ℕ × Bool)} {n : ℕ}
    (ha : SignedList.bounded n.pred a) (hb : SignedList.bounded n.pred b)
    (h1 : BraidGroupInf.mk (FreeGroup.mk a) = BraidGroupInf.mk (FreeGroup.mk b)) :
    BraidGroupFin.mk n (FreeGroup.mk (SignedList.mapNatToFin a n.pred ha)) =
    BraidGroupFin.mk n (FreeGroup.mk (SignedList.mapNatToFin b n.pred hb)) :=
  (braid_word_solver_correct_fin ha hb).mp (braid_word_solver_true_of_BraidGroupInf_eq h1)
