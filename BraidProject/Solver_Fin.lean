import BraidProject.Solver.GroupCorrectnessHardDirection
import BraidProject.ConvertToFin

def is_bounded_by (k : ℕ) (u : List (ℕ × Bool)) := ∀ x ∈ u, x.1 < k

def bb_to_fin (L : List (ℕ × Bool)) (n : ℕ) (hL : is_bounded_by n L) : List (Fin n × Bool) :=
  (List.pmap (λ ⟨i, b⟩ h => (Fin.mk i h, b) ) L) hL

def is_bounded_by_no_bool (k : ℕ) (u : List ℕ) := ∀ x ∈ u, x < k

open Braid
def bbnb_to_fin (L : List ℕ) (n : ℕ) (hL : is_bounded_by_no_bool n L) : List (Fin n) :=
  (List.pmap (λ i => Fin.mk i ) L) hL

def make_fin  (n : ℕ) (a : FreeMonoid ℕ) (bound : ∀ x ∈ a, x<n) : FreeMonoid (Fin n) :=
  (FreeMonoid.pmap (λ i => Fin.mk i ) a) bound

theorem monoid_correctness_easy_direction {n : ℕ} (ha : ∀ x ∈ a, x < n.pred) (hb : ∀ x ∈ b, x < n.pred)
  (h : monoid_solver a b) : PresentedMonoid.mk (braid_monoid_rels_fin n) (make_fin n.pred a ha) =
  PresentedMonoid.mk (braid_monoid_rels_fin n) (make_fin n.pred b hb) := by
  match a with
  | [] =>
    match b with
    | [] => rfl
    | b1 :: b2 =>
      simp [monoid_solver] at h
  | a1 :: a2 =>
    match b with
    | [] => simp [monoid_solver] at h
    | b1 :: b2 =>
      simp [monoid_solver] at h
      apply BraidMonoidFin.eq_of_BraidMonoidInf_eq
      rw [← List.append_nil (a1 :: a2), ← List.append_nil (b1 :: b2)]
      apply bm_equiv_of_reversing (by simp) (by simp)
      have H := @reverse_pair_spec (a1 :: a2) (b1 :: b2) (by simp) (by simp)
      rw [h] at H
      exact SemiThueDataDerivation.toSemiThueData H

theorem monoid_correctness_easy_direction' {n : ℕ} (ha : ∀ x ∈ a, x < n.pred) (hb : ∀ x ∈ b, x < n.pred)
  (h : monoid_solver a b) : PresentedMonoid.mk (braid_monoid_rels_fin' n) (make_fin n.pred a ha) =
  PresentedMonoid.mk (braid_monoid_rels_fin' n) (make_fin n.pred b hb) := by
  match a with
  | [] =>
    match b with
    | [] => rfl
    | b1 :: b2 =>
      simp [monoid_solver] at h
  | a1 :: a2 =>
    match b with
    | [] => simp [monoid_solver] at h
    | b1 :: b2 =>
      simp [monoid_solver] at h
      apply BraidMonoidFin'.eq_of_BraidMonoidInf_eq
      rw [← List.append_nil (a1 :: a2), ← List.append_nil (b1 :: b2)]
      apply bm_equiv_of_reversing (by simp) (by simp)
      have H := @reverse_pair_spec (a1 :: a2) (b1 :: b2) (by simp) (by simp)
      rw [h] at H
      exact SemiThueDataDerivation.toSemiThueData H

theorem is_bounded_by_append : is_bounded_by n (a ++ b) ↔ is_bounded_by n a ∧ is_bounded_by n b := by
  constructor
  · intro h
    constructor
    · intro x hx
      apply h
      exact List.mem_append_left b hx
    intro x hx
    apply h
    exact List.mem_append_right a hx
  intro h x hx
  apply List.mem_append.mp at hx
  cases hx with
  | inl h1 => apply h.1 _ h1
  | inr h2 => apply h.2 _ h2

theorem is_bounded_by_tail (h : is_bounded_by n (a1 :: a2)) : is_bounded_by n a2 := by
  intro x hx
  apply h
  exact List.mem_cons_of_mem _ hx

theorem is_bounded_by_invRev (h : is_bounded_by n a) : is_bounded_by n (FreeGroup.invRev a) := by
  intro x hx
  unfold FreeGroup.invRev at hx
  simp only [List.mem_map, List.mem_reverse] at hx
  rcases hx with ⟨a1, ha1⟩
  rw [← ha1.2]
  apply h (a1.1, a1.2) ha1.1

theorem bb_to_fin_append (ha : is_bounded_by n a) (hb : is_bounded_by n b) :
  bb_to_fin (a ++ b) n (by apply is_bounded_by_append.mpr; constructor; assumption; assumption) =
  bb_to_fin a n ha ++ bb_to_fin b n hb := by
  unfold bb_to_fin
  rw [List.pmap_append]

theorem bb_to_fin_append' (hbb : is_bounded_by n (a ++ b)) :
  bb_to_fin (a ++ b) n hbb =
  bb_to_fin a n (is_bounded_by_append.mp hbb).1 ++ bb_to_fin b n (is_bounded_by_append.mp hbb).2 := by
  unfold bb_to_fin
  rw [List.pmap_append]

theorem bb_to_fin_cons (ha : is_bounded_by n (a1 :: a2)) (ha' : is_bounded_by n a2) :
  bb_to_fin (a1 :: a2) n ha = (Fin.mk a1.1 (ha a1 (by simp)), a1.2) :: bb_to_fin a2 n ha' := by
  unfold bb_to_fin
  simp [List.pmap_cons]

theorem bb_to_fin_invRev (ha : is_bounded_by n a) (ha' : is_bounded_by n (FreeGroup.invRev a)) :
    bb_to_fin (FreeGroup.invRev a) n ha' = FreeGroup.invRev (bb_to_fin a n ha) := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [bb_to_fin_cons ha (is_bounded_by_tail ha)]
    conv => rhs; rw [FreeGroup.invRev_cons]
    specialize ih (is_bounded_by_tail ha) (is_bounded_by_invRev (is_bounded_by_tail ha))
    rw [← ih]
    have : FreeGroup.invRev [(⟨head.1, (ha head (by simp))⟩, head.2)] =
        bb_to_fin (FreeGroup.invRev [head]) n (is_bounded_by_invRev
        (by intro x hx; simp at hx; rw [hx]; exact ha head (by simp))) := rfl
    rw [this]
    rw [← bb_to_fin_append' (by rw [← FreeGroup.invRev_cons]; exact is_bounded_by_invRev ha)]
    congr
    rw [FreeGroup.invRev_cons]

theorem reversing_bounded (h : is_bounded_by n a) (hr : reversing a b) : is_bounded_by n b := by
  cases hr with
  | basic h => intro x hx; simp at hx
  | apart h =>
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h3 | h4
    · apply h
      aesop
    apply h
    aesop
  | close h =>
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h3 | h4 | h5 | h6
    · apply h
      aesop
    · rw [h4]
      rename_i i j hij
      apply h (i, false)
      aesop
    · rw [h5]
      rename_i i j hij
      apply h (j, true)
      aesop
    apply h
    aesop

theorem SemiThueData_reversing_bounded (h : is_bounded_by n L) (h2 : SemiThueData reversing L L1) :
  is_bounded_by n L1 := by
  induction h2 with
  | refl => exact h
  | step h2 h1 =>
    rw [is_bounded_by_append, is_bounded_by_append]
    rw [is_bounded_by_append, is_bounded_by_append] at h
    rename_i h3
    have h3 := reversing_bounded h.1.2 h3
    aesop
  | trans a b c _ => aesop

theorem reverse_word_bounded (ha : is_bounded_by n a) : is_bounded_by n (reverse_word a).1 := by
  exact SemiThueData_reversing_bounded ha (reverse_word a).steps

theorem FreeGroup.invRev_bounded_by (ha : is_bounded_by n a) : is_bounded_by n (FreeGroup.invRev a) := by
  intro x hx
  unfold invRev at hx
  simp only [List.mem_map, List.mem_reverse] at hx
  rcases hx with ⟨a1, ha1⟩
  rw [← ha1.2]
  apply ha (a1.1, a1.2) ha1.1

set_option pp.proofs true in
theorem List.pmap_inj {α β : Type*} {P : α → Prop} (f : ∀ a, P a → β)
  (hf : ∀ a b ha hb, f a ha = f b hb → a = b) (l1 l2 : List α)
  (h1 : ∀ a ∈ l1, P a) (h2 : ∀ a ∈ l2, P a) :
  List.pmap f l1 h1 = List.pmap f l2 h2 → l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    intro hx
    simp only [pmap_nil, nil_eq, pmap_eq_nil_iff] at hx
    exact hx.symm
  | cons head tail ih =>
    intro hx
    simp at hx
    cases l2 with
    | nil => simp at hx
    | cons head1 tail1 =>
      simp at hx
      refine cons_eq_cons.mpr ?_
      constructor
      · apply hf _ _ _ _ hx.1
      apply ih
      exact hx.2

theorem make_fin_inj {n : ℕ} {a b : FreeMonoid ℕ}
  (bound_a : ∀ x ∈ a, x < n) (bound_b : ∀ x ∈ b, x < n)
  (ha : make_fin n a bound_a = make_fin n b bound_b) :
  a = b := by
  unfold make_fin at ha
  apply List.pmap_inj at ha
  exact ha
  intro a b ha hb hx
  simp only [Fin.mk.injEq] at hx
  exact hx

theorem to_horizontal_edge_no_epsilon_FreeMonoid_of : to_horizontal_edge_no_epsilon (FreeMonoid.of x) = [(x, true)] := rfl

theorem bm_to_bg_fin'' {n : ℕ} {a1 b1 : FreeMonoid (Fin n.pred)} (h : PresentedMonoid.mk (braid_monoid_rels_fin' n) a1 =
  PresentedMonoid.mk (braid_monoid_rels_fin' n) b1):
  (PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk (to_horizontal_edge_no_epsilon a1)) =
  (PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk (to_horizontal_edge_no_epsilon b1)) := by
  apply PresentedMonoid.exact at h
  induction h with
  | of x y h =>
    unfold braid_monoid_rels_fin' at h
    match n with
    | 0 => simp at h
    | n + 1 =>
      simp only at h
      cases h with
      | adjacent i =>
        rw [to_horizontal_edge_no_epsilon_mul, to_horizontal_edge_no_epsilon_mul,
          to_horizontal_edge_no_epsilon_mul, to_horizontal_edge_no_epsilon_mul,
          to_horizontal_edge_no_epsilon_FreeMonoid_of, to_horizontal_edge_no_epsilon_FreeMonoid_of]
        apply BraidGroupFin.braid
        unfold Nat.dist
        grind
      | separated i j h =>
        rw [to_horizontal_edge_no_epsilon_mul, to_horizontal_edge_no_epsilon_mul,
          to_horizontal_edge_no_epsilon_FreeMonoid_of, to_horizontal_edge_no_epsilon_FreeMonoid_of,
          ]
        apply BraidGroupFin.comm
        unfold Nat.dist
        grind
  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | mul _ _ ih1 ih2 =>
    rw [to_horizontal_edge_no_epsilon_mul, to_horizontal_edge_no_epsilon_mul, ← FreeGroup.mul_mk,  ← FreeGroup.mul_mk,
    PresentedGroup.mk_mul, PresentedGroup.mk_mul, ih1, ih2]

-- open Braid in
-- theorem bm_to_bg_fin {n : ℕ} {a1 b1 : FreeMonoid (Fin n.pred)}(h : PresentedMonoid.mk (braid_monoid_rels_fin' n) a1 =
--   PresentedMonoid.mk (braid_monoid_rels_fin' n) b1)
--   (bound_a_1 : ∀ x ∈ (List.map (fun x => x.1) a), x < n.pred)
--   (ha : a1 = make_fin n.pred (List.map (fun x => x.1) a) bound_a_1)
--   (bound_a : is_bounded_by n.pred a)
--   (bound_b_1 : ∀ x ∈ (List.map (fun x => x.1) b), x < n.pred)
--   (hb : b1 = make_fin n.pred (List.map (fun x => x.1) b) bound_b_1)
--   (bound_b : is_bounded_by n.pred b) :
--   (PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk (bb_to_fin a n.pred bound_a)) =
--   (PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk (bb_to_fin b n.pred bound_b)) := by
--   apply bm_to_bg_fin'' at h
--   convert h
--   · rw [ha]
--     unfold bb_to_fin to_horizontal_edge_no_epsilon make_fin
--     simp
--     clear ha hb h bound_b bound_b_1 b b1
--     induction a with
--     | nil => simp only [List.pmap_nil, List.map_nil, List.nil_eq, List.map_eq_nil_iff]; rfl
--     | cons head tail ih =>
--       specialize ih (by sorry) sorry

--       unfold FreeMonoid.pmap
--       simp [List.pmap_cons, List.map_cons, ih]
--       constructor
--       · sorry
--       rfl
--   sorry

theorem pg_mk_fg_inv_fin : ((PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk a))⁻¹ =
  (PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk (FreeGroup.invRev a)) := by
  rw [← FreeGroup.inv_mk, map_inv]

theorem pg_mk_to_horizontal_edge_no_epsilon_inv_fin :
  ((PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk (to_horizontal_edge_no_epsilon a)))⁻¹ =
  (PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk (to_vertical_edge_no_epsilon a)) := by
  rw [pg_mk_fg_inv_fin]
  congr
  exact to_vertical_edge_no_epsilon_invRev_to_horizontal_edge_no_epsilon.symm

theorem recover_from_is_true_fin (h : SignedList.is_true d) : to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) d) = (d : List (ℕ × Bool)) := by
  induction d with
  | nil => simp [to_horizontal_edge_no_epsilon]
  | cons head tail ih =>
    have tt : SignedList.is_true tail := (SignedList.is_true_of_cons h).2
    specialize ih tt
    simp only [to_horizontal_edge_no_epsilon, List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · have ht : SignedList.is_true [head] := (SignedList.is_true_of_cons h).1
      specialize ht head
      grind
    rw [← ih]
    unfold to_horizontal_edge_no_epsilon
    simp

theorem SemiThueData_reversing_to_braid_group_equiv_fin (h : SemiThueData reversing a b) (ha : is_bounded_by n.pred a)
  (hb : is_bounded_by n.pred b) :
  (PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk (bb_to_fin a n.pred ha)) =
  (PresentedGroup.mk (Braid.braidRelationFin n)) (FreeGroup.mk (bb_to_fin b n.pred hb)) := by
  induction h with
  | refl => rfl
  | step h =>
    rename_i e f g i
    rw [bb_to_fin_append', ← FreeGroup.mul_mk, bb_to_fin_append', ← FreeGroup.mul_mk,
      bb_to_fin_append', ← FreeGroup.mul_mk, bb_to_fin_append', ← FreeGroup.mul_mk,
      PresentedGroup.mk_mul, PresentedGroup.mk_mul, PresentedGroup.mk_mul, PresentedGroup.mk_mul,
      mul_left_inj, mul_right_inj]
    cases i with
    | basic =>
      rename_i i j hij
      apply Nat.eq_of_dist_eq_zero at hij
      subst hij
      change (PresentedGroup.mk (Braid.braidRelationFin n))
        (FreeGroup.mk ([((⟨i, ha (i, true) (by simp)⟩ : Fin n.pred ), false)] ++
        [((⟨i, ha (i, true) (by simp)⟩ : Fin n.pred ), true)])) = _
      rw [← FreeGroup.mul_mk]
      unfold FreeGroup.mk
      congr
      exact eq_div_iff_mul_eq'.mp rfl
    | apart h =>
      rename_i i j
      change (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)⁻¹ * Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩ = Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩ * (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)⁻¹
      apply (mul_right_inj (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)).mp
      apply (mul_left_inj (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)).mp
      group
      symm
      apply BraidGroupFin.comm
      exact h
    | close h =>
      rename_i i j
      change (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)⁻¹ * (Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩) = (Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩) *  (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩) * (Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩)⁻¹ * (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)⁻¹
      apply (mul_right_inj (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)).mp
      apply (mul_left_inj (Braid.σₙ ⟨i, (ha (i, false) (by simp))⟩)).mp
      apply (mul_left_inj (Braid.σₙ ⟨j, (ha (j, true) (by simp))⟩)).mp
      group
      symm
      exact BraidGroupFin.braid h
  | trans a c ih1 ih2 =>
    have hc := SemiThueData_reversing_bounded ha a
    specialize ih1 ha hc
    specialize ih2 hc hb
    exact ih1.trans ih2


/-- Bridging lemma: when a list is all-True and bounded, `bb_to_fin` agrees with
    `to_horizontal_edge_no_epsilon ∘ make_fin ∘ map (·.1)`. -/
theorem bb_to_fin_of_is_true (d : List (ℕ × Bool)) (n : ℕ) (h_true : SignedList.is_true d)
    (hd : is_bounded_by n d)
    (hd_map : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) d, x < n) :
    bb_to_fin d n hd =
      to_horizontal_edge_no_epsilon (make_fin n (List.map (fun p : ℕ × Bool => p.1) d) hd_map) := by
  show List.pmap _ d hd = List.map _ (List.pmap _ _ hd_map)
  induction d with
  | nil => rfl
  | cons head tail ih =>
    have t_true : SignedList.is_true tail := (SignedList.is_true_of_cons h_true).2
    have t_bd : is_bounded_by n tail := fun x hx => hd x (List.mem_cons_of_mem _ hx)
    have t_bd_map : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) tail, x < n := by
      intro x hx
      apply hd_map
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr hx
    have ih' := ih t_true t_bd t_bd_map
    have h_head : head.2 = true := (SignedList.is_true_of_cons h_true).1 head (by simp)
    obtain ⟨i, bl⟩ := head
    simp only at h_head
    subst h_head
    simp only [List.pmap, List.map_cons]
    exact congrArg _ ih'

/-- Bridging lemma: when a list is all-False and bounded, `bb_to_fin` agrees with
    `FreeGroup.invRev ∘ to_horizontal_edge_no_epsilon ∘ make_fin ∘ map (·.1) ∘ reverse`. -/
theorem bb_to_fin_of_is_false (e : List (ℕ × Bool)) (n : ℕ) (h_false : SignedList.is_false e)
    (he : is_bounded_by n e)
    (he_rev_map : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) e.reverse, x < n) :
    bb_to_fin e n he =
      FreeGroup.invRev (to_horizontal_edge_no_epsilon
        (make_fin n (List.map (fun p : ℕ × Bool => p.1) e.reverse) he_rev_map)) := by
  show List.pmap _ e he =
    (List.map _ (List.map _ (List.pmap _ _ he_rev_map))).reverse
  induction e with
  | nil => rfl
  | cons head tail ih =>
    have t_false : SignedList.is_false tail := (SignedList.is_false_of_cons h_false).2
    have t_bd : is_bounded_by n tail := fun x hx => he x (List.mem_cons_of_mem _ hx)
    have t_bd_map : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) tail.reverse, x < n := by
      intro x hx
      apply he_rev_map
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton]
      left; exact hx
    have ih' := ih t_false t_bd t_bd_map
    have h_head : head.2 = false := (SignedList.is_false_of_cons h_false).1 head (by simp)
    obtain ⟨i, bl⟩ := head
    simp only at h_head
    subst h_head
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.pmap_append, List.pmap, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, Bool.not_true]
    exact congrArg _ ih'

theorem solver_g_correct_one_direction_fin {n : ℕ} (ha : is_bounded_by n.pred a) (hb : is_bounded_by n.pred b) :
    group_solver a b = true →
  PresentedGroup.mk (Braid.braidRelationFin n) (FreeGroup.mk (bb_to_fin a n.pred ha)) =
  PresentedGroup.mk (Braid.braidRelationFin n) (FreeGroup.mk (bb_to_fin b n.pred hb)) := by
  intro h
  unfold group_solver at h
  rcases dede : (reverse_word (a ++ (FreeGroup.invRev b))).2 with ⟨d, e, hde⟩
  -- Establish bounds
  have hab : is_bounded_by n.pred (a ++ FreeGroup.invRev b) :=
    is_bounded_by_append.mpr ⟨ha, FreeGroup.invRev_bounded_by hb⟩
  have hinvb : is_bounded_by n.pred (FreeGroup.invRev b) := FreeGroup.invRev_bounded_by hb
  have hout := reverse_word_bounded hab
  have hde_out : (reverse_word (a ++ FreeGroup.invRev b)).1 = d ++ e := hde.1.2.2
  have hde_b : is_bounded_by n.pred (d ++ e) := hde_out ▸ hout
  have hd : is_bounded_by n.pred d := (is_bounded_by_append.mp hde_b).1
  have he : is_bounded_by n.pred e := (is_bounded_by_append.mp hde_b).2
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
  -- Extract monoid_solver equation from h using dede
  have h_ms : monoid_solver (List.map (fun x => x.1) e.reverse) (List.map (fun x => x.1) d) = true := by
    rw [dede] at h; exact h
  -- Get PresentedMonoid equation
  have H := @monoid_correctness_easy_direction' _ _ n he_rev_map hd_map h_ms
  -- Convert to PresentedGroup equation via bm_to_bg_fin''
  apply bm_to_bg_fin'' at H
  -- Get SemiThueData reversing to (d ++ e)
  have steps_de : SemiThueData reversing (a ++ FreeGroup.invRev b) (d ++ e) := by
    have := (reverse_word (a ++ FreeGroup.invRev b)).3
    rw [hde_out] at this; exact this
  -- H2 from the fin version of SemiThue reversing → braid group equiv
  have H2 := SemiThueData_reversing_to_braid_group_equiv_fin (n := n) steps_de hab hde_b
  -- Split bb_to_fin over ++
  rw [bb_to_fin_append' hab, bb_to_fin_append' hde_b,
      ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul] at H2
  -- Substitute bb_to_fin (invRev b) with FreeGroup.invRev (bb_to_fin b)
  rw [bb_to_fin_invRev hb hinvb] at H2
  -- Bridge bb_to_fin d and bb_to_fin e with to_horizontal_edge_no_epsilon forms
  rw [bb_to_fin_of_is_true d n.pred hde.1.1 hd hd_map,
      bb_to_fin_of_is_false e n.pred hde.1.2.1 he he_rev_map] at H2
  -- Now H2 has: PG(FG(bb_to_fin a)) * PG(FG(invRev (bb_to_fin b))) =
  --             PG(FG(to_hor_d)) * PG(FG(invRev to_hor_e_rev))
  -- H says: PG(FG(to_hor_e_rev)) = PG(FG(to_hor_d))
  -- Combine: RHS of H2 = PG(FG(to_hor_d)) * (PG(FG(to_hor_e_rev)))⁻¹ = PG(FG(to_hor_d)) * (PG(FG(to_hor_d)))⁻¹ = 1
  rw [show FreeGroup.mk (FreeGroup.invRev (to_horizontal_edge_no_epsilon
        (make_fin n.pred (List.map (fun x => x.1) e.reverse) he_rev_map))) =
      (FreeGroup.mk (to_horizontal_edge_no_epsilon
        (make_fin n.pred (List.map (fun x => x.1) e.reverse) he_rev_map)))⁻¹ from
      FreeGroup.inv_mk.symm] at H2
  rw [map_inv, ← H, mul_inv_cancel] at H2
  -- H2 : PG(FG(bb_to_fin a)) * PG(FG(invRev (bb_to_fin b))) = 1
  -- Rewrite PG(FG(invRev _)) as (PG(FG(_)))⁻¹
  rw [show FreeGroup.mk (FreeGroup.invRev (bb_to_fin b n.pred hb)) =
      (FreeGroup.mk (bb_to_fin b n.pred hb))⁻¹ from FreeGroup.inv_mk.symm,
      map_inv] at H2
  exact mul_inv_eq_one.mp H2

theorem bb_to_fin_map_val {n : ℕ} (L : List (ℕ × Bool)) (hL : is_bounded_by n L) :
    List.map (fun p : Fin n × Bool => (p.1.val, p.2)) (bb_to_fin L n hL) = L := by
  unfold bb_to_fin
  induction L with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.pmap, List.map_cons, List.cons.injEq]
    exact ⟨trivial, ih _⟩

theorem BraidGroupInf.eq_of_BraidMonoidInf_eq
    {a b : List (ℕ × Bool)} {n : ℕ} (ha : is_bounded_by n.pred a) (hb : is_bounded_by n.pred b)
    (h1 : (PresentedGroup.mk (braidRelationFin n)) (FreeGroup.mk (bb_to_fin a n.pred ha)) =
      (PresentedGroup.mk (braidRelationFin n)) (FreeGroup.mk (bb_to_fin b n.pred hb))) :
    BraidGroupInf.mk (FreeGroup.mk a) = BraidGroupInf.mk (FreeGroup.mk b) := by
  let f : Fin n.pred → BraidGroupInf := fun i => σ i.val
  have hf : BraidGroupFin.IsLiftable n f :=
    ⟨fun _ _ => BraidGroupInf.braid, fun _ _ => BraidGroupInf.comm⟩
  let φ : BraidGroupFin n →* BraidGroupInf := BraidGroupFin.toGroup n hf
  have φ_spec : ∀ w : FreeGroup (Fin n.pred), φ (BraidGroupFin.mk n w) =
        BraidGroupInf.mk (FreeGroup.map (fun i => i.val) w) := by
    intro w
    have h1 : φ (BraidGroupFin.mk n w) = FreeGroup.lift f w :=
      FreeGroup.lift_unique (φ.comp (BraidGroupFin.mk n)) (fun _ => rfl)
    have h2 : BraidGroupInf.mk (FreeGroup.map (fun i => i.val) w) =
        FreeGroup.lift f w :=
      FreeGroup.lift_unique
        (BraidGroupInf.mk.comp (FreeGroup.map (fun (i : Fin _) => i.1))) (fun _ => rfl)
    exact h1.trans h2.symm
  apply congrArg φ at h1
  change φ (BraidGroupFin.mk n _) = φ (BraidGroupFin.mk n _) at h1
  rw [φ_spec, φ_spec, FreeGroup.map.mk, FreeGroup.map.mk, bb_to_fin_map_val, bb_to_fin_map_val] at h1
  exact h1

theorem solver_g_correct_fin {n : ℕ} (ha : is_bounded_by n.pred a) (hb : is_bounded_by n.pred b) :
  group_solver a b ↔
  PresentedGroup.mk (Braid.braidRelationFin n) (FreeGroup.mk (bb_to_fin a n.pred ha)) =
  PresentedGroup.mk (Braid.braidRelationFin n) (FreeGroup.mk (bb_to_fin b n.pred hb)) := by
  constructor
  · intro sgt
    exact solver_g_correct_one_direction_fin ha hb sgt
  intro h1
  apply solver_g_correct_other_direction
  apply BraidGroupInf.eq_of_BraidMonoidInf_eq ha hb h1
