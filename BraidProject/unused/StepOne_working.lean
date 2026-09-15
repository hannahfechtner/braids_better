import BraidProject.PairInfixIrreducibleCases

namespace Braid

open List SignedList SignedOptionList Relations


-- noncomputable def rg_of_rev_rel' (d1)
--     (gr : SemiThueData grid_style (SignedList.to_SignedOptionList a) b')
--     (b'_is : toSignedList b' = e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b')
--     (rel_holds : grid_style [(some c1, false), (some c2, true)] d1) :
--     Σ b', SemiThueData grid_style (SignedList.to_SignedOptionList a) b' ×
--     PLift (toSignedList b' = e ++ (toSignedList d1) ++ f) × irreducible b' := by
--   have H1 : [(c1, false), (c2, true)].InfixData (toSignedList b') := by
--     rw [b'_is]
--     use e, f
--     constructor; rfl
--   rcases (pairsTogether_of_irreducible pt_b) b' (InfixData.refl b') c1 c2 H1 with ⟨w, t, hwt⟩
--   rw [← hwt.1, toSignedList_append, toSignedList_append, toSignedList] at b'_is
--   rw [← hwt.1] at pt_b
--   have ptw : irreducible w := (irreducible_append (irreducible_append pt_b).1).1
--   have ptt : irreducible t := (irreducible_append pt_b).2
--   rcases distinctPairInfixCases (by simp) b'_is with h1 | h2 | h3
--   · use move_ones (w ++ d1 ++ t)
--     constructor
--     · apply SemiThueData.trans gr
--       rw [← hwt.1]
--       exact SemiThueData.trans (SemiThueData.step _ _ rel_holds) equiv_move_ones
--     constructor
--     constructor
--     · rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, h1.1.1, h1.1.2]
--     exact move_ones_irreducible
--   · rcases h2 with ⟨a1, a2, spec⟩
--     rcases split_of_toSignedList_pair_infix spec.1.1.symm ptw with ⟨w1, w2, speckle⟩
--     use move_ones (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
--     constructor
--     · apply SemiThueData.trans gr
--       rw [← hwt.1]
--       have H : SemiThueData grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
--         (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t) := by
--         apply SemiThueData.append_right
--         rw [speckle.1.1]
--         exact SemiThueData.append_right (SemiThueData.append_right (SemiThueData.append_left
--           (SemiThueData.of_rel rel_holds)))
--       apply H.trans equiv_move_ones
--     constructor
--     · have e_eq : e = toSignedList w1 := spec.1.2.1.trans speckle.1.2.1
--       have f_eq : f = toSignedList w2 ++ [(c1, false), (c2, true)] ++ toSignedList t := by
--         rw [spec.1.2.2, speckle.1.2.2]
--       rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, e_eq, f_eq]
--       constructor
--       simp [toSignedList, toSignedList_append]
--     exact move_ones_irreducible
--   rcases h3 with ⟨a1, a2, spec⟩
--   rcases split_of_toSignedList_pair_infix spec.1.1.symm ptt with ⟨t1, t2, speckle⟩
--   use move_ones (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
--   constructor
--   · apply SemiThueData.trans gr
--     rw [← hwt.1]
--     have H : SemiThueData grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
--         (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2) := by
--       rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
--       apply SemiThueData.append_left
--       have t_eq : t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 := speckle.1.1
--       rw [List.append_assoc] at t_eq
--       rw [t_eq]
--       exact SemiThueData.append_left
--           (SemiThueData.append_left (SemiThueData.append_right (SemiThueData.of_rel rel_holds)))
--     exact H.trans equiv_move_ones
--   constructor
--   · have e_eq : e = toSignedList w ++ [(c1, false), (c2, true)] ++ toSignedList t1 := by
--       rw [spec.1.2.1, speckle.1.2.1]
--     have f_eq : f = toSignedList t2 := spec.1.2.2.trans speckle.1.2.2
--     rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, e_eq, f_eq]
--     exact {down := by simp [toSignedList, toSignedList_append]}
--   exact move_ones_irreducible

noncomputable def grid_style_of_reversing_step (d1)
    (gr : SemiThueData grid_style (SignedList.to_SignedOptionList a) b')
    (b'_is : toSignedList b' = e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b')
    (rel_holds : grid_style [(some c1, false), (some c2, true)] d1) :
    Σ b'', SemiThueData grid_style (SignedList.to_SignedOptionList a) b'' ×
    PLift (toSignedList b'' = e ++ (toSignedList d1) ++ f) × irreducible b'' := by
  have H1 : [(c1, false), (c2, true)].InfixData (toSignedList b') := by
    rw [b'_is]
    use e, f
    constructor; rfl
  rcases (pairsTogether_of_irreducible pt_b) b' (InfixData.refl b') c1 c2 H1 with ⟨w, t, hwt⟩
  rw [← hwt.1, toSignedList_append, toSignedList_append, toSignedList] at b'_is
  rw [← hwt.1] at pt_b
  have := pair_infix_irreducible_cases b'_is (irreducible_append (irreducible_append pt_b).1).1
    (irreducible_append pt_b).2
  rcases this with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
  · use move_ones (w ++ d1 ++ t)
    constructor
    · apply SemiThueData.trans gr
      rw [← hwt.1]
      exact SemiThueData.trans (SemiThueData.step _ _ rel_holds) equiv_move_ones
    constructor
    constructor
    · rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, h2.1.1,
        h2.1.2]
    exact move_ones_irreducible
  · use move_ones (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
    constructor
    · apply SemiThueData.trans gr
      rw [← hwt.1]
      have H : SemiThueData grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t) := by
        apply SemiThueData.append_right
        rw [hw.1.1]
        exact SemiThueData.append_right (SemiThueData.append_right (SemiThueData.append_left
          (SemiThueData.of_rel rel_holds)))
      apply H.trans equiv_move_ones
    constructor
    · rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, hw.1.2.1, hw.1.2.2]
      constructor
      simp [toSignedList, toSignedList_append]
    exact move_ones_irreducible
  use move_ones (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
  constructor
  · apply SemiThueData.trans gr
    rw [← hwt.1]
    have H : SemiThueData grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2) := by
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
      apply SemiThueData.append_left
      rw [List.append_assoc, List.append_assoc] at ht
      rw [ht.1.1]
      exact SemiThueData.append_left
          (SemiThueData.append_left (SemiThueData.append_right (SemiThueData.of_rel rel_holds)))
    exact H.trans equiv_move_ones
  constructor
  · rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, ht.1.2.1, ht.1.2.2]
    exact {down := by simp [toSignedList, toSignedList_append]}
  exact move_ones_irreducible

noncomputable def grid_style_of_reversing (h : SemiThueData reversing a b) :
    Σ b', SemiThueData grid_style (SignedList.to_SignedOptionList a) b' × PLift
    (toSignedList b' = b) × irreducible b' := by
  have H := SemiThueData.toSemiThueDataDerivation h
  induction H with
  | refl =>
    exact ⟨SignedList.to_SignedOptionList _, (SemiThueData.refl,
      {down := toSignedList_toSignedOptionList}, SignedList.toSignedOptionList_irreducible)⟩
  | step h1 h2 ih =>
    rename_i c d e f g
    rcases ih (SemiThueDataDerivation.toSemiThueData h1) with ⟨b', gr, b'_is, pt_b⟩
    cases h2 with
    | basic h_dist =>
      apply Nat.eq_of_dist_eq_zero at h_dist
      apply grid_style_of_reversing_step ([(none, true), (none, false)]) gr  b'_is.1 pt_b
      rw [h_dist]
      exact .basic _
    | apart h_dist =>
      rename_i i j
      exact grid_style_of_reversing_step ([(some j, true), (some i, false)]) gr b'_is.1 pt_b (.apart h_dist)
    | close h_dist =>
      rename_i i j
      exact grid_style_of_reversing_step ([(some j, true), (some i, true), (some j, false), (some i, false)])
        gr b'_is.1 pt_b (.close h_dist)

noncomputable def SemiThueData.reversing.to_grid_style_NegPos_to_PosNeg_mid (h : SemiThueData reversing a b) (ha : SignedList.NegPosData a) :
    Σ b', SemiThueData grid_style (SignedList.to_SignedOptionList a) b' ×
    SignedList.NegPosData (SignedList.to_SignedOptionList a) ×  PLift (toSignedList b' = b) := by
  rcases grid_style_of_reversing h with ⟨b', gr, b'_is, pt_b⟩
  use b'
  constructor
  · exact gr
  constructor
  · exact SignedList.toSignedOptionList_NegPosData ha
  exact b'_is


def PosNegData_of_toSignedList_PosNeg_and_irreducible (h : SignedList.PosNegData (toSignedList L)) (h2 : irreducible L) :
    SignedList.PosNegData L := by
  induction L
  · exact SignedList.PosNegData.nil
  rename_i head tail ih
  have h_io : SignedList.PosNegData (toSignedList tail) := by
    match head with
    | (none, _) =>
      exact h
    | (some _, _) =>
      exact SignedList.PosNegData.tail h
  rcases ih h_io (irreducible_tail h2) with ⟨a1, a2, ha⟩
  match head with
  | (b, true) =>
    use (b, true) :: a1, a2
    constructor
    constructor
    · intro x hx
      simp only [mem_cons] at hx
      rcases hx with h1 | h2
      · simp [h1]
      exact ha.1.1 _ h2
    constructor
    · exact ha.1.2.1
    simp only [cons_append, cons.injEq, true_and]
    exact ha.1.2.2
  | (none, false) =>
    use [], (none, false) :: a2
    constructor
    constructor
    · exact SignedList.is_true_nil
    constructor
    · exact SignedList.is_false_cons _ ha.1.2.1
    simp only [ha.1.2.2, nil_append, cons.injEq, append_left_eq_self, true_and]
    match a1 with
    | [] => exact rfl
    | head :: tail1 =>
      exfalso
      match head with
      | (fst, false) =>
        simp only [SignedList.is_true, mem_cons, forall_eq_or_imp, Bool.false_eq_true, Prod.forall,
          Bool.forall_bool, imp_false, implies_true, and_true, false_and, cons_append] at ha
        exact ha.1
      | (none, true) =>
        simp only [toSignedList] at h
        simp only [SignedList.is_true, mem_cons, forall_eq_or_imp, Prod.forall, Bool.forall_bool,
          Bool.false_eq_true, imp_false, implies_true, and_true, true_and, cons_append] at ha
        rw [ha.1.2.2] at h2
        specialize h2 0
        apply Empty.elim
        apply h2.2.2
        use [], tail1 ++ a2
        exact {down := by simp}
      | (some c, true) =>
        simp only [toSignedList] at h
        simp only [SignedList.is_true, mem_cons, forall_eq_or_imp, Prod.forall, Bool.forall_bool,
          Bool.false_eq_true, imp_false, implies_true, and_true, true_and, cons_append] at ha
        rw [ha.1.2.2] at h2
        specialize h2 c
        apply Empty.elim
        apply h2.2.1
        use [], tail1 ++ a2
        exact {down := by simp}
  | (some a, false) =>
    use [], (some a, false) :: a2
    constructor
    constructor
    · exact SignedList.is_true_nil
    constructor
    · exact SignedList.is_false_cons _ ha.1.2.1
    simp only [ha.1.2.2, nil_append, cons.injEq, append_left_eq_self, true_and]
    match tail with
    | [] =>
      simp only [nil_eq, append_eq_nil_iff] at ha
      exact ha.1.2.2.1
    | (none, true) :: tail2 =>
      apply Empty.elim
      apply (h2 a).1
      use [], tail2
      exact {down := by simp}
    | (_, false) :: tail2 =>
      match a1 with
      | [] => rfl
      | (_, true) :: rest =>
        simp only [cons_append, cons.injEq, Prod.mk.injEq, Bool.false_eq_true, and_false,
          false_and] at ha
        exact ha.1.elim
      | (fst, false) :: rest =>
        simp only [SignedList.is_true, mem_cons, forall_eq_or_imp, Bool.false_eq_true, Prod.forall,
          Bool.forall_bool, imp_false, implies_true, and_true, false_and, cons_append, cons.injEq,
          Prod.mk.injEq] at ha
        exact ha.1.elim
    | (some c, true) :: tail2 =>
      change SignedList.PosNegData ([(a, false), (c, true)] ++ _ ) at h
      apply SignedList.PosNegData.of_append at h
      rcases h.1 with ⟨a3, a4, ha34⟩
      match a3 with
      | [] =>
        simp only [SignedList.is_true_nil, nil_append, true_and] at ha34
        have := ha34.1.1 (c, true) (by simp [← ha34.1.2])
        simp at this
      | head :: tail =>
        simp only [cons_append, cons.injEq] at ha34
        have := (ha34.1.1 (a, false) (by simp [← ha34.1.2.2.1]))
        simp at this

noncomputable def SemiThueData.reversing.to_grid_style_NegPos_to_PosNeg (h : SemiThueData reversing a b) (ha : SignedList.NegPosData a)
    (hb : SignedList.PosNegData b) :
    Σ b', SemiThueData grid_style (SignedList.to_SignedOptionList a) b' ×
    SignedList.NegPosData (SignedList.to_SignedOptionList a) × SignedList.PosNegData b' ×
    PLift (toSignedList b' = b) := by
  rcases grid_style_of_reversing h with ⟨b', gr, b'_is, pt_b⟩
  use b'
  constructor
  · exact gr
  constructor
  · exact SignedList.toSignedOptionList_NegPosData ha
  constructor
  · apply PosNegData_of_toSignedList_PosNeg_and_irreducible _ pt_b
    rw [b'_is.1]
    exact hb
  exact b'_is
