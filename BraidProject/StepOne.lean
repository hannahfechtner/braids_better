import BraidProject.MoveOnes

namespace Braid

open List SignedList SignedOptionList

def distinct_pair_infix_eq (b_ne : b1 ≠ b2) (h : a ++ [b1, b2] ++ c = d ++ [b1, b2] ++ e) :
  PLift (a = d ∧ c = e) ⊕ (Σ a1 a2, PLift (a = a1 ++ [b1, b2] ++ a2 ∧ d = a1 ∧ e = a2 ++ [b1, b2] ++ c)) ⊕
  (Σ c1 c2, PLift (c = c1 ++ [b1, b2] ++ c2 ∧ d = a ++ [b1, b2] ++ c1 ∧ e = c2)) := by
  induction a generalizing b1 b2 c d e
  · simp only [nil_append, cons_append, append_assoc] at h
    simp only [nil_eq, append_assoc, cons_append, nil_append, append_eq_nil_iff, reduceCtorEq,
      and_false, false_and]
    match d with
    | [] =>
      left
      simp only [nil_append, cons.injEq, true_and] at h
      exact ⟨rfl, h⟩
    | d1 :: [] =>
      simp only [cons_append, nil_append, cons.injEq] at h
      left
      rw [h.2.1] at b_ne
      constructor
      simp at b_ne
    | d1 :: d2 :: dr =>
      simp only [cons_append, cons.injEq] at h
      right; right
      use dr, e
      constructor
      simp only [h, and_self]
  rename_i a1 ar ih
  match d with
  | [] =>
    match ar with
    | [] => simp [b_ne] at h
    | a2 :: arr =>
      simp only [cons_append, append_assoc, nil_append, cons.injEq] at h
      right; left
      use [], arr
      constructor
      simp [h]
  | d1 :: [] =>
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq] at h
    match ar with
    | [] => left; constructor; grind
    | a2 :: a3 :: arr =>
      right; left
      use [d1], arr
      constructor
      grind
    | a2 :: [] =>
      simp only [cons_append, nil_append, cons.injEq] at h
      exfalso
      apply b_ne
      exact (h.2.2.1)
  | d1 :: d2 :: dr =>
    simp only [cons_append, append_assoc, nil_append, cons.injEq] at h
    have H1 : ar ++ b1 :: b2 :: c  = ar ++ [b1, b2] ++ c := by simp
    have H : d2 :: (dr ++ b1 :: b2 :: e) = (d2 :: dr) ++ [b1, b2] ++ e := by simp
    rw [H1, H] at h
    specialize ih b_ne h.2
    rcases ih with h1 | h2 | h3
    · left
      simp only [cons.injEq]
      constructor; exact ⟨⟨h.1, h1.1.1⟩, h1.1.2⟩
    · rcases h2 with ⟨a1', a2', spec⟩
      right; left
      use d1 :: a1', a2'
      rw [spec.1.1, spec.1.2.1, spec.1.2.2, h.1]
      constructor; simp
    rcases h3 with ⟨c1', c2', spec⟩
    right; right
    use c1', c2'
    rw [spec.1.1, spec.1.2.1, spec.1.2.2, h.1]
    constructor; simp

private theorem eq_nil_of_toSignedList_nil_between_false_true_irreducible
    (h : irreducible ((some d, false) :: (L ++ [(some e, true)])))
    (h2 : toSignedList L = []) : L = [] := by
  induction L
  · rfl
  rename_i head tail ih
  match head with
  | (some a, snd) =>
    simp [toSignedList] at h2
  | (none, true) =>
    specialize h d
    apply Empty.elim
    apply h.1
    use [], tail ++ [(some e, true)]
    constructor
    simp
  | (none, false) =>
    specialize ih (irreducible_none_false_swap _ (irreducible_tail h))
      (toSignedList_tail_eq_nil_of_eq_nil h2)
    rw [ih] at h
    specialize h e
    apply Empty.elim
    apply h.2.1
    use [(some d, false)], []
    constructor
    simp

private def split_of_toSignedList_singleton_true (hi : irreducible ((some d, false) :: L))
    (h : [(b2, true)] = toSignedList L) :
    Σ L2, PLift (L = (some b2, true) :: L2 ∧ toSignedList L2 = []) := by
  induction L using List.reverseRecOn
  · simp at h
  rename_i train caboose ih
  have H : irreducible ((some d, false) :: train) := by
    rw [← List.cons_append] at hi
    apply (irreducible_append hi).1
  specialize ih H
  match caboose with
  | (none, snd) =>
    simp only [toSignedList_append, toSignedList, append_nil] at h
    rcases ih h with ⟨L2, spec⟩
    use L2 ++ [(none, snd)]
    constructor
    simp [spec.1, toSignedList]
  | (some e, snd2) =>
    simp only [toSignedList_append, toSignedList] at h
    have H1 : [(b2, true)] = [].concat (b2, true) := by simp
    have H2 : toSignedList train ++ [(e, snd2)] = (toSignedList train).concat (e, snd2) := by simp
    rw [H1, H2] at h
    use []
    constructor
    have := List.concat_inj.mp h
    simp only [nil_eq, Prod.mk.injEq, Bool.true_eq] at this
    rw [this.2.2] at hi
    simp [eq_nil_of_toSignedList_nil_between_false_true_irreducible hi this.1, this]

def split_of_toSignedList_eq_pair (h : [(b1, false), (b2, true)] = toSignedList L)
    (hi : irreducible L) : Σ L1 L2, PLift (L = L1 ++ [(some b1, false), (some b2, true)] ++ L2 ∧
    [] = toSignedList L1 ∧ [] = toSignedList L2) := by
  induction L
  · simp at h
  rename_i head tail ih
  match head with
  | (none, snd) =>
    simp [toSignedList] at h
    specialize ih h (irreducible_tail hi)
    rcases ih with ⟨L3, L4, spec⟩
    use (none, snd) :: L3, L4
    rw [spec.1.1]
    simp [toSignedList, ← spec.1.2.1, ←  spec.1.2.2]
    exact {down := trivial}
  | (some d, snd) =>
    simp [toSignedList] at h
    simp [h.1]
    use []
    simp
    rw [h.1.2] at hi
    exact split_of_toSignedList_singleton_true hi h.2

def split_of_toSignedList_pair_prefix
    (h : [(b1, false), (b2, true)] ++ c = toSignedList L) (hi : irreducible L) :
    Σ L1 L2, PLift (L = L1 ++ [(some b1, false), (some b2, true)] ++ L2 ∧
    [] = toSignedList L1 ∧ c = toSignedList L2) := by
  induction L using List.reverseRecOn generalizing c
  · simp at h
  rename_i train caboose ih
  match caboose with
  | (none, snd) =>
    simp only [toSignedList_append, toSignedList, List.append_nil] at h
    rcases ih h (irreducible_append hi).1 with ⟨L3, L4, spec⟩
    use L3, L4 ++ [(none, snd)]
    rw [← spec.1.2.1, spec.1.2.2, spec.1.1]
    constructor; simp [toSignedList]
  | (some d, bo) =>
    induction c using List.reverseRecOn
    · rw [List.append_nil] at h
      exact split_of_toSignedList_eq_pair h hi
    rename_i train1 caboose1 _
    simp only [cons_append, nil_append, toSignedList_append, toSignedList] at h
    have H1 : (b1, false) :: (b2, true) :: (train1 ++ [caboose1]) =
      ((b1, false) :: (b2, true) :: train1).concat caboose1 := by simp
    have H2 : toSignedList train ++ [(d, bo)] = (toSignedList train).concat (d, bo) := by simp
    rw [H1, H2] at h
    rcases ih (List.concat_inj.mp h).1 (irreducible_append hi).1 with ⟨L1, L2, spec⟩
    use L1, L2 ++ [(some d, bo)]
    constructor
    simp [spec.1, toSignedList, (List.concat_inj.mp h).2]


def split_of_toSignedList_pair_infix (h : a ++ [(b1, false), (b2, true)] ++ c = toSignedList L)
    (hi : irreducible L) : Σ L1 L2, PLift (L = L1 ++ [(some b1, false), (some b2, true)] ++ L2 ∧
    a = toSignedList L1 ∧ c = toSignedList L2) := by
  induction L generalizing a c
  · simp at h
  rename_i headl taill ihl
  match headl with
  | (none, snd) =>
    rcases ihl h (irreducible_tail hi) with ⟨L1, L2, spec⟩
    use (none, snd) :: L1, L2
    constructor
    simp [spec.1, toSignedList]
  | (some d, bo) =>
    match a with
    | [] =>
      rw [List.nil_append] at h
      exact split_of_toSignedList_pair_prefix h hi
    | a1 :: ar =>
      simp only [List.cons_append, toSignedList, List.cons.injEq] at h
      rcases ihl h.2 (irreducible_tail hi) with ⟨L1, L2, spec⟩
      use (some d, bo) :: L1, L2
      constructor
      simp [spec.1, h.1, toSignedList]

def giant_list_split {w : List (Option ℕ × Bool)}
    (h : toSignedList w ++ [(c1, false), (c2, true)] ++ toSignedList t =
    e ++ [(c1, false), (c2, true)] ++ f) (ptw : irreducible w) (ptt : irreducible t) :
    PLift (toSignedList w = e ∧ toSignedList t = f) ⊕
    (Σ w1 w2, PLift (w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = toSignedList w1 ∧
    f = toSignedList w2 ++ [(c1, false), (c2, true)] ++ toSignedList t)) ⊕
    (Σ t1 t2, PLift (t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧
    e = toSignedList w ++ [(c1, false), (c2, true)] ++ toSignedList t1 ∧
    f = toSignedList t2)) := by
  rcases distinct_pair_infix_eq (by simp) h with h1 | h2 | h3
  · left; exact h1
  · rcases h2 with ⟨a1, a2, spec⟩
    rcases split_of_toSignedList_pair_infix spec.1.1.symm ptw with ⟨L3, L4, speckle⟩
    right; left
    use L3, L4
    constructor
    simp [spec.1, speckle.1]
  rcases h3 with ⟨a1, a2, spec⟩
  rcases split_of_toSignedList_pair_infix spec.1.1.symm ptt with ⟨L3, L4, speckle⟩
  right; right
  use L3, L4
  constructor
  simp [spec.1, speckle.1]

noncomputable def rg_of_rev_rel' (d1)
    (gr : SemiThue grid_style (SignedList.to_SignedOptionList a) b')
    (b'_is : toSignedList b' = e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b')
    (rel_holds : grid_style [(some c1, false), (some c2, true)] d1) :
    Σ b', SemiThue grid_style (SignedList.to_SignedOptionList a) b' ×
    PLift (toSignedList b' = e ++ (toSignedList d1) ++ f) × irreducible b' := by
  have H1 : [(c1, false), (c2, true)].InfixData (toSignedList b') := by
    rw [b'_is]
    use e, f
    constructor; rfl
  rcases (pairsTogether_of_irreducible pt_b) b' (InfixData.refl b') c1 c2 H1 with ⟨w, t, hwt⟩
  rw [← hwt.1, toSignedList_append, toSignedList_append, toSignedList] at b'_is
  rw [← hwt.1] at pt_b
  have ptw : irreducible w := (irreducible_append (irreducible_append pt_b).1).1
  have ptt : irreducible t := (irreducible_append pt_b).2
  rcases distinct_pair_infix_eq (by simp) b'_is with h1 | h2 | h3
  · use move_ones (w ++ d1 ++ t)
    constructor
    · apply SemiThue.trans gr
      rw [← hwt.1]
      exact SemiThue.trans (SemiThue.step rel_holds) equiv_move_ones
    constructor
    constructor
    · rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, h1.1.1, h1.1.2]
    exact move_ones_irreducible
  · rcases h2 with ⟨a1, a2, spec⟩
    rcases split_of_toSignedList_pair_infix spec.1.1.symm ptw with ⟨w1, w2, speckle⟩
    use move_ones (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
    constructor
    · apply SemiThue.trans gr
      rw [← hwt.1]
      have H : SemiThue grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t) := by
        apply SemiThue.append_right
        rw [speckle.1.1]
        exact SemiThue.append_right (SemiThue.append_right (SemiThue.append_left
          (SemiThue.of_rel rel_holds)))
      apply H.trans equiv_move_ones
    constructor
    · have e_eq : e = toSignedList w1 := spec.1.2.1.trans speckle.1.2.1
      have f_eq : f = toSignedList w2 ++ [(c1, false), (c2, true)] ++ toSignedList t := by
        rw [spec.1.2.2, speckle.1.2.2]
      rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, e_eq, f_eq]
      constructor
      simp [toSignedList, toSignedList_append]
    exact move_ones_irreducible
  rcases h3 with ⟨a1, a2, spec⟩
  rcases split_of_toSignedList_pair_infix spec.1.1.symm ptt with ⟨t1, t2, speckle⟩
  use move_ones (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
  constructor
  · apply SemiThue.trans gr
    rw [← hwt.1]
    have H : SemiThue grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2) := by
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
      apply SemiThue.append_left
      have t_eq : t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 := speckle.1.1
      rw [List.append_assoc] at t_eq
      rw [t_eq]
      exact SemiThue.append_left
          (SemiThue.append_left (SemiThue.append_right (SemiThue.of_rel rel_holds)))
    exact H.trans equiv_move_ones
  constructor
  · have e_eq : e = toSignedList w ++ [(c1, false), (c2, true)] ++ toSignedList t1 := by
      rw [spec.1.2.1, speckle.1.2.1]
    have f_eq : f = toSignedList t2 := spec.1.2.2.trans speckle.1.2.2
    rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, e_eq, f_eq]
    exact {down := by simp [toSignedList, toSignedList_append]}
  exact move_ones_irreducible

noncomputable def rg_of_rev_rel (d1)
    (gr : SemiThue grid_style (SignedList.to_SignedOptionList a) b')
    (b'_is : toSignedList b' = e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b')
    (rel_holds : grid_style [(some c1, false), (some c2, true)] d1) :
    Σ b', SemiThue grid_style (SignedList.to_SignedOptionList a) b' ×
    PLift (toSignedList b' = e ++ (toSignedList d1) ++ f) × irreducible b' := by
  have H1 : [(c1, false), (c2, true)].InfixData (toSignedList b') := by
    rw [b'_is]
    use e, f
    constructor; rfl
  rcases (pairsTogether_of_irreducible pt_b) b' (InfixData.refl b') c1 c2 H1 with ⟨w, t, hwt⟩
  rw [← hwt.1, toSignedList_append, toSignedList_append, toSignedList] at b'_is
  rw [← hwt.1] at pt_b
  have ptw : pairsTogether w :=
    (pairsTogether_append (pairsTogether_append (pairsTogether_of_irreducible pt_b)).1).1
  have ptt : pairsTogether t := by
    rw [List.append_assoc] at pt_b
    exact (pairsTogether_append (pairsTogether_append (pairsTogether_of_irreducible pt_b)).2).2
  have := giant_list_split b'_is (irreducible_append (irreducible_append pt_b).1).1
    (irreducible_append pt_b).2
  rcases this with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
  · use move_ones (w ++ d1 ++ t)
    constructor
    · apply SemiThue.trans gr
      rw [← hwt.1]
      exact SemiThue.trans (SemiThue.step rel_holds) equiv_move_ones
    constructor
    constructor
    · rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, h2.1.1,
        h2.1.2]
    exact move_ones_irreducible
  · use move_ones (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
    constructor
    · apply SemiThue.trans gr
      rw [← hwt.1]
      have H : SemiThue grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t) := by
        apply SemiThue.append_right
        rw [hw.1.1]
        exact SemiThue.append_right (SemiThue.append_right (SemiThue.append_left
          (SemiThue.of_rel rel_holds)))
      apply H.trans equiv_move_ones
    constructor
    · rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, hw.1.2.1, hw.1.2.2]
      constructor
      simp [toSignedList, toSignedList_append]
    exact move_ones_irreducible
  use move_ones (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
  constructor
  · apply SemiThue.trans gr
    rw [← hwt.1]
    have H : SemiThue grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2) := by
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
      apply SemiThue.append_left
      rw [List.append_assoc, List.append_assoc] at ht
      rw [ht.1.1]
      exact SemiThue.append_left
          (SemiThue.append_left (SemiThue.append_right (SemiThue.of_rel rel_holds)))
    exact H.trans equiv_move_ones
  constructor
  · rw [toSignedList_move_ones, toSignedList_append, toSignedList_append, ht.1.2.1, ht.1.2.2]
    exact {down := by simp [toSignedList, toSignedList_append]}
  exact move_ones_irreducible

noncomputable def grid_style_of_reversing (h : SemiThue reversing a b) :
    Σ b', SemiThue grid_style (SignedList.to_SignedOptionList a) b' × PLift
    (toSignedList b' = b) × irreducible b' := by
  have H := SemiThue.toSemiThueDerivation h
  induction H with
  | refl =>
    exact ⟨SignedList.to_SignedOptionList _, (SemiThue.refl,
      {down := toSignedList_toSignedOptionList}, SignedList.toSignedOptionList_irreducible)⟩
  | step h1 h2 ih =>
    rename_i c d e f g
    rcases ih (SemiThueDerivation.toSemiThue h1) with ⟨b', gr, b'_is, pt_b⟩
    cases h2 with
    | basic h_dist =>
      apply Nat.eq_of_dist_eq_zero at h_dist
      apply rg_of_rev_rel ([(none, true), (none, false)]) gr  b'_is.1 pt_b
      rw [h_dist]
      exact .basic _
    | apart h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, false)]) gr b'_is.1 pt_b (.apart h_dist)
    | close h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, true), (some j, false), (some i, false)])
        gr b'_is.1 pt_b (.close h_dist)

def in_order_of_rm_irr (h : SignedList.PosNegData (toSignedList L)) (h2 : irreducible L) :
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
  | (none, true) =>
    use (none, true) :: a1, a2
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
  | (some a, true) =>
    use (some a, true) :: a1, a2
    constructor
    constructor
    · intro x hx
      simp only [mem_cons] at hx
      rcases hx with h1 | h2
      · simp [h1]
      exact ha.1.1 _ h2
    constructor
    · exact ha.1.2.1
    simp [ha.1.2.2]
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
        have := ha34.1.2.2
        simp only [nil_append] at this
        rw [← this] at ha34
        have := ha34.1.2.1 (c, true) (by simp)
        simp at this
      | head :: tail =>
        have := ha34.1.2.2
        simp only [cons_append, cons.injEq] at this
        rw [← this.1] at ha34
        simp only [SignedList.is_true, mem_cons, forall_eq_or_imp, Bool.false_eq_true, Prod.forall,
          Bool.forall_bool, imp_false, implies_true, and_true, false_and, cons_append, cons.injEq,
          true_and] at ha34
        exact ha34.1.elim

noncomputable def stepOne_mid (h : SemiThue reversing a b) (ha : SignedList.NegPosData a) :
    Σ b', SemiThue grid_style (SignedList.to_SignedOptionList a) b' ×
    SignedList.NegPosData (SignedList.to_SignedOptionList a) ×  PLift (toSignedList b' = b) := by
  rcases grid_style_of_reversing h with ⟨b', gr, b'_is, pt_b⟩
  use b'
  constructor
  · exact gr
  constructor
  · exact SignedList.toSignedOptionList_NegPosData ha
  exact b'_is

noncomputable def stepOne (h : SemiThue reversing a b) (ha : SignedList.NegPosData a)
    (hb : SignedList.PosNegData b) :
    Σ b', SemiThue grid_style (SignedList.to_SignedOptionList a) b' ×
    SignedList.NegPosData (SignedList.to_SignedOptionList a) × SignedList.PosNegData b' ×
    PLift (toSignedList b' = b) := by
  rcases grid_style_of_reversing h with ⟨b', gr, b'_is, pt_b⟩
  use b'
  constructor
  · exact gr
  constructor
  · exact SignedList.toSignedOptionList_NegPosData ha
  constructor
  · apply in_order_of_rm_irr _ pt_b
    rw [b'_is.1]
    exact hb
  exact b'_is
