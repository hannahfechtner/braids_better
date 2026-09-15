import BraidProject.MoveOnes
import BraidProject.DataCarrying.SignedList

namespace Braid

open SignedOptionList List

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

def pair_infix_irreducible_cases {w : List (Option ℕ × Bool)}
    (h : toSignedList w ++ [(c1, false), (c2, true)] ++ toSignedList t =
    e ++ [(c1, false), (c2, true)] ++ f) (ptw : irreducible w) (ptt : irreducible t) :
    PLift (toSignedList w = e ∧ toSignedList t = f) ⊕
    (Σ w1 w2, PLift (w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = toSignedList w1 ∧
    f = toSignedList w2 ++ [(c1, false), (c2, true)] ++ toSignedList t)) ⊕
    (Σ t1 t2, PLift (t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧
    e = toSignedList w ++ [(c1, false), (c2, true)] ++ toSignedList t1 ∧
    f = toSignedList t2)) := by
  rcases distinctPairInfixCases (by simp) h with h1 | h2 | h3
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
