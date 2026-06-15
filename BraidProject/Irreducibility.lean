import BraidProject.List_C
import BraidProject.SignedOptionList
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Cast.Order.Basic

namespace Braid

open SignedOptionList

def pairAppears (L : List (Option ℕ × Bool)) := ∀ a b, List.InfixData [(a, false), (b, true)] (toSignedList L) →
    List.InfixData [(some a, false), (some b, true)] L

def pairAppears_empty : pairAppears [] := by
  unfold pairAppears
  simp only [toSignedList_nil]
  intro a b h1
  apply List.InfixData.length_le at h1
  simp at h1

def pairAppears_singleton : pairAppears [a] := by
  intro c d hcd
  exfalso
  match a with
  | (none, _) =>
    change List.InfixData [(c, false), (d, true)] [] at hcd
    apply List.InfixData.length_le  at hcd
    simp at hcd
  | (some a, b) =>
    change List.InfixData [(c, false), (d, true)] [(a, b)] at hcd
    rcases hcd with ⟨w, t, ⟨hwt⟩⟩
    apply congr_arg List.length at hwt
    simp at hwt
    omega

open List

def pairsTogether (L) := ∀ L1, InfixData L1 L → pairAppears L1

def pairsTogether_empty : pairsTogether [] := by
  unfold pairsTogether
  intro L1 hl
  rw [InfixData.of_nil hl]
  exact pairAppears_empty

def pairsTogether_append (h : pairsTogether (a ++ b)) : pairsTogether a × pairsTogether b :=
  ⟨fun L1 hl c d hcd ↦ h L1 (InfixData.append_right hl) c d hcd,
  fun L1 hl c d hcd ↦ h L1 (InfixData.append_left hl) c d hcd⟩

def irreducible (L : List (Option ℕ × Bool)) :=
  ∀ a, (InfixData [(some a, false), (none, true)] L → Empty) × (InfixData  [(none, false), (some a, true)] L → Empty) ×
   (InfixData [(none, false), (none, true)] L → Empty)

def irreducible_nil : irreducible [] := by
  unfold irreducible
  intro h
  exact ⟨InfixData.length_two_not_infix_nil, ⟨InfixData.length_two_not_infix_nil, InfixData.length_two_not_infix_nil⟩⟩

def irreducible_singleton : irreducible [a] := by
  unfold irreducible
  intro a
  constructor
  · intro h
    apply InfixData.length_le at h
    simp at h
  constructor
  · intro h
    apply InfixData.length_le at h
    simp at h
  intro h
  apply InfixData.length_le at h
  simp at h

def irreducible_tail {head : Option ℕ × Bool} {tail : List (Option ℕ × Bool)} (h : irreducible (head :: tail)) : irreducible tail := by
  intro a
  constructor
  · intro h1
    apply (h a).1
    exact InfixData.cons h1
  constructor
  · intro h1
    apply (h a).2.1
    exact InfixData.cons h1
  intro h1
  apply (h a).2.2
  exact InfixData.cons h1

def irreducible_append (h : irreducible (a ++ b)) : irreducible a × irreducible b :=
  ⟨fun x ↦ ⟨fun hx ↦ (h x).1 (InfixData.append_right hx),
      ⟨fun hx ↦ (h x).2.1 (InfixData.append_right hx), fun hx ↦ (h x).2.2 (InfixData.append_right hx)⟩⟩,
  fun x ↦ ⟨fun hx ↦ (h x).1 (InfixData.append_left hx),
      ⟨fun hx ↦ (h x).2.1 (InfixData.append_left hx), fun hx ↦ (h x).2.2 (InfixData.append_left hx)⟩⟩⟩

def SignedList.toSignedOptionList_irreducible : irreducible (SignedList.to_SignedOptionList a) := by
  induction a with
  | nil => exact irreducible_nil
  | cons head tail ih =>
    unfold SignedList.to_SignedOptionList
    intro x
    constructor
    · intro hx
      match tail with
      | [] =>
        apply InfixData.length_le at hx
        simp at hx
      | t1 :: tr =>
        exact (ih x).1 (InfixData.tail_of_cons_cons_ne hx (by simp))
    constructor
    · intro hx
      exact (ih x).2.1 (InfixData.tail_of_cons_ne hx (by simp))
    intro hx
    exact (ih x).2.2 (InfixData.tail_of_cons_ne hx (by simp))

def irreducible_cons_true (h : irreducible L) : irreducible ((a, true) :: L) := by
  intro a
  constructor
  · exact fun h1 => (h a).1 (InfixData.tail_of_cons_ne h1 (by simp))
  constructor
  · exact fun h1 => (h a).2.1 (InfixData.tail_of_cons_ne h1 (by simp))
  exact fun h1 => (h a).2.2 (InfixData.tail_of_cons_ne h1 (by simp))

def irreducible_cons_cons_bool_eq  (h : irreducible ((b1, b) :: L)) :
    irreducible ((a1, b) :: (b1, b) :: L) := by
  intro a1
  constructor
  · intro h2
    apply (h a1).1
    match b with
    | true =>
      apply InfixData.tail_of_cons_ne h2
      simp
    | false =>
      apply InfixData.tail_of_cons_cons_ne h2
      simp
  constructor
  · intro h2
    apply (h a1).2.1
    match b with
    | true =>
      apply InfixData.tail_of_cons_ne h2
      simp
    | false =>
      apply InfixData.tail_of_cons_cons_ne h2
      simp
  intro h2
  apply (h a1).2.2
  match b with
  | true =>
    apply InfixData.tail_of_cons_ne h2
    simp
  | false =>
    apply InfixData.tail_of_cons_cons_ne h2
    simp

def irreducible_cons_some_cons_some (h : irreducible ((some c, b1) :: L)) :
    irreducible ((some d, b2) :: (some c, b1) :: L) := by
  intro a1
  match b2 with
  | true =>
    constructor
    · intro h3
      apply (h a1).1
      apply InfixData.tail_of_cons_ne h3 (by simp)
    constructor
    · intro h3
      apply (h a1).2.1
      apply InfixData.tail_of_cons_ne h3 (by simp)
    intro h3
    apply (h a1).2.2
    apply InfixData.tail_of_cons_ne h3 (by simp)
  | false =>
    constructor
    · intro h3
      apply (h a1).1
      apply InfixData.tail_of_cons_cons_ne h3 (by simp)
    constructor
    · intro h3
      apply (h a1).2.1
      apply InfixData.tail_of_cons_ne h3 (by simp)
    intro h3
    apply (h a1).2.2
    apply InfixData.tail_of_cons_ne h3 (by simp)

def irreducible_none_false_swap (b) (h : irreducible ((none, false) :: L)) : irreducible ((b, false) :: L) := by
  match L with
  | [] => exact irreducible_singleton
  | (some c, true) :: tail =>
    specialize h c
    apply Empty.elim
    apply h.2.1
    use [], tail
    constructor
    simp
  | (some c, false) :: tail =>
    intro a
    constructor
    · intro h1
      apply (irreducible_tail h a).1 (InfixData.tail_of_cons_cons_ne h1 (by simp))
    constructor
    · intro h1
      apply (irreducible_tail h a).2.1 (InfixData.tail_of_cons_cons_ne h1 (by simp))
    intro h1
    apply (irreducible_tail h a).2.2 (InfixData.tail_of_cons_cons_ne h1 (by simp))
  | (none, true) :: tail =>
    specialize h 0
    apply Empty.elim
    apply h.2.2
    use [], tail
    constructor
    simp
  | (none, false) :: tail =>
    intro a
    constructor
    · intro h1
      apply (irreducible_tail h a).1 (InfixData.tail_of_cons_cons_ne h1 (by simp))
    constructor
    · intro h1
      apply (irreducible_tail h a).2.1 (InfixData.tail_of_cons_cons_ne h1 (by simp))
    intro h1
    apply (irreducible_tail h a).2.2 (InfixData.tail_of_cons_cons_ne h1 (by simp))

theorem toSignedList_tail_not_cons_true_of_irreducible_cons_none_false
    {tail : List (Option ℕ × Bool)} (h : irreducible ((none, false) :: tail))
    (h2 : toSignedList tail = (a, true) :: rest) : False := by
  have H : ∀ t L rest, L.length = t → irreducible ((none, false) :: L) → toSignedList L = (a, true) :: rest → False := by
    intro t
    induction t with
    | zero =>
      intro L rest len irr hin
      simp at len
      simp [len] at hin
    | succ n ih =>
      intro L rest len irr hin
      match L with
      | [] => simp at len
      | (none, true) :: tail1 =>
        have H := by
          apply (irr 0).2.2
          use [], tail1
          simp
          exact {down := trivial}
        cases H
      | (none, false) :: tail1 =>
        simp [toSignedList] at hin
        specialize ih tail1 rest
        simp at len
        exact ih len (irreducible_tail irr) hin
      | (some b, true) :: tail1 =>
        have H := by
          apply (irr b).2.1
          use [], tail1
          simp
          exact {down := trivial}
        cases H
      | (some b, false) :: tail1 => simp [toSignedList] at hin
  exact H _ _ _ rfl h h2

def infixData_false_true_tail_of_cons_false_toSignedList_of_irreducible_cons_none_false
    (irr : irreducible ((none, false) :: L)) (hin : InfixData [(c, false), (d, true)] ((b, false) :: toSignedList L)) :
    InfixData [(c, false), (d, true)] (toSignedList L) := by
  match hl : toSignedList L with
  | [] =>
    rw [hl] at hin
    apply InfixData.length_le at hin
    simp at hin
  | (a, true) :: tail =>
    exact (toSignedList_tail_not_cons_true_of_irreducible_cons_none_false irr hl).elim
  | (a, false) :: tail =>
    rw [hl] at hin
    apply InfixData.tail_of_cons_cons_ne hin
    simp

open List

-- a quick example to show that pairsTogether does not imply irreducible
def not_irreducible_of_pairAppears : (pairsTogether [(some a, false), (none, true)]) × (irreducible [(some a, false), (none, true)] → Empty) := by
  constructor
  · intro L1 hL1
    rcases hL1 with ⟨w, t, ⟨hwt⟩⟩
    intro c d hcd
    exfalso
    have ts_eq : toSignedList (w ++ L1 ++ t) = [(a, false)] := by
      rw [hwt]; rfl
    rw [toSignedList_append, toSignedList_append] at ts_eq
    apply congr_arg List.length at ts_eq
    apply List.InfixData.length_le at hcd
    simp only [append_assoc, length_append, length_cons, length_nil, zero_add,
      Nat.reduceAdd] at ts_eq hcd
    omega
  intro hi
  apply (hi a).1
  use [], []
  constructor
  simp

def pairAppears_of_irreducible (h : irreducible L) : pairAppears L := by
  have H : ∀ t L, L.length ≤ t → irreducible L → pairAppears L := by
    intro t
    induction t
    · intro L len
      simp only [nonpos_iff_eq_zero, length_eq_zero_iff] at len
      intro h
      rw [len]
      exact pairAppears_empty
    rename_i n ih
    intro L len irr c d h
    cases L with
    | nil =>
      apply InfixData.length_le at h
      simp at h
    | cons head tail =>
      match head with
      | (none, true) =>
        simp only [toSignedList] at h
        simp only [length_cons, add_le_add_iff_right] at len
        exact InfixData.cons <| ih tail len (irreducible_tail irr) c d h
      | (none, false) =>
        match tail with
        | [] =>
          apply InfixData.length_le at h
          simp [toSignedList] at h
        | (none, true) :: tail1 =>
          simp [toSignedList] at h
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply InfixData.cons
          exact ih tail1 (by omega) (irreducible_tail (irreducible_tail irr)) c d h
        | (none, false) :: tail1 =>
          simp only [toSignedList] at h
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply InfixData.cons
          exact ih tail1 (by omega) (irreducible_tail (irreducible_tail irr)) c d h
        | (some e, true) :: tail1 =>
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply ih ((some e, true) :: tail1) _ (irreducible_tail irr) _ _ h
          simp [len]
        | (some e, false) :: tail1 =>
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply ih ((some e, false) :: tail1) _ (irreducible_tail irr) _ _ h
          simp [len]
      | (some b, true) =>
        match tail with
        | [] =>
          apply InfixData.length_le at h
          simp [toSignedList] at h
        | (none, true) :: tail1 =>
          simp only [toSignedList] at h
          simp at len
          apply InfixData.cons
          apply InfixData.cons
          apply ih tail1
          · omega
          apply irreducible_tail (irreducible_tail irr)
          apply InfixData.tail_of_cons_ne h
          simp
        | (none, false) :: tail1 =>
          simp only [toSignedList] at h
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply InfixData.cons
          apply ih tail1
          · omega
          apply irreducible_tail (irreducible_tail irr)
          apply InfixData.tail_of_cons_ne h
          simp
        | (some e, true) :: tail1 =>
          simp only [toSignedList] at h
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply InfixData.cons
          apply ih tail1
          · omega
          apply irreducible_tail (irreducible_tail irr)
          have h3 : [(c, false), (d, true)].InfixData ((e, true) :: toSignedList tail1) := by
            apply InfixData.tail_of_cons_ne h
            simp
          apply InfixData.tail_of_cons_ne h3
          simp
        | (some c, false) :: tail1 =>
          simp only [toSignedList] at h
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply ih ((some c, false) :: tail1)
          · simp [len]
          apply irreducible_tail irr
          apply InfixData.tail_of_cons_ne h
          simp
      | (some b, false) =>
        match tail with
        | [] =>
          apply InfixData.length_le at h
          simp [toSignedList] at h
        | (none, true) :: tail1 =>
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply InfixData.cons
          apply Empty.elim
          apply (irr b).1
          use [], tail1
          simp
          exact {down := trivial}
        | (none, false) :: tail1 =>
          simp only [List.length_cons, add_le_add_iff_right] at len
          apply InfixData.cons <| InfixData.cons <| ih tail1 (by omega) (irreducible_tail (irreducible_tail irr)) _ _
            (infixData_false_true_tail_of_cons_false_toSignedList_of_irreducible_cons_none_false (irreducible_tail irr) h)
        | (some e, true) :: tail1 =>
          simp at len
          if hcd : c = b then
            if hed : e = d
              then use [], tail1; simp; exact {down := ⟨hcd, hed.symm⟩}
            else
            {
              have h3 : [(c, false), (d, true)].InfixData ((e, true) :: toSignedList tail1) := by
                apply InfixData.tail_of_cons_cons_ne h
                simp only [ne_eq, Prod.mk.injEq, and_true]
                aesop
              exact InfixData.cons <| InfixData.cons <| ih tail1 (by omega) (irreducible_tail
                (irreducible_tail irr)) _ _ (InfixData.tail_of_cons_ne h3 (by simp))
            }
          else
          {
            have h3 : [(c, false), (d, true)].InfixData (toSignedList ((some e, true) :: tail1)) := by
              apply InfixData.tail_of_cons_ne h
              simp [hcd]
            apply InfixData.cons <| InfixData.cons <| ih tail1 (by omega)
              (irreducible_tail (irreducible_tail irr)) _ _ (InfixData.tail_of_cons_ne h3 (by simp))
          }
        | (some e, false) :: tail1 =>
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply ih ((some e, false) :: tail1) (by simp [len]) (irreducible_tail irr)
          apply InfixData.tail_of_cons_cons_ne h
          simp
  exact H L.length L (by simp) h

def irreducible_infix (h : irreducible L) (h2 : InfixData L1 L) : irreducible L1 :=
  fun a ↦ ⟨fun ha ↦ (h a).1 (ha.trans h2), ⟨fun ha ↦ (h a).2.1 (ha.trans h2), fun ha ↦
        (h a).2.2 (ha.trans h2)⟩⟩

def pairsTogether_of_irreducible (h : irreducible L) : pairsTogether L := by
  intro h1 hl
  apply pairAppears_of_irreducible (irreducible_infix h hl)
