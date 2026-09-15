import BraidProject.DataCarrying.SignedList
import BraidProject.Additions.SignedOptionList
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Cast.Order.Basic

namespace Braid

open SignedOptionList

-- we need InfixData over List.isInfix because eventually we will need to define a function
-- on this data in StepOne_length
def pairAppears (L : List (Option ℕ × Bool)) :=
    ∀ a b, List.InfixData [(a, false), (b, true)] (toSignedList L) →
    List.InfixData [(some a, false), (some b, true)] L

def pairAppears_empty : pairAppears [] := by
  unfold pairAppears
  simp only [toSignedList_nil]
  intro a b h1
  apply List.InfixData.length_le at h1
  simp at h1

def pairAppears_singleton : pairAppears [a] := by
  intro c d hcd
  match a with
  | (none, _) =>
    apply List.InfixData.length_le  at hcd
    simp at hcd
  | (some a, b) =>
    rcases hcd with ⟨w, t, ⟨hwt⟩⟩
    apply congr_arg List.length at hwt
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons, toSignedList_cons_some, toSignedList_nil, List.length_nil, zero_add] at hwt
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
  constructor; any_goals constructor
  all_goals exact InfixData.length_two_not_infix_nil

def irreducible_singleton : irreducible [a] := by
  intro a
  constructor; any_goals constructor
  all_goals
  intro h
  apply InfixData.length_le at h
  simp at h

def irreducible_tail {head : Option ℕ × Bool} {tail : List (Option ℕ × Bool)} (h : irreducible (head :: tail)) : irreducible tail := by
  intro a
  constructor; any_goals constructor
  all_goals intro h1
  · exact (h a).1 <| InfixData.cons h1
  · exact (h a).2.1 <| InfixData.cons h1
  exact (h a).2.2 <| InfixData.cons h1

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
    constructor; any_goals constructor
    all_goals intro hx
    · match tail with
      | [] =>
        apply InfixData.length_le at hx
        simp at hx
      | t1 :: tr =>
        exact (ih x).1 (InfixData.tail_of_cons_cons_ne hx (by simp))
    · exact (ih x).2.1 (InfixData.tail_of_cons_ne hx (by simp))
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
      exact InfixData.tail_of_cons_ne h2 (by simp)
    | false =>
      exact InfixData.tail_of_cons_cons_ne h2 (by simp)
  constructor
  · intro h2
    apply (h a1).2.1
    match b with
    | true =>
      exact InfixData.tail_of_cons_ne h2 (by simp)
    | false =>
      exact InfixData.tail_of_cons_cons_ne h2 (by simp)
  intro h2
  apply (h a1).2.2
  match b with
  | true =>
    exact InfixData.tail_of_cons_ne h2 (by simp)
  | false =>
    exact InfixData.tail_of_cons_cons_ne h2 (by simp)

def irreducible_cons_some_cons_some (h : irreducible ((some c, b1) :: L)) :
    irreducible ((some d, b2) :: (some c, b1) :: L) := by
  intro a1
  match b2 with
  | true =>
    constructor
    · exact fun h3 => (h a1).1 <| InfixData.tail_of_cons_ne h3 (by simp)
    constructor
    · exact fun h3 => (h a1).2.1 <| InfixData.tail_of_cons_ne h3 (by simp)
    exact fun h3 => (h a1).2.2 <| InfixData.tail_of_cons_ne h3 (by simp)
  | false =>
    constructor
    · exact fun h3 => (h a1).1 <| InfixData.tail_of_cons_cons_ne h3 (by simp)
    constructor
    · exact fun h3 =>(h a1).2.1 <| InfixData.tail_of_cons_ne h3 (by simp)
    exact fun h3 => (h a1).2.2 <| InfixData.tail_of_cons_ne h3 (by simp)

def irreducible_none_false_swap (b) (h : irreducible ((none, false) :: L)) : irreducible ((b, false) :: L) := by
  match L with
  | [] => exact irreducible_singleton
  | (some c, true) :: tail =>
    apply Empty.elim
    apply (h c).2.1
    use [], tail
    constructor
    simp
  | (some c, false) :: tail =>
    intro a
    constructor
    · exact fun h1 => (irreducible_tail h a).1 (InfixData.tail_of_cons_cons_ne h1 (by simp))
    constructor
    · exact fun h1 => (irreducible_tail h a).2.1 (InfixData.tail_of_cons_cons_ne h1 (by simp))
    exact fun h1 => (irreducible_tail h a).2.2 (InfixData.tail_of_cons_cons_ne h1 (by simp))
  | (none, true) :: tail =>
    apply Empty.elim
    apply (h 0).2.2
    use [], tail
    constructor
    simp
  | (none, false) :: tail =>
    intro a
    constructor
    · exact fun h1 => (irreducible_tail h a).1 (InfixData.tail_of_cons_cons_ne h1 (by simp))
    constructor
    · exact fun h1 => (irreducible_tail h a).2.1 (InfixData.tail_of_cons_cons_ne h1 (by simp))
    exact fun h1 => (irreducible_tail h a).2.2 (InfixData.tail_of_cons_cons_ne h1 (by simp))

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

theorem toSignedList_tail_not_cons_true_of_irreducible_cons_none_false
    {tail : List (Option ℕ × Bool)} (h : irreducible ((none, false) :: tail))
    (h2 : toSignedList tail = (a, true) :: rest) : False := by
  have H : ∀ t L rest, L.length = t → irreducible ((none, false) :: L) → toSignedList L = (a, true) :: rest → False := by
    intro t
    induction t with
    | zero => simp_all
    | succ n ih =>
      intro L rest len irr hin
      match L with
      | [] => simp at len
      | (none, true) :: tail1 =>
        apply Empty.elim
        apply (irr 0).2.2
        use [], tail1
        constructor
        simp
      | (none, false) :: tail1 =>
        specialize ih tail1 rest
        simp only [length_cons, Nat.add_right_cancel_iff] at len
        exact ih len (irreducible_tail irr) hin
      | (some b, true) :: tail1 =>
        apply Empty.elim
        apply (irr b).2.1
        use [], tail1
        constructor
        simp
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
  · intro L1 hL1 c d hcd
    rcases hL1 with ⟨w, t, ⟨hwt⟩⟩
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
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply InfixData.cons
          exact ih tail1 (by omega) (irreducible_tail (irreducible_tail irr)) c d h
        | (none, false) :: tail1 =>
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
          simp only [length_cons, add_le_add_iff_right, Order.add_one_le_iff] at len
          apply InfixData.cons
          apply InfixData.cons
          apply ih tail1 (by omega) (irreducible_tail (irreducible_tail irr))
          exact (InfixData.tail_of_cons_ne h (by simp))
        | (none, false) :: tail1 =>
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply InfixData.cons
          exact ih tail1 (by omega) (irreducible_tail (irreducible_tail irr))
            _ _ (InfixData.tail_of_cons_ne h (by simp))
        | (some e, true) :: tail1 =>
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply InfixData.cons
          apply ih tail1 (by omega) (irreducible_tail (irreducible_tail irr))
          exact InfixData.tail_of_cons_ne (InfixData.tail_of_cons_ne h (by simp)) (by simp)
        | (some c, false) :: tail1 =>
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply ih ((some c, false) :: tail1) (by simp [len]) (irreducible_tail irr)
          exact InfixData.tail_of_cons_ne h (by simp)
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
          constructor
          simp
        | (none, false) :: tail1 =>
          simp only [List.length_cons, add_le_add_iff_right] at len
          apply InfixData.cons <| InfixData.cons <| ih tail1 (by omega) (irreducible_tail (irreducible_tail irr)) _ _
            (infixData_false_true_tail_of_cons_false_toSignedList_of_irreducible_cons_none_false (irreducible_tail irr) h)
        | (some e, true) :: tail1 =>
          simp only [length_cons, add_le_add_iff_right, Order.add_one_le_iff] at len
          if hcd : c = b then
            if hed : e = d
              then use [], tail1; simp only [nil_append, cons_append, cons.injEq, Prod.mk.injEq,
                Option.some.injEq, and_true]; exact {down := ⟨hcd, hed.symm⟩}
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
            exact InfixData.cons <| InfixData.cons <| ih tail1 (by omega)
              (irreducible_tail (irreducible_tail irr)) _ _ (InfixData.tail_of_cons_ne
              (by apply InfixData.tail_of_cons_ne h; simp [hcd]) (by simp))
        | (some e, false) :: tail1 =>
          simp only [length_cons, add_le_add_iff_right] at len
          apply InfixData.cons
          apply ih ((some e, false) :: tail1) (by simp [len]) (irreducible_tail irr)
          exact InfixData.tail_of_cons_cons_ne h (by simp)
  exact H L.length L (by simp) h

def irreducible_infix (h : irreducible L) (h2 : InfixData L1 L) : irreducible L1 :=
  fun a ↦ ⟨fun ha ↦ (h a).1 (ha.trans h2), ⟨fun ha ↦ (h a).2.1 (ha.trans h2), fun ha ↦
        (h a).2.2 (ha.trans h2)⟩⟩

def pairsTogether_of_irreducible (h : irreducible L) : pairsTogether L :=
  fun _ hl => pairAppears_of_irreducible (irreducible_infix h hl)
