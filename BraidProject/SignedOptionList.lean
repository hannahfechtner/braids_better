import BraidProject.SignedList
import Mathlib.Tactic.Use

namespace SignedOptionList

def toList : (a : List (Option α × Bool)) → List α
  | [] => []
  | (some a, _) :: c => a :: toList c
  | (none, _) :: c => toList c

@[simp]
def toList_nil : toList ([] : List (Option α × Bool)) = [] := rfl

@[simp]
theorem toList_cons_some : toList ((some a, bo) :: b) = a :: toList b := rfl

@[simp]
theorem toList_cons_none : toList ((none, bo) :: b) = toList b := rfl

theorem toList_append : toList (a ++ b) = toList a ++ toList b := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rcases head with a | b
    · exact ih
    simp only [List.cons_append, toList_cons_some, List.cons.injEq, true_and]
    exact ih

def toSignedList {α : Type} (L : List (Option α × Bool)) : List (α × Bool) :=
  match L with
  | [] => []
  | (some a, b) :: c => (a, b) :: toSignedList c
  | (none, _) :: c => toSignedList c

@[simp]
theorem toSignedList_nil : toSignedList ([] : List (Option α × Bool)) = [] := rfl

@[simp]
theorem toSignedList_append : toSignedList (L1 ++ L2) = toSignedList L1 ++ toSignedList L2 := by
  induction L1
  · simp
  rename_i head tail ih
  match head with
  | (none, _) => simp [toSignedList, ih]
  | (some _, _) => simp [toSignedList, ih]

theorem toSignedList_eq_append (h : toSignedList a = b ++ c) :
    ∃ a₁ a₂, a = a₁ ++ a₂ ∧ toSignedList a₁ = b ∧ toSignedList a₂ = c := by
  induction a generalizing b c with
  | nil =>
    simp only [toSignedList, List.nil_eq, List.append_eq_nil_iff] at h
    use [], []
    simp [h.1, h.2]
  | cons head tail ih =>
    match head with
    | (none, b) =>
      simp only [toSignedList] at h
      rcases ih h with ⟨a1, a2, a_is, b_is, c_is⟩
      use (none, b) :: a1, a2
      simp_all [toSignedList]
    | (some d, e) =>
      match b with
      | [] =>
        match c with
        | [] => simp [toSignedList] at h
        | c1 :: c2 =>
          simp only [toSignedList, List.nil_append, List.cons.injEq] at h
          use [], (some d, e) :: tail
          simp [← h.1, ← h.2, toSignedList]
      | b1 :: b2 =>
        simp only [toSignedList, List.cons_append, List.cons.injEq] at h
        match b2 with
        | [] =>
          use [(some d, e)], tail
          simp_all [toSignedList]
        | b21 :: b22 =>
          rcases ih h.2 with ⟨a1, a2, a_is, b_is, c_is⟩
          use (some d, e) :: a1, a2
          simp_all [toSignedList]

theorem toSignedList_len(a : List (Option α × Bool)) : (toSignedList a).length ≤ a.length := by
  induction a with
  | nil => simp [toSignedList]
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp only [toSignedList, List.length_cons, ge_iff_le]
      omega
    | (some a, true) =>
      simp [toSignedList, ih]
    | (some a, false) =>
      simp [toSignedList, ih]

@[simp]
theorem toSignedList_tail_eq_nil_of_eq_nil (h : toSignedList (head :: tail) = []) : toSignedList tail = [] := by
  change toSignedList ([head] ++ tail) = [] at h
  rw [toSignedList_append, List.append_eq_nil_iff] at h
  exact h.2


@[simp]
theorem toSignedList_toSignedOptionList {a : List (ℕ × Bool)} : toSignedList (SignedList.to_SignedOptionList a) = a := by
  induction a
  · rfl
  rename_i ih
  simp only [SignedList.to_SignedOptionList, List.map_cons, toSignedList, List.cons.injEq, true_and]
  exact ih

end SignedOptionList
