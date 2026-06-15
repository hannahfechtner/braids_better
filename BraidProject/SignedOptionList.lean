import BraidProject.SignedList

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
