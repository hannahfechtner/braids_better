import Mathlib.GroupTheory.FreeGroup.Basic
import BraidProject.SignedOptionList

theorem FreeGroup.invRev_eq_nil_iff : FreeGroup.invRev a = [] ↔ a = [] := by
  simp [FreeGroup.invRev]

theorem FreeGroup.invRev_eq_singleton_iff : FreeGroup.invRev a = [(i, b)] ↔ a = [(i, !b)] := by
  simp [FreeGroup.invRev]

theorem FreeGroup.invRev_eq_pair_iff : FreeGroup.invRev a = [(i, b), (j, c)] ↔ a = [(j, !c), (i, !b)] := by
  constructor
  · intro h
    apply congr_arg FreeGroup.invRev at h
    rw [FreeGroup.invRev_invRev] at h
    simp [h, FreeGroup.invRev]
  intro h
  simp [FreeGroup.invRev, h]


open SignedList

def FreeGroup.invRev_false (h : is_true a) : is_false (FreeGroup.invRev a) := by
  simp [is_false, FreeGroup.invRev]
  intro a1 a1_in
  specialize h (a1, false) a1_in
  simp at h

def FreeGroup.invRev_true (h : is_false a) : is_true (FreeGroup.invRev a) := by
  simp [is_true, FreeGroup.invRev]
  intro a1 a1_in
  specialize h (a1, true) a1_in
  simp at h

theorem SignedOptionList.toSignedList_invRev : SignedOptionList.toSignedList (FreeGroup.invRev a) =
  FreeGroup.invRev (SignedOptionList.toSignedList a) := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [FreeGroup.invRev_cons, SignedOptionList.toSignedList_append, ih]
    match head with
    | (none, b) => simp [SignedOptionList.toSignedList, FreeGroup.invRev]
    | (some n, b) => simp [SignedOptionList.toSignedList, FreeGroup.invRev]
