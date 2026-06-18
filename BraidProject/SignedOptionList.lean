import BraidProject.SignedList
import BraidProject.Additions.List

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

@[simp]
theorem toList_append : toList (a ++ b) = toList a ++ toList b := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rcases head with a | b
    · exact ih
    simp only [List.cons_append, toList_cons_some, List.cons.injEq, true_and]
    exact ih

theorem toList_len(a : List (Option α × Bool)) : (toList a).length ≤ a.length := by
  induction a with
  | nil => simp [toList]
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp only [toList, List.length_cons, ge_iff_le]
      omega
    | (some a, true) =>
      simp [toList, ih]
    | (some a, false) =>
      simp [toList, ih]

theorem toList_reverse : toList a.reverse = (toList a).reverse := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    have : head :: tail = [head] ++ tail := by rfl
    rw [this, toList_append, List.reverse_append, toList_append, List.reverse_append, ih, List.append_cancel_left_eq]
    match head with
    | (none, b) => simp [toList]
    | (some n, b) => simp [toList]

theorem toList_eq_append (h : toList a = b ++ c) :
    ∃ a₁ a₂, a = a₁ ++ a₂ ∧ toList a₁ = b ∧ toList a₂ = c := by
  induction a generalizing b c with
  | nil =>
    simp only [toList, List.nil_eq, List.append_eq_nil_iff] at h
    use [], []
    simp [h.1, h.2]
  | cons head tail ih =>
    match head with
    | (none, b) =>
      simp only [toList] at h
      rcases ih h with ⟨a1, a2, a_is, b_is, c_is⟩
      use (none, b) :: a1, a2
      simp_all [toList]
    | (some d, e) =>
      match b with
      | [] =>
        match c with
        | [] => simp [toList] at h
        | c1 :: c2 =>
          simp only [toList, List.nil_append, List.cons.injEq] at h
          use [], (some d, e) :: tail
          simp [← h.1, ← h.2, toList]
      | b1 :: b2 =>
        simp only [toList, List.cons_append, List.cons.injEq] at h
        match b2 with
        | [] =>
          use [(some d, e)], tail
          simp_all [toList]
        | b21 :: b22 =>
          rcases ih h.2 with ⟨a1, a2, a_is, b_is, c_is⟩
          use (some d, e) :: a1, a2
          simp_all [toList]

theorem toList_eq_append_cases {n : List (α)} (h : toList b = n ++ q) :
  n = [] ∨ q = [] ∨ ∃ b1 b2, b1.length > 0 ∧ b2.length > 0 ∧
          b = b1 ++ b2 ∧ toList b1 = n ∧ toList b2 = q := by
  have := SignedOptionList.toList_eq_append h
  rcases this with ⟨a₁, a₂, b_is, n_is, q_is⟩
  match a₁ with
  | [] => left; rw [← n_is]; simp
  | head₁ :: tail₁ =>
    match a₂ with
    | [] => right; left; rw [← q_is]; simp
    | head₂ :: tail₂ =>
      right; right
      use head₁ :: tail₁, head₂ :: tail₂
      simp_all

theorem toList_prefix_append_cases {α : Type} {n q : List α} {b : List (Option α × Bool)}
  (h : toList b <+:  n ++ q) (hn : n.length > 0) :
  toList b <+: n ∨ ∃ (b₁ b₂ : List (Option α × Bool)), b₁.length > 0 ∧ b₂.length > 0 ∧
  b = b₁ ++ b₂ ∧
    toList b₁ = n ∧ toList b₂ <+: q := by
  rcases List.IsPrefix.append_cases h with one | two
  · left
    exact one
  rcases two with ⟨b1, b1_len, b_is, b1_pref⟩
  right
  rcases SignedOptionList.toList_eq_append b_is with ⟨a3, a4, a_is, a3a1, m4⟩
  use a3, a4
  constructor
  · have H := SignedOptionList.toList_len a3
    rw [a3a1] at H
    omega
  constructor
  · have H := SignedOptionList.toList_len a4
    rw [m4] at H
    omega
  aesop



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

@[simp]
theorem  toList_invRev : SignedOptionList.toList (FreeGroup.invRev a) = (SignedOptionList.toList a).reverse := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [FreeGroup.invRev_cons, SignedOptionList.toList_append, ih]
    match head with
    | (none, b) => simp [SignedOptionList.toList, FreeGroup.invRev]
    | (some n, b) => simp [SignedOptionList.toList, FreeGroup.invRev]

lemma toList_invRev_eq_nil_iff : SignedOptionList.toList (FreeGroup.invRev a) = [] ↔ SignedOptionList.toList a = [] := by
  rw [toList_invRev, List.reverse_eq_nil_iff]

lemma toList_invRev_eq_singleton_iff : SignedOptionList.toList (FreeGroup.invRev a) = [i] ↔ SignedOptionList.toList a = [i] := by
  rw [toList_invRev]
  refine ⟨fun h => ?_, fun h => by rw [h]; rfl⟩
  have := congr_arg List.reverse h
  simpa using this

lemma toList_invRev_eq_pair_iff : SignedOptionList.toList (FreeGroup.invRev a) = [i, j] ↔ SignedOptionList.toList a = [j, i] := by
  rw [toList_invRev]
  refine ⟨fun h => ?_, fun h => by rw [h]; rfl⟩
  have := congr_arg List.reverse h
  simpa using this

theorem toList_invRev_length : (SignedOptionList.toList (FreeGroup.invRev a)).length =
    (SignedOptionList.toList a).length := by
  rw [toList_invRev]
  simp only [List.length_reverse]

theorem toList_invRev_eq_append_cases {m q : List α}
    (h : toList (FreeGroup.invRev a) = (m ++ q)) :
   m = [] ∨ q = [] ∨ ∃ (a1 a2 : List (Option α × Bool)), a1.length > 0 ∧ a2.length > 0 ∧
        FreeGroup.invRev a = (FreeGroup.invRev a1) ++ (FreeGroup.invRev a2) ∧ toList (FreeGroup.invRev a1) = m ∧ toList (FreeGroup.invRev a2) = q  := by
  induction m generalizing a q with
  | nil => exact Or.inl rfl
  | cons m1 m2 ih =>
    right
    match q with
    | [] => exact Or.inl rfl
    | q1 :: q2 =>
      right
      rcases SignedOptionList.toList_eq_append h with ⟨a1, a2, a_is, a1s, a2s⟩
      use FreeGroup.invRev a1, FreeGroup.invRev a2
      have := SignedOptionList.toList_len a1
      have := SignedOptionList.toList_len a2
      have a1le := congr_arg List.length a1s
      have a2le := congr_arg List.length a2s
      simp [] at a1le
      simp [] at a2le
      have a1_len : a1.length > 0 := by omega
      have a2_len : a2.length > 0 := by omega
      simp_all

theorem toList_invRev_prefix_append_cases {m q : List α}
    (h : toList (FreeGroup.invRev a) <+: (m ++ q)) :
    toList (FreeGroup.invRev a) <+: m ∨
    ∃ a1 a2, a1.length > 0 ∧ a = a1 ++ a2 ∧
    toList (FreeGroup.invRev a2) = m ∧ toList (FreeGroup.invRev a1) <+: q := by
  rcases List.IsPrefix.append_cases h with hp | ⟨extra, h_len, h_eq, h_pref⟩
  · exact Or.inl hp
  refine Or.inr ?_
  rcases SignedOptionList.toList_eq_append h_eq with ⟨b1, b2, b_is, b1s, b2s⟩
  refine ⟨FreeGroup.invRev b2, FreeGroup.invRev b1, ?_, ?_, ?_, ?_⟩
  · rw [FreeGroup.invRev_length]
    have := SignedOptionList.toList_len b2
    rw [b2s] at this
    omega
  · have ha : a = FreeGroup.invRev (b1 ++ b2) := by
      rw [← b_is, FreeGroup.invRev_invRev]
    rw [ha, FreeGroup.invRev_append]
  · rw [FreeGroup.invRev_invRev]; exact b1s
  · rw [FreeGroup.invRev_invRev, b2s]; exact h_pref

end SignedOptionList

#min_imports
