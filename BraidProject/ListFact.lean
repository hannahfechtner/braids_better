theorem list_splits_somewhere {a b c d : List α} (h : a ++ b = c ++ d) :
    a = c ∨ (∃ to_middle, a = c ++ to_middle ∧ d = to_middle ++ b) ∨
    (∃ from_middle, a ++ from_middle = c ∧ b = from_middle ++ d) := by
  induction a generalizing b c d
  · simp at h
    match c with
    | [] => left; rfl
    | c1 :: cr =>
      right; right
      apply Exists.intro (c1 :: cr)
      simp [h]
  rename_i a1 ar ih
  match c with
  | [] =>
    right
    left
    apply Exists.intro (a1 :: ar)
    simp [h]
  | c1 :: cr =>
    simp at h
    specialize ih h.2
    rw [← h.1]
    simp
    exact ih
