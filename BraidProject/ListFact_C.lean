noncomputable def list_splits_somewhere {a b c d : List α} (h : a ++ b = c ++ d) :
    PLift (a = c) ⊕ (Σ to_middle, PLift (a = c ++ to_middle ∧ d = to_middle ++ b)) ⊕
    (Σ from_middle, PLift (a ++ from_middle = c ∧ b = from_middle ++ d)) := by
  induction a generalizing b c d
  · simp at h
    match c with
    | [] => left; exact ⟨rfl⟩
    | c1 :: cr =>
      right; right
      exact ⟨(c1 :: cr), by simp [h]; exact ⟨trivial⟩⟩
  rename_i a1 ar ih
  match c with
  | [] =>
    right
    left
    exact ⟨(a1 :: ar), by simp [h]; exact ⟨trivial⟩⟩
  | c1 :: cr =>
    simp at h
    specialize ih h.2
    rw [← h.1]
    simp
    exact ih
