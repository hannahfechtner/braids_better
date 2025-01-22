theorem list_splits_somewhere {a b c d : List α} (h : a ++ b = c ++ d) :
    a = c ∨ (∃ to_middle, a = c ++ to_middle ∧ d = to_middle ++ b) ∨
    (∃ from_middle, a ++ from_middle = c ∧ b = from_middle ++ d) := by
  sorry
