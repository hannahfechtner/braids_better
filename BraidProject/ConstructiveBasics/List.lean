def List.cases_C (a : List α) : PLift (a = []) ⊕ PLift (a.length > 0) :=
  match ha : a.length with
  | 0 => Sum.inl ⟨List.length_eq_zero_iff.mp ha⟩
  | Nat.succ n => Sum.inr ⟨by simp⟩

def List.append_eq_append_sum {α} : ∀ {a b c d : List α}, a ++ b = c ++ d →
    (Σ m : List α, PLift (c = a ++ m ∧ b = m ++ d)) ⊕
    (Σ m : List α, PLift (a = c ++ m ∧ d = m ++ b))
  | [], b, c, d, h => .inl ⟨c, ⟨rfl, by simpa using h⟩⟩
  | x :: rest, b, [], d, h => .inr ⟨x :: rest, ⟨by simp, by simpa using h.symm⟩⟩
  | x :: rest, b, y :: rest', d, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hxy, heq⟩ := h
    have ih := append_eq_append_sum heq
    match ih with
    | .inl ⟨m, hm⟩ =>
      exact .inl ⟨m, ⟨by rw [hxy, hm.down.1]; rfl, hm.down.2⟩⟩
    | .inr ⟨m, hm⟩ =>
      exact .inr ⟨m, ⟨by rw [hxy, hm.down.1]; rfl, hm.down.2⟩⟩
