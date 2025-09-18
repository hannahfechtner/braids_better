import BraidProject.TrueFalse_C

def to_option (L : List (ℕ × Bool)) : List (Option ℕ × Bool) := (List.map (fun x ↦ (some x.1, x.2)) L)

def is_false_to_option (ha : is_false a) : is_false (to_option a) := by
  unfold to_option
  unfold is_false
  intro x hx
  simp at hx
  constructor
  rcases hx.1 with ⟨a1, h1 | h2⟩
  · rw [← h1.2]
  specialize ha (a1, true) ⟨h2.1⟩
  simp at ha
  exact ha.1.elim

def is_true_to_option (ha : is_true a) : is_true (to_option a) := by
  unfold to_option
  intro x hx
  simp only [List.mem_map, Prod.exists, Bool.exists_bool] at hx
  exact {down := by
              rcases hx with ⟨a1, spec1 | spec2⟩
              · have := (ha _ ⟨spec1.1⟩).1
                simp [this, ← spec1.2]
              rw [← spec2.2]}
