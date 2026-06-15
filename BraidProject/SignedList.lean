
namespace SignedList

def is_false (a : List (α × Bool)) : Prop := ∀ x , x ∈ a → x.2 = false

@[simp]
theorem is_false_nil : is_false ([] : List (α × Bool)) := by
  simp [is_false]

theorem is_false_of_append (h : is_false (a ++ b)) : is_false a ∧ is_false b := by
  constructor
  · exact fun x hx => h x (List.mem_append_left b hx)
  exact fun x hx => h x (List.mem_append_right a hx)

theorem is_false_append (h1 : is_false a) (h2 : is_false b) : is_false (a ++ b) := by
  intro x h
  simp only [List.mem_append] at h
  cases h with
  | inl h => exact h1 x h
  | inr h => exact h2 x h

theorem is_false_of_cons (h : is_false (a :: b)) : is_false [a] ∧ is_false b := by
  change is_false ([a]++b) at h
  exact is_false_of_append h

theorem is_false_cons (a : List (α × Bool)) (h : is_false a): is_false ((b, false) :: a) := by
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h2
  · simp [h1]
  exact h _ h2

theorem is_false_tail (h : is_false (x :: xs)) : is_false xs := by
  change is_false ([x] ++ xs) at h
  exact (is_false_of_append h).2


def is_true (a : List (α × Bool)) := ∀ x, x ∈ a → x.2 = true

@[simp]
theorem is_true_nil : is_true ([] : List (α × Bool)) := by
  simp [is_true]

theorem is_true_of_append (h : is_true (a ++ b)) : is_true a ∧ is_true b := by
  constructor
  · exact fun x hx => h x (List.mem_append_left b hx)
  exact fun x hx => h x (List.mem_append_right a hx)

theorem is_true_append (h1 : is_true a) (h2 : is_true b) : is_true (a ++ b) := by
  intro x h
  simp at h
  cases h with
  | inl h => exact h1 x h
  | inr h => exact h2 x h

theorem is_true_of_cons (h : is_true (a :: b)) : is_true [a] ∧ is_true b := by
  change is_true ([a]++b) at h
  exact is_true_of_append h

theorem is_true_cons (a : List (α × Bool)) (h : is_true a): is_true ((b, true) :: a) := by
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h2
  · simp [h1]
  exact h _ h2

theorem is_true_tail (h : is_true (x :: xs)) : is_true xs := by
  change is_true ([x] ++ xs) at h
  exact (is_true_of_append h).2

theorem eq_of_is_true_append_false_append_eq (ha : is_true a) (hb : is_true b)
    (h : a ++ [(c, false)] ++ d = b ++ [(e, false)] ++ f) : a = b ∧ c = e ∧ d = f := by
  have hab : a = b := by
    have h' := h
    rw [List.append_assoc, List.append_assoc] at h'
    rcases List.append_eq_append_iff.mp h' with ⟨k, hk1, hk2⟩ | ⟨k, hk1, hk2⟩
    · cases k with
      | nil => rw [List.append_nil] at hk1; exact hk1.symm
      | cons head tail =>
        rw [hk1] at hb
        have hh : head.2 = true := hb head (List.mem_append_right a List.mem_cons_self)
        simp only [List.cons_append, List.cons.injEq] at hk2
        simp [← hk2.1] at hh
    cases k with
    | nil => rw [List.append_nil] at hk1; exact hk1
    | cons head tail =>
      rw [hk1] at ha
      have hh : head.2 = true := ha head (List.mem_append_right b List.mem_cons_self)
      simp only [List.cons_append, List.cons.injEq] at hk2
      simp [← hk2.1] at hh
  refine ⟨hab, ?_⟩
  rw [hab, List.append_assoc, List.append_assoc, List.append_cancel_left_eq] at h
  simp at h
  exact h

theorem eq_of_is_false_append_true_append_eq (ha : is_false a) (hb : is_false b)
    (h : a ++ [(c, true)] ++ d = b ++ [(e, true)] ++ f) : a = b ∧ c = e ∧ d = f := by
  have hab : a = b := by
    have h' := h
    rw [List.append_assoc, List.append_assoc] at h'
    rcases List.append_eq_append_iff.mp h' with ⟨k, hk1, hk2⟩ | ⟨k, hk1, hk2⟩
    · cases k with
      | nil => rw [List.append_nil] at hk1; exact hk1.symm
      | cons head tail =>
        rw [hk1] at hb
        have hh : head.2 = false := hb head (List.mem_append_right a List.mem_cons_self)
        simp only [List.cons_append, List.cons.injEq] at hk2
        simp [← hk2.1] at hh
    cases k with
    | nil => rw [List.append_nil] at hk1; exact hk1
    | cons head tail =>
      rw [hk1] at ha
      have hh : head.2 = false := ha head (List.mem_append_right b List.mem_cons_self)
      simp only [List.cons_append, List.cons.injEq] at hk2
      simp [← hk2.1] at hh
  refine ⟨hab, ?_⟩
  rw [hab, List.append_assoc, List.append_assoc, List.append_cancel_left_eq] at h
  simp at h
  exact h

def to_SignedOptionList (L : List (ℕ × Bool)) : List (Option ℕ × Bool) := (List.map (fun x ↦ (some x.1, x.2)) L)

theorem is_false_to_SignedOptionList (ha : is_false a) : is_false (to_SignedOptionList a) := by
  unfold to_SignedOptionList
  unfold is_false
  intro x hx
  simp at hx
  rcases hx with ⟨a1, h1 | h2⟩
  · rw [← h1.2]
  specialize ha (a1, true) h2.1
  simp at ha

theorem is_true_to_SignedOptionList (ha : is_true a) : is_true (to_SignedOptionList a) := by
  unfold to_SignedOptionList
  intro x hx
  simp only [List.mem_map, Prod.exists, Bool.exists_bool] at hx
  rcases hx with ⟨a1, spec1 | spec2⟩
  · simp [(ha _ spec1.1), ← spec1.2]
  rw [← spec2.2]

theorem to_SignedOptionList_length : (to_SignedOptionList a).length = a.length := by
  unfold to_SignedOptionList
  simp only [List.length_map]

end SignedList
