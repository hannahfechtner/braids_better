import Mathlib.Data.List.Basic

noncomputable def ListC.append_eq_append {a b c d : List α} (h : a ++ b = c ++ d) :
    (Σ to_middle, PLift (a = c ++ to_middle ∧ d = to_middle ++ b)) ⊕
    (Σ from_middle, PLift (a ++ from_middle = c ∧ b = from_middle ++ d)) := by
  induction a generalizing b c d
  · simp only [List.nil_append] at h
    match c with
    | [] =>
      exact Sum.inl ⟨[], by simp [h]; exact ⟨trivial⟩⟩
    | c1 :: cr =>
      exact Sum.inr ⟨(c1 :: cr), by simp [h]; exact ⟨trivial⟩⟩
  rename_i a1 ar ih
  match c with
  | [] =>
    exact Sum.inl ⟨(a1 :: ar), by simp [h]; exact ⟨trivial⟩⟩
  | c1 :: cr =>
    simp only [List.cons_append, List.cons.injEq] at h
    rw [← h.1]
    simp only [List.cons.injEq, true_and, List.cons_append]
    exact ih h.2


namespace List

def PrefixData {α : Type} (l₁ l₂ : List α) : Type :=
  Σ sx, PLift (l₁ ++ sx = l₂)

def SuffixData {α : Type} (l₁ l₂ : List α) : Type :=
  Σ pr, PLift (pr ++ l₁ = l₂)

@[simp]
def PrefixData.nil : PrefixData [] u := by
  use u
  exact ⟨by simp⟩

@[simp]
def SuffixData.nil : SuffixData [] u := by
  use u
  exact ⟨by simp⟩

@[simp]
def PrefixData.refl {u : List α} : PrefixData u u := by
  use []
  exact ⟨by simp⟩

@[simp]
def SuffixData.refl {u : List α} : SuffixData u u := by
  use []
  exact ⟨by simp⟩

def PrefixData.cons (a) : PrefixData l₁ l₂ → PrefixData (a :: l₁) (a :: l₂) := by
  rintro ⟨rest, ⟨h⟩⟩
  use rest
  exact ⟨by simp [h]⟩

def PrefixData.append_self : PrefixData a (a ++ b) := by
  use b
  exact ⟨by simp⟩

def SuffixData.append_self : SuffixData b (a ++ b) := by
  use a
  exact ⟨by simp⟩

def SuffixData.append_right (h : SuffixData b c) : SuffixData (b ++ a) (c ++ a) := by
  rcases h with ⟨t, ⟨ht⟩⟩
  use t
  constructor
  simp [← ht]

def PrefixData.append_left :
    (PrefixData l₁ l₂ → PrefixData (l ++ l₁) (l ++ l₂)) := by
  rintro ⟨w, ⟨h⟩⟩
  use w
  exact ⟨by simp [← List.append_assoc, ← h]⟩

def PrefixData.of_append_left : PrefixData (l ++ l₁) (l ++ l₂) → PrefixData l₁ l₂ := by
  induction l with
  | nil => simp only [nil_append]; exact id
  | cons head tail ih =>
    rintro ⟨w, ⟨hwt⟩⟩
    apply ih
    use w
    constructor
    grind

def InfixData {α : Type} (l₁ l₂ : List α) : Type :=
  Σ pr sx, PLift (pr ++ l₁ ++ sx = l₂)

def InfixData.refl (a : List α) : InfixData a a := by
  use [], []
  exact ⟨by simp⟩

@[simp]
def InfixData.nil (l : List α) : InfixData [] l := by
  use l, []
  simp
  exact ⟨by trivial⟩

def InfixData.tail_of_cons_ne (h : InfixData (a :: b)  (c :: d)) (ne : a ≠ c) : InfixData (a :: b) d := by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp only [nil_append, cons_append, cons.injEq] at hwt
    exact (ne hwt.1.1).elim
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    use tail, t
    exact ⟨hwt.1.2⟩

def InfixData.tail_of_cons_cons_ne (h : InfixData [a, b] (c1 :: c2 :: d)) (ne : b ≠ c2) : InfixData [a, b] (c2 :: d) := by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at hwt
    exact (ne hwt.1.2.1).elim
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    use tail, t
    exact ⟨hwt.1.2⟩

def InfixData.cons_cons_cases (h : InfixData [a, b] (c :: d :: e)) :
    (PLift (a = c ∧ b =d)) ⊕ InfixData [a, b] (d :: e):= by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at hwt
    left
    exact ⟨hwt.1.1, hwt.1.2.1⟩
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    right
    use tail, t
    exact ⟨hwt.1.2⟩

def InfixData.append_right (h : InfixData  l1 l2) : InfixData l1 (l2 ++ l3) := by
  rcases h with ⟨w, t, hwt⟩
  use w, t ++ l3
  rw [← hwt.1]
  exact {down := by simp}

def InfixData.append_left (h : InfixData l1 l2) : InfixData l1 (l3 ++ l2) := by
  rcases h with ⟨w, t, hwt⟩
  use l3 ++ w, t
  rw [← hwt.1]
  exact {down := by simp}

theorem InfixData.length_le (h : InfixData l1 l2) : l1.length ≤ l2.length := by
  rcases h with ⟨w, t, ⟨hwt⟩⟩
  apply congr_arg List.length at hwt
  simp only [List.append_assoc, List.length_append] at hwt
  omega

theorem InfixData.of_nil (h : InfixData L []) : L = [] := by
  apply InfixData.length_le at h
  simp only [List.length_nil, Nat.le_zero_eq, List.length_eq_zero_iff] at h
  exact h

@[simp]
theorem InfixData.not_nil_of_length_pos (h : InfixData l1 []) (h2 : l1.length > 0) : False := by
  apply InfixData.length_le at h
  simp only [length_nil, Nat.le_zero_eq, length_eq_zero_iff] at h
  rw [h] at h2
  simp at h2

def InfixData.cons {l1 l2 : List α} (h : InfixData l1 l2) : InfixData l1 (a :: l2) := by
  rcases h with ⟨w, t, ⟨hwt⟩⟩
  rw [← hwt]
  use a ::w, t
  exact {down := by simp [hwt]}

@[simp]
def InfixData.length_two_not_infix_nil : InfixData [a, b] [] → Empty := by
  intro h
  apply InfixData.not_nil_of_length_pos at h
  simp at h

def InfixData.trans (h1 : InfixData a b) (h2 : InfixData b c) : InfixData a c := by
  rcases h1 with ⟨w, t, ⟨hwt⟩⟩
  rcases h2 with ⟨w2, t2, ⟨hwt2⟩⟩
  use w2 ++ w, t ++ t2
  rw [← hwt2, ← hwt]
  exact {down := by simp}


def distinct_pair_infix_eq (b_ne : b1 ≠ b2) (h : a ++ [b1, b2] ++ c = d ++ [b1, b2] ++ e) :
  PLift (a = d ∧ c = e) ⊕ (Σ a1 a2, PLift (a = a1 ++ [b1, b2] ++ a2 ∧ d = a1 ∧ e = a2 ++ [b1, b2] ++ c)) ⊕
  (Σ c1 c2, PLift (c = c1 ++ [b1, b2] ++ c2 ∧ d = a ++ [b1, b2] ++ c1 ∧ e = c2)) := by
  induction a generalizing b1 b2 c d e
  · simp only [nil_append, cons_append, append_assoc] at h
    simp only [nil_eq, append_assoc, cons_append, nil_append, append_eq_nil_iff, reduceCtorEq,
      and_false, false_and]
    match d with
    | [] =>
      left
      simp only [nil_append, cons.injEq, true_and] at h
      exact ⟨rfl, h⟩
    | d1 :: [] =>
      simp only [cons_append, nil_append, cons.injEq] at h
      left
      rw [h.2.1] at b_ne
      constructor
      simp at b_ne
    | d1 :: d2 :: dr =>
      simp only [cons_append, cons.injEq] at h
      right; right
      use dr, e
      constructor
      simp only [h, and_self]
  rename_i a1 ar ih
  match d with
  | [] =>
    match ar with
    | [] => simp [b_ne] at h
    | a2 :: arr =>
      simp only [cons_append, append_assoc, nil_append, cons.injEq] at h
      right; left
      use [], arr
      constructor
      simp [h]
  | d1 :: [] =>
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq] at h
    match ar with
    | [] => left; constructor; grind
    | a2 :: a3 :: arr =>
      right; left
      use [d1], arr
      constructor
      grind
    | a2 :: [] =>
      simp only [cons_append, nil_append, cons.injEq] at h
      exfalso
      apply b_ne
      exact (h.2.2.1)
  | d1 :: d2 :: dr =>
    simp only [cons_append, append_assoc, nil_append, cons.injEq] at h
    have H1 : ar ++ b1 :: b2 :: c  = ar ++ [b1, b2] ++ c := by simp
    have H : d2 :: (dr ++ b1 :: b2 :: e) = (d2 :: dr) ++ [b1, b2] ++ e := by simp
    rw [H1, H] at h
    specialize ih b_ne h.2
    rcases ih with h1 | h2 | h3
    · left
      simp only [cons.injEq]
      constructor; exact ⟨⟨h.1, h1.1.1⟩, h1.1.2⟩
    · rcases h2 with ⟨a1', a2', spec⟩
      right; left
      use d1 :: a1', a2'
      rw [spec.1.1, spec.1.2.1, spec.1.2.2, h.1]
      constructor; simp
    rcases h3 with ⟨c1', c2', spec⟩
    right; right
    use c1', c2'
    rw [spec.1.1, spec.1.2.1, spec.1.2.2, h.1]
    constructor; simp
end List
