import Mathlib.Algebra.Order.Ring.Nat

def lt' : (Option ℕ × Bool) → Option ℕ × Bool →  Prop
  | (_, true), (_, false) => true
  | (none, true), (some _, true) => true
  | (some i, true), (some j, true) => i < j
  | (some i, false), (some j, false) => i < j
  | (some _, false), (none, false) => true
  | (_, _), (_, _) => false

theorem lt_acc_none : Acc lt' (none, true) := by
  apply Acc.intro
  intro y hy
  exfalso
  simp [lt'] at hy

theorem some_zero_true : Acc lt' (some 0, true) := by
  apply Acc.intro
  intro y hy
  cases y with
  | mk fst snd =>
    cases fst with
    | none =>
      cases snd with
      | false =>
        simp [lt'] at hy
      | true =>
        exact lt_acc_none
    | some val =>
      induction val with
      | zero =>
        cases snd with
        | false => simp [lt'] at hy
        | true => simp [lt'] at hy
      | succ n ih =>
        cases snd with
        | false => simp [lt'] at hy
        | true => simp [lt'] at hy

theorem lt_acc_some_true : Acc lt' (some val, true) := by
  induction val with
  | zero => exact some_zero_true
  | succ n ih =>
    apply Acc.intro
    intro y y_lt
    have H : y = (some n, true) ∨ lt' y (some n, true) := by
      cases y with
      | mk fst snd =>
        cases fst with
        | none =>
          cases snd with
          | false =>
            simp [lt'] at y_lt
          | true =>
            exact Or.inr y_lt
        | some val =>
          cases val with
          | zero =>
            cases snd with
            | false =>
              simp [lt'] at y_lt
            | true =>
              cases n with
              | zero => left; rfl
              | succ n => right; simp [lt']
          | succ m =>
            cases snd with
            | false =>
              simp [lt'] at y_lt
            | true =>
              simp [lt'] at y_lt
              have H : n = m + 1 ∨ n > m + 1 := by omega
              cases H with
              | inl h =>
                rw [h]
                exact Or.inl rfl
              | inr h =>
                exact Or.inr h
    cases H with
    | inl h => rw [h] ; assumption
    | inr h => exact Acc.inv ih h

theorem lt_acc_some_false : Acc lt' (some val, false) := by
  induction val with
  | zero =>
    apply Acc.intro
    intro y hy
    cases y with
    | mk fst snd =>
      cases fst with
      | none =>
        cases snd with
        | false => simp [lt'] at hy
        | true => exact lt_acc_none
      | some val =>
        cases snd with
        | false => simp [lt'] at hy
        | true => exact lt_acc_some_true
  | succ n ih =>
    apply Acc.intro
    intro y y_lt
    have H : y = (some n, false) ∨ lt' y (some n, false) := by
      cases y with
      | mk fst snd =>
        cases fst with
        | none =>
          cases snd with
          | false =>
            simp [lt'] at y_lt
          | true =>
            exact Or.inr y_lt
        | some val =>
          cases val with
          | zero =>
            cases snd with
            | false =>
              cases n with
              | zero => left; rfl
              | succ n => right; simp [lt']
            | true =>
              right; simp [lt']
          | succ m =>
            cases snd with
            | false =>
              simp [lt'] at y_lt
              have H : m + 1 = n ∨ m + 1 < n := by omega
              cases H with
              | inl h =>
                rw [h]
                exact Or.inl rfl
              | inr h =>
                exact Or.inr h
            | true =>
              right; assumption
    cases H with
    | inl h => rw [h] ; assumption
    | inr h => exact Acc.inv ih h

theorem lt_acc_none_false : Acc lt' (none, false) := by
  apply Acc.intro
  intro y hy
  cases y with
  | mk fst snd =>
    cases fst with
    | none =>
      cases snd with
      | false =>
        simp [lt'] at hy
      | true =>
        exact lt_acc_none
    | some val =>
      cases val with
      | zero =>
        cases snd with
        | false =>
          exact lt_acc_some_false
        | true =>
          exact some_zero_true
      | succ n =>
        cases snd with
        | false =>
          exact lt_acc_some_false
        | true =>
          exact lt_acc_some_true

theorem lt_acc : ∀ (a : Option ℕ × Bool), Acc lt' a := by
  intro a
  cases a with
  | mk fst snd =>
    cases snd with
    | false =>
      cases fst with
      | none => exact lt_acc_none_false
      | some val => exact lt_acc_some_false
    | true =>
      cases fst with
      | none => exact lt_acc_none
      | some val => exact lt_acc_some_true

instance : WellFounded lt' := by
  refine WellFounded.intro ?h
  intro a
  exact lt_acc a
