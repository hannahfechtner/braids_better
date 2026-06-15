import Mathlib.Algebra.Order.Ring.Nat

namespace SignedOptionNat

def lt : (Option ℕ × Bool) → Option ℕ × Bool →  Prop
  | (_, true), (_, false) => true
  | (none, true), (some _, true) => true
  | (some i, true), (some j, true) => i < j
  | (some i, false), (some j, false) => i < j
  | (some _, false), (none, false) => true
  | (_, _), (_, _) => false

instance : LT ((Option ℕ × Bool)) where
  lt := lt

instance (a b) : Decidable (lt a b) := by
  unfold lt
  simp only [Bool.false_eq_true]
  split
  all_goals exact inferInstance

theorem acc_none_true : Acc lt (none, true) := by
  apply Acc.intro
  intro y hy
  simp [lt] at hy

theorem acc_some_zero_true : Acc lt (some 0, true) := by
  apply Acc.intro
  intro y hy
  match y with
  | (none, true) => exact acc_none_true
  | (none, false) => simp [lt] at hy
  | (some i, true) => simp [lt] at hy
  | (some i, false) => simp [lt] at hy

theorem acc_some_true : Acc lt (some val, true) := by
  induction val with
  | zero => exact acc_some_zero_true
  | succ n ih =>
    apply Acc.intro
    intro y y_lt
    have : y = (some n, true) ∨ lt y (some n, true) := by
      match y with
      | (none, true) => right; simp [lt]
      | (none, false) => simp [lt] at y_lt
      | (some a, true) => grind [lt]
      | (some a, false) => simp [lt] at y_lt
    cases this with
    | inl h => rw [h] ; assumption
    | inr h => exact Acc.inv ih h

theorem acc_some_zero_false : Acc lt (some 0, false) := by
  apply Acc.intro
  intro y hy
  match y with
  | (none, true) => exact acc_none_true
  | (none, false) => simp [lt] at hy
  | (some i, true) => exact acc_some_true
  | (some i, false) => simp [lt] at hy

theorem acc_some_false : Acc lt (some val, false) := by
  induction val with
  | zero => exact acc_some_zero_false
  | succ n ih =>
    apply Acc.intro
    intro y y_lt
    have : y = (some n, false) ∨ lt y (some n, false) := by
      match y with
      | (none, true) => right; simp [lt]
      | (none, false) => simp [lt] at y_lt
      | (some a, true) => grind [lt]
      | (some a, false) => grind [lt]
    cases this with
    | inl h => rw [h] ; assumption
    | inr h => exact Acc.inv ih h

theorem acc_none_false : Acc lt (none, false) := by
  apply Acc.intro
  intro y hy
  match y with
  | (none, true) => exact acc_none_true
  | (none, false) => simp [lt] at hy
  | (some i, true) => exact acc_some_true
  | (some i, false) => exact acc_some_false

theorem acc (a : Option ℕ × Bool) : Acc lt a := by
  match a with
  | (none, true) => exact acc_none_true
  | (some val, true) => exact acc_some_true
  | (some val, false) => exact acc_some_false
  | (none, false) => exact acc_none_false

instance wellFounded_lt : WellFounded lt := WellFounded.intro fun a ↦ acc a

end SignedOptionNat
