import BraidProject.Additions.FreeMonoid
import BraidProject.DataCarrying.List

def FreeMonoid.prodEqOfCases {α} (a b : FreeMonoid α) {i : α} (h : a * b = .of i) :
    (a = 1 ∧ b = .of i) ⊕' (a = .of i ∧ b = 1) := by
  cases a with
  | h0 => exact .inl ⟨rfl, by rwa [one_mul] at h⟩
  | ih x rest =>
    rw [mul_assoc] at h
    have h' : .of x * (rest * b) = .of i * 1 := by rw [mul_one]; exact h
    have hp := FreeMonoid.first_generator_eq h'
    have hrb := FreeMonoid.prod_eq_one hp.2
    exact .inr ⟨by rw [hp.1, hrb.1, mul_one], hrb.2⟩

def FreeMonoid.prodEqProdCases {α} (a b c d : FreeMonoid α) (h : a * b = c * d) :
    (Σ m, PLift (c = a * m ∧ b = m * d)) ⊕ (Σ m, PLift (a = c * m ∧ d = m * b)) :=
  List.appendEqAppendCases h
