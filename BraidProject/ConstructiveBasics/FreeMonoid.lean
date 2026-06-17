import BraidProject.Additions.FreeMonoid
import BraidProject.ConstructiveBasics.List

def FreeMonoid.prod_eq_of_sum {α} (a b : FreeMonoid α) {i : α} (h : a * b = .of i) :
    (a = 1 ∧ b = .of i) ⊕' (a = .of i ∧ b = 1) := by
  cases a with
  | h0 => exact .inl ⟨rfl, by rwa [one_mul] at h⟩
  | ih x rest =>
    rw [mul_assoc] at h
    have h' : .of x * (rest * b) = .of i * 1 := by rw [mul_one]; exact h
    have hp := FreeMonoid.parts_eq h'
    have hrb := FreeMonoid.prod_eq_one hp.2
    exact .inr ⟨by rw [hp.1, hrb.1, mul_one], hrb.2⟩

def FreeMonoid.prod_eq_prod_sum {α} (a b c d : FreeMonoid α) (h : a * b = c * d) :
    (Σ m, PLift (c = a * m ∧ b = m * d)) ⊕ (Σ m, PLift (a = c * m ∧ d = m * b)) :=
  List.append_eq_append_sum h

-- /-- An induction principle on free monoids, with cases for `1`, `FreeMonoid.of` and `*`. -/
-- def FreeMonoid.inductionOn'' {C : FreeMonoid α → Type} (z : FreeMonoid α) (one : C 1)
--     (of : ∀ (x : α), C (FreeMonoid.of x)) (mul : ∀ (x y : FreeMonoid α), C x → C y → C (x * y)) :
--   C z := List.rec one (fun _ _ ih => mul [_] _ (of _) ih) z

-- /-- An induction principle for free monoids which mirrors induction on lists, with cases analogous
-- to the empty list and cons -/
-- @[to_additive (attr := elab_as_elim) self /--An induction principle for free monoids which mirrors
-- induction on lists, with cases analogous to the empty list and cons-/]
-- def FreeMonoid.inductionOn''' {p : FreeMonoid α → Type} (a : FreeMonoid α)
--     (one : p (1 : FreeMonoid α)) (mul_of : ∀ b a, p a → p (of b * a)) : p a :=
--   List.rec one (fun _ _ tail_ih => mul_of _ _ tail_ih) a
