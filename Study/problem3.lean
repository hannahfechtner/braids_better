import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

open Finset

-- -- A sequence of natural numbers with finite support
-- def FinSuppSeq := { f : ℕ → ℕ // ∃ N, ∀ n, N < n → f n = 0 }

-- A finite sequence supported on {0, 1, ..., N}
structure FinSuppSeq (N : ℕ) where
  val : Fin (N+1) → ℕ

-- Support: indices where the value is nonzero
def FinSuppSeq.support {N : ℕ} (f : FinSuppSeq N) : Finset (Fin (N+1)) :=
  univ.filter (λ i => f.val i ≠ 0)

def FinSuppSeq.isDelightful {N : ℕ} (f : FinSuppSeq N) : Prop :=
  ∀ i : Fin (N+1), 1 ≤ (i : ℕ) →
    f.val i = ((f.support.image (↑)).filter (λ j => j ≠ 0 ∧ j % (i : ℕ) = 0)).card

-- (1, 0)
def delightful0 : FinSuppSeq 1 :=
  ⟨fun
    | 0 => 1
    | 1 => 0,
   ⟩

-- (2, 1, 0)
def delightful1 : FinSuppSeq 2 :=
  ⟨fun
    | 0 => 2
    | 1 => 1
    | 2 => 0,
   ⟩

-- (2, 2, 0)
def delightful2 : FinSuppSeq 2 :=
  ⟨fun
    | 0 => 2
    | 1 => 2
    | 2 => 0,
   ⟩

example : delightful0.isDelightful := by
  intro i hi
  cases i <;> simp [FinSuppSeq.support, delightful0]
  split
  · simp_all
  simp_all
  exact rfl

example : delightful1.isDelightful := by
  intro i hi
  cases i <;> simp [FinSuppSeq.support, delightful1]
  split
  · simp_all
  · simp_all
    exact rfl
  simp_all
  symm
  rw [Finset.card_eq_zero]
  apply?


  sorry

example : delightful2.isDelightful := by
  intro i hi
  cases i <;> simp [FinSuppSeq.support, delightful2]
  split
  · simp_all
  · simp_all
    sorry
  simp_all
  sorry
