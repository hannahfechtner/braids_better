import Mathlib.GroupTheory.FreeGroup.Basic
import BraidProject.Additions.SignedList

theorem FreeGroup.mk_cons {α : Type} (x : α × Bool) (l : List (α × Bool)) :
    FreeGroup.mk (x :: l) = FreeGroup.mk [x] * FreeGroup.mk l := by
  simp [FreeGroup.mul_mk]

theorem FreeGroup.exists_rep {α : Type} (g : FreeGroup α) : ∃ l : List (α × Bool), FreeGroup.mk l = g :=
  Quot.exists_rep g
  
namespace SignedList

theorem is_true_invRev_of_false (h : is_false a) : is_true (FreeGroup.invRev a) := by
  intro x hx
  simp only [FreeGroup.invRev, List.mem_reverse, List.mem_map, Prod.exists, Bool.exists_bool,
    Bool.not_false, Bool.not_true] at hx
  rcases hx with ⟨a1, ha1⟩
  cases ha1 with
  | inl h1 => aesop
  | inr h1 =>
    specialize h (a1, true) h1.1
    aesop

theorem is_false_invRev_of_true (h : is_true a) : is_false (FreeGroup.invRev a) := by
  intro x hx
  simp only [FreeGroup.invRev, List.mem_reverse, List.mem_map, Prod.exists, Bool.exists_bool,
    Bool.not_false, Bool.not_true] at hx
  rcases hx with ⟨a1, ha1⟩
  cases ha1 with
  | inl h1 =>
    specialize h (a1, false) h1.1
    aesop
  | inr h1 => aesop
