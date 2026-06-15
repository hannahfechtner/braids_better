import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.GroupTheory.FreeGroup.Basic

namespace Monoid
def alternate [Monoid G] (a b : G) (n : ℕ) : G := match n with
  | 0 => 1
  | n' + 1 => a * alternate b a n'

@[simp]
theorem alternate_zero  [Monoid G] (a b : G) : alternate a b 0 = 1 := rfl

@[simp]
theorem alternate_one [Monoid G] (a b : G) : alternate a b 1 = a := by
  unfold alternate; simp

@[simp]
theorem alternate_two [Monoid G] (a b : G) : alternate a b 2 = a * b := by
  unfold alternate; simp

@[simp]
theorem alternate_three [Monoid G] (a b : G) : alternate a b 3 = a * b * a := by
  unfold alternate; simp; rw [mul_assoc]

theorem alternate_succ [Monoid G] (a b : G) : alternate a b (n + 1) = a * alternate b a n := rfl

theorem alternate_succ' [Monoid G] {a b : G} : alternate a b (n + 1) =
    (if Even n then alternate a b n * a else alternate a b n * b) := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    rw [alternate_succ, ih]
    split
    · next hn =>
      grind [alternate_succ]
    next hn =>
    have : Even (n + 1) := by aesop
    grind [alternate_succ]

theorem lift_monoid_alternate [Monoid H] {f : G → H} {x y : FreeMonoid G} {n : ℕ} :
    FreeMonoid.lift f (Monoid.alternate x y n) =
    Monoid.alternate (FreeMonoid.lift f x) (FreeMonoid.lift f y) n := by
  induction n generalizing x y with
  | zero =>
      simp
  | succ n ih =>
      grind [Monoid.alternate_succ]

theorem lift_group_alternate [Group H] {f : G → H} {x y : FreeGroup G} {n : ℕ} :
    FreeGroup.lift f (Monoid.alternate x y n) =
    Monoid.alternate (FreeGroup.lift f x) (FreeGroup.lift f y) n := by
  induction n generalizing x y with
  | zero =>
      simp
  | succ n ih =>
      grind [Monoid.alternate_succ]


end Monoid

#min_imports

