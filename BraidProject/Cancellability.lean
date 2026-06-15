import BraidProject.Stability'
import BraidProject.CommonMultiples

open Braid BraidMonoidInf Grid DeterminativeSpine

namespace Braid

theorem Grid.of_mk_eq_mk (h : BraidMonoidInf.mk a = BraidMonoidInf.mk b) :
    grid a b 1 1 := by
  rcases (stability _ _ 1 1 (top_left_word a) _ _ rfl h) with ⟨a, b, hg, ha, hb⟩
  rw [BraidMonoidInf.one_of_eq_mk_one ha.symm, BraidMonoidInf.one_of_eq_mk_one hb.symm] at hg
  exact hg

theorem BraidMonoidInf.left_cancellative {a b c : BraidMonoidInf} (h1 : c * a = c * b) :
    a = b := by
  induction a with | h a'
  induction b with | h b'
  induction c with | h c'
  induction c' using FreeMonoid.inductionOn' with
  | one => exact h1
  | mul_of d e f =>
    apply f
    change BraidMonoidInf.mk _ = BraidMonoidInf.mk _ at h1
    simp only at h1
    rw [mul_assoc, mul_assoc] at h1
    have := Grid.of_mk_eq_mk h1
    rcases splittable_horizontally this _ _ rfl with ⟨middle, f₁, f₂, g₁, g₂, f_is⟩
    rw [(FreeMonoid.prod_eq_one f_is.symm).1] at g₁
    rcases splittable_vertically g₁ _ _ rfl with ⟨s₁, m₁, m₂, g₃, g₄, middle_is⟩
    have ⟨hm₁, hs₁⟩ := generator_generator_same g₃
    rw [hs₁] at g₄
    have ⟨hm₂, _⟩ := one_word g₄
    rw [hm₁, one_mul, hm₂] at middle_is
    rw [middle_is] at g₂
    have := braid_eq_of_grid g₂
    rw [mul_one, (FreeMonoid.prod_eq_one f_is.symm).2, mul_one, mk_mul, mk_mul] at this
    exact this

theorem BraidMonoidInf.right_cancellative {a b c : BraidMonoidInf} (h1 : a * c = b * c) : a = b := by
  apply BraidMonoidInf.reverse_eq_reverse_iff.mp at h1
  rw [BraidMonoidInf.reverse_braid_mul, BraidMonoidInf.reverse_braid_mul] at h1
  exact BraidMonoidInf.reverse_eq_reverse_iff.mpr (left_cancellative h1)

instance BraidMonoidInf_Cancellative : CancelMonoid BraidMonoidInf where
    mul_right_cancel := fun _ _ _ => right_cancellative
    mul_left_cancel := fun _ _ _ => left_cancellative

instance : IsLeftCancelMul BraidMonoidInf := ⟨fun _ _ _ => left_cancellative⟩

instance : IsRightCancelMul BraidMonoidInf := ⟨fun _ _ _ => right_cancellative⟩

theorem Grid.unicity (h1 : grid a b c d) : ∀ c' d', grid a b c' d' → c' = c ∧ d' = d := by
  induction h1 with
  | empty => exact fun _ _ h => one_one h
  | top_bottom i => exact fun _ _ h => one_generator h
  | sides i => exact fun _ _ h =>  generator_one h
  | top_left i => exact fun _ _ h => generator_generator_same h
  | adjacent i k h => exact fun _ _ hg => generator_generator_close hg h
  | separated i j h => exact fun _ _ hg => generator_generator_apart hg (by aesop)
  | vertical _ _ _ _ =>
    intro _ _ gr
    rcases splittable_horizontally gr _ _ rfl
    grind
  | horizontal _ _ _ _ =>
    intro _ _ gr
    rcases splittable_vertically gr _ _ rfl
    grind

theorem Grid.existence : ∀ a b, ∃ c d, grid a b c d := by
  intro a b
  rcases common_right_mul_inf_mk a b with ⟨c1, d1, h⟩
  have big_grid : grid (a * c1) (b * d1) 1 1 := by
    apply Grid.of_mk_eq_mk
    aesop
  rcases splittable_horizontally big_grid _ _ rfl with ⟨_, c₁, c₂, top_grid, _, side_one⟩
  rw [(FreeMonoid.prod_eq_one side_one.symm).1] at top_grid
  rcases splittable_vertically top_grid _ _ rfl with ⟨top_vert, m₁, m₂, top_left, _, _⟩
  use m₁, top_vert
