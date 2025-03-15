/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/

import Mathlib.Data.List.Lex
import Mathlib.Tactic.Linarith

/-!
# Shortlex ordering of lists.

Given a relation `r` on `α`, the shortlex order on `List α` is defined by `L < M` iff
* `L.length < M.length`
* `L.length = M.length` and `L < M` under the lexicographic ordering over `r` on lists

## Main results

We show that if `r` is well-founded, so too is the shortlex order over `r`

## See also

Related files are:
* `Mathlib/Data/List/Lex`: Lexicographic order on `List α`.
* `Mathlib/Data/DFinsupp/WellFounded`: Well-foundedness of lexicographic orders on `DFinsupp` and
  `Pi`.
-/

/-! ### shortlex ordering -/

--to add to another file
theorem InvImage.trichotomous {α β : Type*} {r : α → α → Prop} [IsTrichotomous α r] {f : β → α}
    (h : Function.Injective f) : ∀ a b, (InvImage r f) a b ∨ a = b ∨ (InvImage r f) b a := by
  intro a b
  rw [← Function.Injective.eq_iff h]
  exact IsTrichotomous.trichotomous (f a) (f b)

instance InvImage.isAsymm {α β : Type*} {r : α → α → Prop} [IsAsymm α r] (f : β → α) :
    IsAsymm β (InvImage r f) where
  asymm := fun a b h h2 => IsAsymm.asymm (f a) (f b) h h2

/-- Given a relation `r` on `α`, the shortlex order on `List α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `n < k` or `n = k` and `[a0, ..., an] < [b0, ..., bk]`
under the lexicographic order induced by `r`. -/
def Shortlex {α : Type*} (r : α → α → Prop) : List α → List α → Prop :=
  InvImage (Prod.Lex (· < ·) (List.Lex r)) fun a ↦ (a.length, a)

namespace Shortlex

variable {α : Type*} {r : α → α → Prop}

/-- If a list `s` is shorter than a list `t`, then `s` is smaller than `t` under any shortlex
order. -/
theorem of_length_lt {s t : List α} (h : s.length < t.length) : Shortlex r s t :=
  Prod.Lex.left _ _ h

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r`  when `s` is smaller than `t` under the lexicographic order over `r` -/
theorem of_lex {s t : List α} (h : s.length = t.length) (h2 : List.Lex r s t) :
    Shortlex r s t := by
  apply Prod.lex_def.mpr
  right
  exact ⟨h, h2⟩

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r` exactly when `s` is smaller than `t` under the lexicographic order over `r`.-/
theorem _root_.List.shortlex_iff_lex {s t : List α} (h : s.length = t.length) :
    Shortlex r s t ↔ List.Lex r s t := by
  constructor
  · intro h2
    rw [Shortlex, InvImage, Prod.lex_def, h, lt_self_iff_false, false_or] at h2
    simp only [true_and] at h2
    exact h2
  exact fun h1 => of_lex h h1

theorem _root_.List.shortlex_def {s t : List α} : Shortlex r s t ↔
    s.length < t.length ∨ s.length = t.length ∧ List.Lex r s t := by
  constructor
  · intro hs
    unfold Shortlex InvImage at hs
    simp only at hs
    generalize hp : (s.length, s) = p at hs
    generalize hq : (t.length, t) = q at hs
    cases hs with
    | left b₁ b₂ h =>
      left
      rw [Prod.mk.injEq] at hp hq
      rw [← hp.1, ← hq.1] at h
      exact h
    | right a h =>
      right
      rw [Prod.mk.injEq] at hp hq
      rw [← hp.2, ← hq.2] at h
      exact ⟨hp.1.trans hq.1.symm, h⟩
  intro hpq
  rcases hpq with h1 | h2
  · exact of_length_lt h1
  exact of_lex h2.1 h2.2

open List
theorem cons_iff [IsIrrefl α r] {a : α} {s t : List α} : Shortlex r (a :: s) (a :: t) ↔
    Shortlex r s t := by
  simp only [shortlex_def, length_cons, add_lt_add_iff_right, add_left_inj, List.Lex.cons_iff]

@[simp]
theorem not_nil_right {s : List α} : ¬ Shortlex r s [] := by
  rw [shortlex_def]
  rintro (h1 | h2)
  · simp only [List.length_nil, not_lt_zero'] at h1
  · exact List.not_lex_nil h2.2

theorem nil_left_or_eq_nil (s : List α) : Shortlex r [] s ∨ s = [] := by
  cases s with
  | nil => right; rfl
  | cons head tail => exact Or.inl (of_length_lt (Nat.succ_pos tail.length))

@[simp]
theorem singleton_iff (a b : α) : Shortlex r [a] [b] ↔ r a b := by
  simp only [shortlex_def, length_singleton, lt_self_iff_false, Lex.singleton_iff, true_and,
    false_or]

instance isTrichotomous [IsTrichotomous α r] : IsTrichotomous (List α) (Shortlex r) where
  trichotomous := fun a b => InvImage.trichotomous (by simp [Function.Injective]) _ _

theorem append_right {s₁ s₂ : List α} (t : List α) : Shortlex r s₁ s₂ →
    Shortlex r s₁ (s₂ ++ t) := by
  intro h
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]
    omega
  cases t with
  | nil =>
    rw [List.append_nil]
    exact h
  | cons head tail =>
    apply of_length_lt
    rw [List.length_append, List.length_cons]
    omega

theorem List.Lex.ne [IsIrrefl α r] (h : a = b) : ¬ List.Lex r a b := by
  intro h
  induction h with
  | nil => simp at h
  | cons h1 ih =>
    simp at h
    exact ih h
  | rel hr =>
    simp at h
    rw [h.1] at hr
    rename_i hi _ _ _ _
    exact @IsIrrefl.irrefl _ _ hi _ hr

theorem List.lex_append_right_iff {s₁ s₂ : List α} (t : List α) [IsIrrefl α r] (h : s₁.length = s₂.length) :
    List.Lex r s₁ s₂ ↔ List.Lex r (s₁ ++ t) (s₂ ++ t) := by
  constructor
  · intro h
    induction h with
    | nil => simp at h
    | cons h ih =>
      apply Lex.cons
      simp at h
      specialize ih h
      exact ih
    | rel h =>
      apply Lex.rel (by assumption)
  intro h
  generalize h1 : s₁ ++ t = s1'
  generalize h2 : s₂ ++ t = s2'
  rw [h1, h2] at h
  induction h generalizing s₁ s₂ with
  | nil =>
    simp at h1
    rw [h1.1]
    rw [h1.2] at h2
    simp at h2
    rw [h2, h1.1] at h
    simp at h
  | cons h4 ih =>
    cases s₁ with
    | nil =>
      cases s₂ with
      | cons head tail => simp at h
      | nil =>
        simp at h1
        simp at h2
        have h3 := h1.symm.trans h2
        simp at h3
        rw [h3] at h4
        exfalso
        rename_i hi _ _ _
        apply List.Lex.ne rfl h4
    | cons head tail =>
      cases s₂ with
      | nil => simp at h
      | cons head1 tail1 =>
        simp at h2
        simp at h1
        simp at h
        specialize ih h h1.2 h2.2
        rw [h2.1, h1.1]
        exact Lex.cons ih
  | rel hr =>
    cases s₁ with
    | nil =>
      cases s₂ with
      | nil =>
        simp at h1
        simp at h2
        have h3 := h1.symm.trans h2
        simp at h3
        rw [h3.1] at hr
        exfalso
        rename_i hi _ _ _ _
        apply @IsIrrefl.irrefl _ _ hi _ hr
      | cons head tail => simp at h
    | cons head tail =>
      cases s₂ with
      | nil => simp at h
      | cons head tail =>
        simp at h1
        simp at h2
        rw [h1.1, h2.1]
        exact Lex.rel hr

theorem append_right_iff {s₁ s₂ : List α} (t : List α) [IsIrrefl α r] : Shortlex r s₁ s₂ ↔
    Shortlex r (s₁ ++ t) (s₂ ++ t) := by
  constructor
  · intro h
    rcases shortlex_def.mp h with h1 | h2
    · apply of_length_lt
      rw [List.length_append, List.length_append]
      omega
    apply of_lex
    · simp [h2.1]
    exact (List.lex_append_right_iff _ h2.1).mp h2.2
  intro h
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append, List.length_append] at h1
    omega
  apply of_lex
  · simp at h2
    simp [h2.1]
  simp at h2
  exact (List.lex_append_right_iff _ h2.1).mpr h2.2

theorem append_left {t₁ t₂ : List α} (h : Shortlex r t₁ t₂) (s : List α) :
    Shortlex r (s ++ t₁) (s ++ t₂) := by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append, List.length_append]
    omega
  cases s with
  | nil =>
    rw [List.nil_append, List.nil_append]
    exact h
  | cons head tail =>
    apply of_lex
    · simp only [List.cons_append, List.length_cons, List.length_append, Nat.succ_eq_add_one,
      add_left_inj, add_right_inj]
      exact h2.1
    exact List.Lex.append_left r h2.2 (head :: tail)


theorem List.Lex.append_left_iff [IsIrrefl α r] : List.Lex r (s ++ t₁) (s ++ t₂) ↔ List.Lex r t₁ t₂ := by
  constructor
  · intro h
    induction s with
    | nil =>
      simp only [List.nil_append] at h
      exact h
    | cons head tail ih =>
      simp only [List.cons_append, List.Lex.cons_iff] at h
      exact ih h
  intro h
  apply List.Lex.append_left r h

theorem append_left_iff [IsIrrefl α r] {t₁ t₂ : List α} (s : List α) : Shortlex r t₁ t₂ ↔
    Shortlex r (s ++ t₁) (s ++ t₂) := by
  constructor
  · exact fun h => append_left h _
  intro h
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    simp at h1
    omega
  simp at h2
  apply of_lex h2.1
  apply List.Lex.append_left_iff.mp h2.2
section WellFounded

variable {h : WellFounded r}

theorem _root_.Acc.shortlex {a : α} (n : ℕ) (aca : Acc r a)
    (acb : (b : List α) → b.length < n → Acc (Shortlex r) b) (b : List α) (hb : b.length < n)
    (ih : ∀ s : List α, s.length < (a::b).length → Acc (Shortlex r) s) :
    Acc (Shortlex r) ([a] ++ b) := by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction (acb b hb) with
    | intro xb _ ihb =>
      apply Acc.intro ([xa] ++ xb)
      intro p lt
      rcases shortlex_def.mp lt with h1 | h2
      · exact ih _ h1
      · cases p with
        | nil => simp only [List.length_nil, List.singleton_append, List.length_cons,
          Nat.succ_eq_add_one, self_eq_add_left, add_eq_zero, List.length_eq_zero, one_ne_zero,
          and_false, false_and] at h2
        | cons headp tailp =>
          cases h2.2 with
          | cons h =>
            rw [List.append_eq, List.nil_append] at h
            simp only [List.length_cons, Nat.succ_eq_add_one, List.singleton_append,
              add_left_inj] at h2
            rw [← h2.1] at hb
            apply ihb _ (of_lex (h2.1) h) hb
            intro l hl
            apply ih
            rw [List.length_cons, ← h2.1]
            exact hl
          | rel h =>
            simp only [List.length_cons, Nat.succ_eq_add_one, List.singleton_append,
              add_left_inj] at h2
            rw [← h2.1] at hb
            apply iha headp h _ hb
            intro l hl
            apply ih
            rw [List.length_cons, ← h2.1]
            exact hl

theorem wf (h : WellFounded r) : WellFounded (Shortlex r) := by
  suffices h : ∀ n, ∀ (a : List α), a.length = n → Acc (Shortlex r) a from
    WellFounded.intro (fun a => h a.length a rfl)
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro a len_a
      rw [List.length_eq_zero] at len_a
      rw [len_a]
      exact Acc.intro _ <| fun _ ylt => (Shortlex.not_nil_right ylt).elim
    | succ n =>
      intro a len_a
      rcases List.exists_of_length_succ a len_a with ⟨head, tail, a_is⟩
      rw [a_is]
      rw [a_is, List.length_cons, add_left_inj] at len_a
      apply Acc.shortlex (n+1) (WellFounded.apply h head) (fun b bl => ih b.length bl _ rfl)
      · rw [len_a]
        exact lt_add_one n
      intro l ll
      apply ih l.length _ _ rfl
      rw [← len_a]
      exact ll

end WellFounded

end Shortlex
