import Mathlib.Data.List.Lex
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Indexes
import Mathlib.Data.DFinsupp.Basic
import Mathlib.Data.DFinsupp.Lex
import Mathlib.Data.DFinsupp.WellFounded

def Shortlex {α : Type*} (r : α → α → Prop) : List α → List α → Prop :=
  fun a b => Prod.Lex (fun n1 n2 => n1 < n2) (fun a b => List.Lex r a b) (a.length, a) (b.length, b)

namespace Shortlex

theorem not_nil_nil (h : Shortlex r [] []) : False := by
  cases h with
  | left b₁ b₂ h => exact Nat.not_succ_le_zero 0 h
  | right a h => exact List.Lex.not_nil_right _ _ h

theorem not_nil_right (h : Shortlex r l []) : False := by
  unfold Shortlex at h
  generalize hl : (l.length, l) = l' at h
  cases h with
  | left b₁ b₂ h => simp only [List.length_nil, not_lt_zero'] at h
  | right a h => exact List.Lex.not_nil_right _ _ h

theorem acc_empty {α : Type*} (r : α → α → Prop) : Acc (Shortlex r) [] := by
  apply Acc.intro
  intro y ylt
  exact (Shortlex.not_nil_right ylt).elim

variable {α : Type*} (r : α → α → Prop) {h : WellFounded r}

theorem acc_singleton {α : Type*} (r : α → α → Prop) {h : WellFounded r} {i : α} : Acc (Shortlex r) [i] := by
  apply WellFounded.induction h i
  intro x ih
  apply Acc.intro
  intro y ylt
  unfold Shortlex at ylt
  generalize hy : (y.length, y) = z at ylt
  cases ylt with
  | left b₁ b₂ h =>
    simp only [List.length_singleton, Nat.lt_one_iff] at h
    rw [h] at hy
    simp only [Prod.mk.injEq, List.length_eq_zero] at hy
    rw [hy.1]
    apply acc_empty
  | right a h' =>
    simp only [List.length_singleton, Prod.mk.injEq] at hy
    rcases List.length_eq_one.mp hy.1 with ⟨j, hj⟩
    rw [hj]
    rw [← hy.2, hj, List.Lex.singleton_iff] at h'
    exact ih j h'


theorem shorter_than {m n : List α} (h : m.length < n.length) : Shortlex r m n := Prod.Lex.left m n h

theorem acc_lt (h : Acc (Shortlex r) l) (m : List α) (hl : m.length < l.length) :
    Acc (Shortlex r) m := by
  apply Acc.inv h
  exact shorter_than _ hl

theorem acc_length_one (m : List α) (hl : m.length =1) :
    Acc (Shortlex r) m := by
  rcases List.length_eq_one.mp hl with ⟨q, hq⟩
  rw [hq]
  apply acc_singleton
  exact h

theorem lexAccessible2 {a : α} (aca : Acc r a) (acb : (b : α) → Acc r b) (b : α) :
    Acc (Shortlex r) [a, b] := by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction (acb b) with
    | intro xb _ ihb =>
      apply Acc.intro [xa, xb]
      intro p lt
      unfold Shortlex at lt
      generalize hp : (p.length, p) = p' at lt
      cases lt with
      | left  _ _ h =>
        simp at hp
        simp at h
        cases h with
        | refl =>
          rcases List.length_eq_one.mp hp.1 with ⟨w, hw⟩
          rw [hw]
          apply acc_singleton
          exact h
        | step n =>
          simp only [Nat.succ_eq_add_one, zero_add, Nat.le_eq, add_le_iff_nonpos_left,
            nonpos_iff_eq_zero] at n
          rw [n, List.length_eq_zero] at hp
          rw [hp.1]
          exact acc_empty r
      | right _ h   =>
        simp at hp
        rw [← hp.2] at h
        rcases List.length_eq_two.mp hp.1 with ⟨p1, p2, h12⟩
        rw [h12] at h
        cases h with
        | cons h =>
          cases h with
          | cons h => simp only [List.Lex.not_nil_right] at h
          | rel h =>
            rw [h12]
            apply ihb
            exact h
        | rel h =>
          rw [h12]
          apply iha _ h

theorem acc_pair {α : Type*} (r : α → α → Prop) {h : WellFounded r} (i j : α) :
    Acc (Shortlex r) [i, j] := by
  apply lexAccessible2
  exact h
  exact WellFounded.apply h i
  exact fun j => WellFounded.apply h j

theorem lexAccessible' {a : α} (n : ℕ) (aca : Acc r a)
    (acb : (b : List α) → b.length < n → Acc (Shortlex r) b) (b : List α) (hb : b.length < n)
    (ih : ∀ l : List α, l.length < (a::b).length → Acc (Shortlex r) l) :
    Acc (Shortlex r) ([a] ++ b) := by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction (acb b hb) with
    | intro xb _ ihb =>
      apply Acc.intro ([xa] ++ xb)
      intro p lt
      unfold Shortlex at lt
      generalize hp : (p.length, p) = p' at lt
      cases lt with
      | left  _ _ h =>
        simp at hp
        simp at h
        apply ih
        simp
        rw [hp.1]
        exact h
      | right _ h   =>
        simp at hp
        rw [← hp.2] at h
        cases p with
        | nil => simp at hp
        | cons headp tailp =>
          cases h with
          | cons h =>
            simp at h
            apply ihb
            unfold Shortlex
            apply (Prod.lex_def _ _).mpr
            right
            constructor
            · simp at hp
              exact hp.1
            exact h
            · simp at hp
              rw [hp.1]
              exact hb
            intro l hl
            apply ih
            simp
            simp at hl
            simp at hp
            rw [← hp.1]
            exact hl
          | rel h =>
            apply iha
            exact h
            · simp at hp
              rw [hp.1]
              exact hb
            intro l hl
            apply ih
            simp
            simp at hl
            simp at hp
            rw [← hp.1]
            exact hl

theorem wf {α : Type*} (r : α → α → Prop) {h : WellFounded r} : WellFounded (Shortlex r) := by
  apply WellFounded.intro
  have H : ∀ n, ∀ (a : List α), a.length = n → Acc (Shortlex r) a := by
    intro n
    induction n using Nat.strongInductionOn
    rename_i n ih
    cases n with
    | zero =>
      intro a len_a
      simp only [List.length_eq_zero] at len_a
      rw [len_a]
      exact acc_empty r
    | succ n =>
      intro a
      cases a with
      | nil =>
        intro len_a
        simp only [List.length_nil, self_eq_add_left, add_eq_zero, one_ne_zero, and_false]
          at len_a
      | cons head tail =>
        intro len_a
        simp only [List.length_cons, Nat.succ_eq_add_one, add_left_inj] at len_a
        apply lexAccessible' r (n+1)
        · exact WellFounded.apply h head
        · exact fun b bl =>ih b.length bl _ rfl
        · rw [len_a]
          exact lt_add_one n
        · intro l ll
          apply ih l.length
          simp only [List.length_cons, Nat.succ_eq_add_one] at ll
          · rw [← len_a]
            exact ll
          rfl
  exact fun a => H a.length _ rfl
