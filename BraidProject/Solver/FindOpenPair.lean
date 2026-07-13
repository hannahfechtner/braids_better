import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic

namespace Braid

def FindOpenPair (L : List (ℕ × Bool)) :
    Option (List (ℕ × Bool) × ((ℕ) × (ℕ)) × List (ℕ × Bool)) :=
  match L with
  | [] => none
  | _ :: [] => none
  | (a, false) :: (b, true) :: tail =>
    some ([], (a, b), tail)
  | head :: tail =>
    match FindOpenPair tail with
    | none => none
    | some (c, e, f) =>
      some (head :: c, e, f)

namespace FindOpenPair

@[simp]
theorem nil : FindOpenPair [] = none := by simp [FindOpenPair]

@[simp]
theorem singleton : FindOpenPair [a] = none := by
  unfold FindOpenPair; simp

theorem cons_eq_none (h : FindOpenPair (a :: b) = none) : FindOpenPair b = none := by
  induction b with
  | nil => simp
  | cons head tail ih =>
    unfold FindOpenPair at h
    rcases a with ⟨a1, a2⟩
    rcases head with ⟨h3, h4⟩
    cases a2 with
    | false =>
      cases h4 with
      | true => simp at h
      | false =>
        cases ha : FindOpenPair ((h3, false) :: tail) with
        | none => rfl
        | some a => simp [ha] at h
    | true =>
      cases ha : FindOpenPair ((h3, h4) :: tail) with
      | none => rfl
      | some a => simp [ha] at h

theorem cons_true_eq_none_iff : FindOpenPair ((a, true) :: tail) = none ↔ FindOpenPair tail = none := by
  constructor
  · exact cons_eq_none
  intro h
  cases tail with
    | nil => simp [FindOpenPair]
    | cons head tail => simp [h, FindOpenPair]

@[simp]
theorem eq_some_cons_true (h : FindOpenPair tail = some ⟨a, b, c⟩) :
    FindOpenPair ((d, true) :: tail) = some ⟨(d, true):: a, b, c⟩ := by
  conv => lhs; unfold FindOpenPair
  cases tail with
  | nil => simp at h
  | cons headt tailt => simp [h]

theorem first_elem_eq_nil (h : FindOpenPair a = some ([], d, e)) : ∃ a1 a2, a = (a1, false) :: a2 := by
  induction a with
  | nil => simp [FindOpenPair] at h
  | cons head tail ih =>
    rcases head with ⟨h1, t1⟩
    cases t1 with
    | false => use h1, tail
    | true =>
      cases tail with
      | nil => simp [FindOpenPair] at h
      | cons head1 tail1 =>
        rcases head1 with ⟨h2, t2⟩
        cases hf : FindOpenPair ((h2, t2) :: tail1) with
        | none => simp [FindOpenPair, hf] at h
        | some _ =>
          simp [FindOpenPair, hf] at h

theorem true_cons_eq_some (h : FindOpenPair ((a, true)::b) = some (c1 :: c, d, e)) :
    FindOpenPair b = (c, d, e) ∧ c1 = (a, true) := by
  induction b with
  | nil =>
    simp [FindOpenPair] at h
  | cons hb tb ih =>
    rcases hb with ⟨fb, sb⟩
    cases sb with
    | false =>
      cases h1 : FindOpenPair ((fb, false) :: tb) with
      | none => simp [h1, FindOpenPair] at h
      | some val =>
        simp only [FindOpenPair, h1, Prod.mk.eta, Option.some.injEq, Prod.mk.injEq,
          List.cons.injEq] at h
        constructor
        · rw [← h.2, ← h.1.2]
        exact h.1.1.symm
    | true =>
      simp only [FindOpenPair] at h
      cases h1 : FindOpenPair ((fb, true) :: tb) with
      | none => simp [h1] at h
      | some val =>
        simp [h1] at h
        constructor
        · rw [← h.2, ← h.1.2]
        exact h.1.1.symm

theorem spec {L : List ((ℕ × Bool))} (h : FindOpenPair L = some (c, d, e)) :
    L = c ++ ([(d.1, false)] ++ [(d.2, true)]) ++ e := by
  induction L generalizing c d e with
  | nil => simp [FindOpenPair] at h
  | cons head tail ih =>
  cases tail with
  | nil => simp [FindOpenPair] at h
  | cons head1 tail1 =>
    rcases head with ⟨fst1, snd1⟩
    cases snd1 with
    | false =>
      rcases head1 with ⟨fst2, snd2⟩
      cases snd2 with
      | false =>
        unfold FindOpenPair at h
        cases hcases : FindOpenPair ((fst2, false) :: tail1) with
        | none => simp [hcases] at h
        | some thing =>
          rcases thing with ⟨v1, v2, v3⟩
          simp only [hcases, Option.some.injEq, Prod.mk.injEq] at h
          rw [h.2.1, h.2.2] at hcases
          rw [← h.1, ih hcases]
          simp
      | true =>
        simp only [FindOpenPair, Option.some.injEq, Prod.mk.injEq, List.nil_eq] at h
        rw [h.1, h.2.2]
        have H := Prod.mk.inj h.2.1
        rw [← H.1, ← H.2]
        simp
    | true =>
      cases c with
      | nil =>
        rcases first_elem_eq_nil h with ⟨a1, a2, ha⟩
        simp at ha
      | cons head3 tail3 =>
        apply true_cons_eq_some at h
        rw [ih h.1, ← h.2]
        simp

theorem pair_eq_some {a b : ℕ × Bool} (h : FindOpenPair [a,b] = some (c, d, e)) :
    d = (a.1, b.1) := by
  have H := spec h
  rcases d with ⟨d1, d2⟩
  have h_len := congr_arg List.length H
  simp only [List.length, zero_add, Nat.reduceAdd, List.cons_append, List.nil_append,
    List.append_assoc, List.length_append] at h_len
  simp only [List.cons_append, List.nil_append, List.append_assoc] at H
  have hc : c = [] := List.length_eq_zero_iff.mp (by omega)
  have he : e = [] := List.length_eq_zero_iff.mp (by omega)
  rw [hc, he, List.nil_append, List.cons.injEq, List.cons.injEq] at H
  simp [H]
