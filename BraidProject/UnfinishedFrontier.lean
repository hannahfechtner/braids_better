import BraidProject.DataCarrying.SignedList
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

namespace Braid

open SignedList

theorem true_false_not_infix_false_true (h : c1 ++ [(c2, true), (c3, false)] ++ c4 = a ++ b)
    (ha : SignedList.is_false a) (hb : SignedList.is_true b) : False := by
  have : c1 ++ [(c2, true), (c3, false)] ++ c4 =
    c1 ++ [(c2, true)] ++ ([(c3, false)] ++ c4) := by simp
  rw [this] at h
  rcases List.append_eq_append_iff.mp h with ⟨m, hm1, hm2⟩ | ⟨m, hm1, hm2⟩
  · rw [hm1] at ha
    specialize ha (c2, true) (by simp)
    simp only [Bool.true_eq_false] at ha
  rw [hm2] at hb
  specialize hb (c3, false) (by simp)
  simp only [Bool.false_eq_true] at hb

theorem eq_left_singleton_of_is_false_append_eq_unfinished_cell
    (h : a.length > 0) (h1 : SignedList.is_false a) (h3 : a ++ b = [(a1, false), (b1, true)]) :
    a = [(a1, false)]  := by
  have H : a.length = 1 := by
    have := congr_arg List.length h3
    have : ¬ a.length > 2 := by grind
    have : ¬ a.length = 2 := by
      intro h
      have : b = [] := by
        apply List.eq_nil_of_length_eq_zero
        grind
      rw [this, List.append_nil] at h3
      rw [h3] at h1
      specialize h1 (b1, true)
      simp at h1
    omega
  change a ++ b = [(a1, false)] ++ [(b1, true)] at h3
  exact (List.append_inj_left h3.symm H.symm).symm

theorem eq_right_singleton_of_is_true_append_eq_unfinished_cell (h : b.length > 0)
    (h1 : SignedList.is_true b) (h3 : a ++ b = [(a1, false), (b1, true)]) :
    b = [(b1, true)]  := by
  have H : b.length = 1 := by
    have h2 : ¬ b.length > 2 := by
        intro h
        apply congr_arg List.length at h3
        simp at h3
        omega
    have H : ¬ b.length = 2 := by
      intro h
      have H : a = [] := by
        apply congr_arg List.length at h3
        simp only [List.length_append, h, List.length_cons, List.length_nil, Nat.zero_add,
          Nat.reduceAdd, Nat.add_eq_right, List.length_eq_zero_iff] at h3
        exact h3
      rw [H, List.nil_append] at h3
      rw [h3] at h1
      simp only [SignedList.is_true] at h1
      specialize h1 (a1,false) List.mem_cons_self
      simp only [Bool.false_eq_true] at h1
    omega
  change a ++ b = [(a1, false)] ++ [(b1, true)] at h3
  exact (List.append_inj_right' h3.symm H.symm).symm

theorem eq_singletons_of_false_true_eq_unfinished_cell
    (ha : SignedList.is_false a) (hb : SignedList.is_true b) (h : [(c, false), (d, true)] = a ++ b) :
    a = [(c, false)] ∧ b = [(d, true)] := by
  have H1 : ¬ a.length = 0 := by
    intro h1
    rw [List.length_eq_zero_iff.mp h1, List.nil_append] at h
    rw [← h] at hb
    simp [SignedList.is_true] at hb
  have H2 : ¬ b.length = 0 := by
    intro h1
    rw [List.length_eq_zero_iff.mp h1, List.append_nil] at h
    rw [← h] at ha
    simp [SignedList.is_false] at ha
  have := eq_right_singleton_of_is_true_append_eq_unfinished_cell (Nat.zero_lt_of_ne_zero H2) hb h.symm
  have := eq_left_singleton_of_is_false_append_eq_unfinished_cell (Nat.zero_lt_of_ne_zero H1) ha h.symm
  grind

def true_prefix_of_unfinished_frontier_generalized
    (h1 : SignedList.is_true bot3) (h : k₂ ++ [(a1, false)] ++ l = bot3 ++ mid3 ++ up3) :
    List.PrefixData bot3 k₂ := by
  induction k₂ generalizing bot3 with
  | nil =>
    cases bot3 with
    | nil => exact List.PrefixData.nil
    | cons head tail =>
      grind [SignedList.is_true]
  | cons head tail ih =>
    cases bot3 with
    | nil => exact List.PrefixData.nil
    | cons head1 tail1 =>
      simp only [List.cons_append, List.cons.injEq] at h
      specialize @ih tail1 (SignedList.is_true_of_cons h1).2 h.2
      rw [h.1]
      exact (List.PrefixData.cons head1) ih

def true_prefix_of_unfinished_frontier
    (h1 : SignedList.is_true bot3) (h : k₂ ++ [(a1, false), (b1, true)] ++ l = bot3 ++ mid3 ++ up3) :
    List.PrefixData bot3 k₂ := by
  have : k₂ ++ [(a1, false), (b1, true)] ++ l =  k₂ ++ [(a1, false)] ++ ([(b1, true)] ++ l) := by simp
  rw [this] at h
  exact true_prefix_of_unfinished_frontier_generalized h1 h

theorem true_prefix_of_unfinished_frontier_generalized_overall {α : Type} {a1 a2 : α} {k₂ l up3 bot3 : List (α × Bool)}
    (h1 : SignedList.is_true bot3) (h2 : is_true k₂) (h : k₂ ++ [(a1, false)] ++ l = bot3 ++ [(a2, false)] ++ up3) :
    k₂ = bot3 := by
  have h3 := List.PrefixData.to_IsPrefix <| true_prefix_of_unfinished_frontier_generalized h1 h
  have h4 := List.PrefixData.to_IsPrefix <| true_prefix_of_unfinished_frontier_generalized h2 h.symm
  exact h4.eq_of_length (h4.length_le.antisymm h3.length_le)

def false_prefix_of_unfinished_frontier_generalized
    (h1 : SignedList.is_false t3) (h : k₂ ++ [(a1, true)] ++ l = t3 ++ mid3 ++ up3) :
    List.PrefixData t3 k₂ := by
  induction k₂ generalizing t3 with
  | nil =>
    cases t3 with
    | nil => exact List.PrefixData.nil
    | cons head tail =>
      grind [SignedList.is_false]
  | cons head tail ih =>
    cases t3 with
    | nil => exact List.PrefixData.nil
    | cons head1 tail1 =>
      simp only [List.cons_append, List.cons.injEq] at h
      specialize @ih tail1 (SignedList.is_false_of_cons h1).2 h.2
      rw [h.1]
      exact (List.PrefixData.cons head1) ih

theorem false_prefix_of_unfinished_frontier_generalized_overall {α : Type} {a1 a2 : α} {k₂ l up3 t3 : List (α × Bool)}
    (h1 : SignedList.is_false t3) (h2 : is_false k₂) (h : k₂ ++ [(a1, true)] ++ l = t3 ++ [(a2, true)] ++ up3) :
    k₂ = t3 := by
  have h3 := List.PrefixData.to_IsPrefix <| false_prefix_of_unfinished_frontier_generalized h1 h
  have h4 := List.PrefixData.to_IsPrefix <| false_prefix_of_unfinished_frontier_generalized h2 h.symm
  exact h4.eq_of_length (h4.length_le.antisymm h3.length_le)

theorem false_suffix_of_unfinished_frontier_generalized_overall {α : Type} {a1 a2 : α} {k₂ l up3 t3 : List (α × Bool)}
    (h1 : SignedList.is_false t3) (h2 : is_false k₂) (h : l ++ [(a1, true)] ++ k₂ = up3 ++ [(a2, true)] ++ t3) :
    k₂ = t3 := by
  have hr := congr_arg List.reverse h
  simp only [List.reverse_append, List.reverse_singleton, ← List.append_assoc] at hr
  have h1' : SignedList.is_false t3.reverse := fun x hx => h1 x (List.mem_reverse.mp hx)
  have h2' : SignedList.is_false k₂.reverse := fun x hx => h2 x (List.mem_reverse.mp hx)
  exact List.reverse_injective (false_prefix_of_unfinished_frontier_generalized_overall h1' h2' hr)

def false_prefix_of_unfinished_frontier (h1 : SignedList.is_false t3) (h : tk ++ [(a1, false), (b1, true)] ++ l =
    t3 ++ (f, false) :: (m ++ [(c, true)]) ++ up3) : List.PrefixData t3 tk := by
  induction tk generalizing t3 with
  | nil =>
    cases t3 with
    | nil => exact List.PrefixData.nil
    | cons head tail =>
      cases tail with
      | nil =>
        simp at h
      | cons ht tt =>
        simp only [List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq] at h
        rw [← h.2.1] at h1
        specialize h1 (b1, true) (by simp)
        simp at h1
  | cons head tail ih =>
    cases t3 with
    | nil =>
      exact List.PrefixData.nil
    | cons ht tt =>
      simp only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq] at h
      rw [h.1]
      exact List.PrefixData.cons ht (@ih tt (SignedList.is_false_of_cons h1).2 (by simp [h.2]))

theorem empty_middle_frontier_of_pos_neg_frontier (h : PosNegData c)
    (hf : c = c1 ++ [(c2, false)] ++ (m1 ++ [(d2, true)] ++ d1)) : False := by
  rcases h with ⟨a, b, ha, hb, rfl⟩
  rw [List.append_assoc m1] at hf
  rcases List.append_eq_append_iff.mp hf with ⟨r, hr1, hr2⟩ | ⟨r, hr1, hr2⟩
  · rw [hr2] at hb
    specialize hb (d2, true) (by simp)
    aesop
  rw [hr1] at ha
  specialize ha (c2, false) (by simp)
  aesop
