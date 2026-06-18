import BraidProject.List_C
import BraidProject.SignedOptionList
import Mathlib.GroupTheory.FreeGroup.Basic

namespace Braid

def to_vertical_edge (a : List ℕ) : List (Option ℕ × Bool) :=
  match a with
  | [] => [(none, false)]
  | _ => List.map (fun x => (some x, false)) a.reverse

def to_horizontal_edge (a : List ℕ) : List (Option ℕ × Bool) :=
  match a with
  | [] => [(none, true)]
  | _ => List.map (fun x => (some x, true)) a

@[simp]
theorem to_vertical_edge_nil : to_vertical_edge [] = [(none, false)] := rfl

@[simp]
theorem to_vertical_edge_singleton (a : ℕ) : to_vertical_edge [a] = [(some a, false)] := rfl

@[simp]
theorem to_vertical_edge_pair (a : ℕ) : to_vertical_edge [a, b] = [(some b, false), (some a, false)] := rfl

@[simp]
theorem to_vertical_edge_cons_cons : to_vertical_edge (a :: b :: c) = to_vertical_edge (b :: c) ++ [(some a, false)] := by
  simp [to_vertical_edge]

theorem to_vertical_edge_reverse : to_vertical_edge a.reverse = (to_vertical_edge a).reverse := by
  induction a with
  | nil => simp
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp [to_vertical_edge, List.nil_append]
    | cons head1 tail1 =>
      simp_all [to_vertical_edge, List.append_assoc, List.reverse_cons, List.reverse_append]

theorem to_vertical_edge_length_pos : (to_vertical_edge a).length > 0 := by
  induction a with
  | nil => simp
  | cons head tail ih => cases tail; all_goals simp

@[simp]
theorem to_horizontal_edge_nil : to_horizontal_edge [] = [(none, true)] := rfl

@[simp]
theorem to_horizontal_edge_singleton (a : ℕ) : to_horizontal_edge [a] = [(some a, true)] := rfl

@[simp]
theorem to_horizontal_edge_pair (a : ℕ) : to_horizontal_edge [a, b] = [(some a, true), (some b, true)] := rfl

@[simp]
theorem to_horizontal_edge_cons_cons : to_horizontal_edge (a :: b :: c) = (some a, true) :: to_horizontal_edge (b :: c):= by
  simp [to_horizontal_edge]

theorem to_horizontal_edge_length_pos : (to_horizontal_edge a).length > 0 := by
  induction a with
  | nil => simp
  | cons head tail ih => cases tail; all_goals simp

theorem to_horizontal_edge_eq_cons (c) : ∃ a b, to_horizontal_edge c = (a, true) :: b := by
  induction c with
  | nil => use none, []; rfl
  | cons head tail ih =>
    cases tail
    · use some head, []
      rfl
    simp

theorem to_horizontal_edge_options (c) : (∃ a, to_horizontal_edge c = [(a, true)]) ∨ ∃ a b, to_horizontal_edge c = (some a, true) :: (to_horizontal_edge b) := by
  induction c with
  | nil => simp
  | cons head tail ih => cases tail; all_goals simp

theorem to_vertical_edge_inj (h : to_vertical_edge a = to_vertical_edge b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons head tail =>
      simp only [to_vertical_edge, List.reverse_cons, List.map_append, List.map_reverse,
        List.map_cons, List.map_nil] at h
      have H2 : List.getLast? [(none, false)] =
          List.getLast? ((List.map (fun x ↦ (some x, false)) tail).reverse ++ [
          (some head, false)]) := by
        rw [h]
      simp at H2
  | cons head tail ih =>
    cases b with
    | nil =>
      simp only [to_vertical_edge, List.reverse_cons, List.map_append, List.map_reverse,
        List.map_cons, List.map_nil] at h
      have H2 : List.getLast? [(none, false)] =
        List.getLast? ((List.map (fun x ↦ (some x, false)) tail).reverse ++ [(some head, false)]) := by
        rw [h]
      simp at H2
    | cons headb tailb =>
      simp only [to_vertical_edge, List.reverse_cons, List.map_append, List.map_reverse,
        List.map_cons, List.map_nil, List.append_singleton_inj, List.reverse_inj, Prod.mk.injEq,
        Option.some.injEq, and_true] at h
      have H2 : List.getLast? ((List.map (fun x ↦ (some x, false)) tail).reverse ++ [(some head, false)]) =
        List.getLast? ((List.map (fun x ↦ (some x, false)) tailb).reverse ++ [(some headb, false)]) := by
        congr 1
        simp only [List.append_singleton_inj, List.reverse_inj, Prod.mk.injEq, Option.some.injEq,
          and_true]
        exact h
      simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_reverse,
        List.head?_map, Option.some_or, Option.some.injEq, Prod.mk.injEq, and_true] at H2
      simp only [H2, List.cons.injEq, true_and]
      apply ih
      rw [← H2] at h
      cases tail with
      | nil =>
        cases tailb with
        | nil => rfl
        | cons t1 t2 => simp at h
      | cons t1 t2 =>
        cases tailb with
        | nil => simp at h
        | cons t3 t4 =>
          simp only [to_vertical_edge]
          simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, Option.some.injEq,
            and_true] at h
          simp [h]

theorem to_horizontal_edge_inj (h : to_horizontal_edge a = to_horizontal_edge b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons head tail => simp [to_horizontal_edge] at h
  | cons head tail ih =>
    cases b with
    | nil => simp [to_horizontal_edge] at h
    | cons headb tailb =>
      simp only [to_horizontal_edge, List.map_cons, List.cons.injEq, Prod.mk.injEq,
        Option.some.injEq, and_true] at h
      simp only [h, List.cons.injEq, true_and]
      apply ih
      cases tail with
      | nil =>
        cases tailb with
        | nil => rfl
        | cons t1 t2 => simp at h
      | cons t3 t4 =>
        cases tailb with
        | nil => simp at h
        | cons t1 t2 =>
          simp only [to_horizontal_edge, List.map_cons, List.cons.injEq, Prod.mk.injEq,
            Option.some.injEq, and_true]
          simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, Option.some.injEq,
            and_true] at h
          exact h.2

theorem FreeGroup.invRev_to_horizontal_edge : FreeGroup.invRev (to_horizontal_edge a) = to_vertical_edge a := by
  cases a with
  | nil => simp [to_horizontal_edge, to_vertical_edge, FreeGroup.invRev]
  | cons head tail =>
    simp [FreeGroup.invRev, to_horizontal_edge,to_vertical_edge]

theorem FreeGroup.invRev_to_vertical_edge : FreeGroup.invRev (to_vertical_edge a) = to_horizontal_edge a := by
  cases a with
  | nil => simp [to_horizontal_edge, to_vertical_edge, FreeGroup.invRev]
  | cons head tail =>
    simp [FreeGroup.invRev, to_vertical_edge, to_horizontal_edge]

open SignedOptionList

@[simp]
theorem toList_to_vertical_edge : toList (to_vertical_edge a) = a.reverse := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp [toList, List.nil_append]
    | cons head1 tail1 =>
      simp_all [toList_append, to_vertical_edge]

@[simp]
theorem toList_to_vertical_edge_rev : toList (to_vertical_edge a).reverse = a := by
  rw [← to_vertical_edge_reverse, toList_to_vertical_edge, List.reverse_reverse]

@[simp]
theorem toList_to_horizontal_edge : toList (to_horizontal_edge a) = a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    simp only [to_horizontal_edge, List.map_cons, toList_cons_some, List.cons.injEq, true_and]
    cases tail with
    | nil => simp
    | cons head tail => exact ih

open SignedList

def is_false_to_vertical_edge : is_false (to_vertical_edge a) := by
  cases a ; all_goals simp [to_vertical_edge, is_false]

def is_true_to_horizontal_edge : is_true (to_horizontal_edge a) := by
  cases a ; all_goals simp [to_horizontal_edge, is_true]

theorem not_false_true_infix_horizontal_vertical_edge (h : to_horizontal_edge d ++ to_vertical_edge c = k ++ [(a1, false), (b1, true)] ++ l) : False := by
  induction k generalizing d with
  | nil =>
    rcases to_horizontal_edge_eq_cons d with ⟨w, w2, hw⟩
    grind
  | cons head tail ih =>
    rcases to_horizontal_edge_options d with h1 | h2
    · rcases h1 with ⟨a3, h3⟩
      rw [h3] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at h
      have : is_false (tail ++ (a1, false) :: (b1, true) :: l) := by
        rw [← h.2]
        exact is_false_to_vertical_edge
      specialize this (b1, true)
      simp at this
    grind

def option_to_list (a : Option α) : List α :=
  match a with
  | none => []
  | some b => [b]

@[simp]
theorem to_horizontal_edge_option_to_list : to_horizontal_edge (option_to_list a) = [(a, true)] := by
  cases a with
  | none => rfl
  | some val => rfl

@[simp]
theorem to_vertical_edge_option_to_list : to_vertical_edge (option_to_list a) = [(a, false)] := by
  cases a with
  | none => rfl
  | some val => rfl

theorem eq_left_singleton_of_is_false_append_eq_unfinished_cell (h : a.length > 0) (h1 : is_false a) (h3 : a ++ b = [(a1, false), (b1, true)]) :
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

theorem eq_right_singleton_of_is_true_append_eq_unfinished_cell (h : b.length > 0) (h1 : is_true b) (h3 : a ++ b = [(a1, false), (b1, true)]) :
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
      simp only [is_true] at h1
      specialize h1 (a1,false) List.mem_cons_self
      simp only [Bool.false_eq_true] at h1
    omega
  change a ++ b = [(a1, false)] ++ [(b1, true)] at h3
  exact (List.append_inj_right' h3.symm H.symm).symm

theorem eq_singletons_of_false_true_eq_unfinished_cell (ha : is_false a) (hb : is_true b) (h : [(c, false), (d, true)] = a ++ b) :
    a = [(c, false)] ∧ b = [(d, true)] := by
  have H1 : ¬ a.length = 0 := by
    intro h1
    rw [List.length_eq_zero_iff.mp h1, List.nil_append] at h
    rw [← h] at hb
    simp [is_true] at hb
  have H2 : ¬ b.length = 0 := by
    intro h1
    rw [List.length_eq_zero_iff.mp h1, List.append_nil] at h
    rw [← h] at ha
    simp [is_false] at ha
  have := eq_right_singleton_of_is_true_append_eq_unfinished_cell (Nat.zero_lt_of_ne_zero H2) hb h.symm
  have := eq_left_singleton_of_is_false_append_eq_unfinished_cell (Nat.zero_lt_of_ne_zero H1) ha h.symm
  grind


def true_prefix_of_unfinished_frontier (h1 : is_true bot3) (h : k₂ ++ [(a1, false), (b1, true)] ++ l = bot3 ++ mid3 ++ up3) :
    List.PrefixData bot3 k₂ := by
  induction k₂ generalizing bot3 with
  | nil =>
    cases bot3 with
    | nil => exact List.PrefixData.nil
    | cons head tail =>
      grind [is_true]
  | cons head tail ih =>
    cases bot3 with
    | nil => exact List.PrefixData.nil
    | cons head1 tail1 =>
      simp only [List.cons_append, List.cons.injEq] at h
      specialize @ih tail1 (is_true_of_cons h1).2 h.2
      rw [h.1]
      exact (List.PrefixData.cons head1) ih

def false_prefix_of_unfinished_frontier (h1 : is_false t3) (h : tk ++ [(a1, false), (b1, true)] ++ l =
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
      exact List.PrefixData.cons ht (@ih tt (is_false_of_cons h1).2 (by simp [h.2]))
