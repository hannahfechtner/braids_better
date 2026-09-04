import BraidProject.List_C
import BraidProject.SignedOptionList
import BraidProject.SignedList_C
import Mathlib.GroupTheory.FreeGroup.Basic

namespace Braid

def to_vertical_edge_no_epsilon {α : Type} (a : List α) : List (α × Bool) :=
  List.map (fun x => (x, false)) a.reverse

def to_horizontal_edge_no_epsilon {α : Type} (a : List α) : List (α × Bool) :=
  List.map (fun x => (x, true)) a

def to_vertical_edge (a : List α) : List (Option α × Bool) :=
  match a with
  | [] => [(none, false)]
  | _ => List.map (fun x => (some x, false)) a.reverse

def to_horizontal_edge (a : List α) : List (Option α × Bool) :=
  match a with
  | [] => [(none, true)]
  | _ => List.map (fun x => (some x, true)) a

@[simp]
theorem to_vertical_edge_no_epsilon_nil {α : Type} : to_vertical_edge_no_epsilon ([] : List α) = [] := rfl

@[simp]
theorem to_vertical_edge_no_epsilon_one : to_vertical_edge_no_epsilon (1 : FreeMonoid α) = [] := rfl

@[simp]
theorem to_vertical_edge_no_epsilon_singleton (a : α) : to_vertical_edge_no_epsilon [a] = [(a, false)] := rfl

@[simp]
theorem to_vertical_edge_no_epsilon_cons (a : α) (b : List α) : to_vertical_edge_no_epsilon (a :: b) = to_vertical_edge_no_epsilon b ++ [(a, false)] := by
  simp [to_vertical_edge_no_epsilon]

@[simp]
theorem to_vertical_edge_no_epsilon_pair (a : α) : to_vertical_edge_no_epsilon [a, b] = [(b, false), (a, false)] := rfl

@[simp]
theorem to_vertical_edge_no_epsilon_cons_cons : to_vertical_edge_no_epsilon (a :: b :: c) = to_vertical_edge_no_epsilon (b :: c) ++ [(a, false)] := by
  simp [to_vertical_edge_no_epsilon]

@[simp]
theorem to_vertical_edge_no_epsilon_reverse {α : Type} {a : List α} : to_vertical_edge_no_epsilon a.reverse = (to_vertical_edge_no_epsilon a).reverse := by
  induction a with
  | nil => simp
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp [to_vertical_edge_no_epsilon, List.nil_append]
    | cons head1 tail1 =>
      simp_all [to_vertical_edge_no_epsilon, List.append_assoc, List.reverse_cons, List.reverse_append]

theorem to_vertical_edge_no_epsilon_eq_nil {α : Type} {a : List α} (h : to_vertical_edge_no_epsilon (a : List α) = []) : a = [] := by
  cases a
  · rfl
  simp at h

theorem to_vertical_edge_no_epsilon_eq_append {a : List α} (h : to_vertical_edge_no_epsilon a = b ++ c) :
    ∃ a₁ a₂, a = a₁ ++ a₂ ∧ to_vertical_edge_no_epsilon a₁ = c ∧ to_vertical_edge_no_epsilon a₂ = b := by
  induction a using List.reverseRecOn generalizing b with
  | nil =>
    rw [to_vertical_edge_no_epsilon_nil] at h
    rcases List.append_eq_nil_iff.mp h.symm with ⟨hb, hc⟩
    exact ⟨[], [], rfl, by rw [to_vertical_edge_no_epsilon_nil, hc],
      by rw [to_vertical_edge_no_epsilon_nil, hb]⟩
  | append_singleton front caboose ih =>
    have hsplit : to_vertical_edge_no_epsilon (front ++ [caboose]) =
        (caboose, false) :: to_vertical_edge_no_epsilon front := by
      simp [to_vertical_edge_no_epsilon]
    rw [hsplit] at h
    match b with
    | [] =>
      rw [List.nil_append] at h
      exact ⟨front ++ [caboose], [], (List.append_nil _).symm,
        by rw [hsplit, h], to_vertical_edge_no_epsilon_nil⟩
    | hb :: tb =>
      rw [List.cons_append, List.cons.injEq] at h
      rcases ih h.2 with ⟨a₁, a₂, ha, h1, h2⟩
      refine ⟨a₁, a₂ ++ [caboose], ?_, h1, ?_⟩
      · rw [ha, List.append_assoc]
      · have : to_vertical_edge_no_epsilon (a₂ ++ [caboose]) =
            (caboose, false) :: to_vertical_edge_no_epsilon a₂ := by
          simp [to_vertical_edge_no_epsilon]
        rw [this, h2, ← h.1]
@[simp]
theorem to_vertical_edge_no_epsilon_length : (to_vertical_edge_no_epsilon a).length = a.length := by
  unfold to_vertical_edge_no_epsilon
  simp

@[simp]
theorem to_vertical_edge_nil : to_vertical_edge ([] : List α) = [(none, false)] := rfl

@[simp]
theorem to_vertical_edge_one : to_vertical_edge (1 : FreeMonoid α) = [(none, false)] := rfl

@[simp]
theorem to_vertical_edge_singleton (a : α) : to_vertical_edge [a] = [(some a, false)] := rfl

@[simp]
theorem to_vertical_edge_pair (a : α) : to_vertical_edge [a, b] = [(some b, false), (some a, false)] := rfl

@[simp]
theorem to_vertical_edge_cons_cons : to_vertical_edge (a :: b :: c) = to_vertical_edge (b :: c) ++ [(some a, false)] := by
  simp [to_vertical_edge]

@[simp]
theorem to_vertical_edge_append (ha : a.length > 0) (hb : b.length > 0) :
    to_vertical_edge (a ++ b) = to_vertical_edge b ++ to_vertical_edge a := by
  unfold to_vertical_edge
  aesop

@[simp]
theorem to_vertical_edge_no_epsilon_append {a b : List α} :
  to_vertical_edge_no_epsilon (a ++ b) = to_vertical_edge_no_epsilon b ++ to_vertical_edge_no_epsilon a := by
  simp [to_vertical_edge_no_epsilon]

@[simp]
theorem to_vertical_edge_no_epsilon_mul {a b : FreeMonoid α} :
  to_vertical_edge_no_epsilon (a * b) = to_vertical_edge_no_epsilon b ++ to_vertical_edge_no_epsilon a := by
  rw [← to_vertical_edge_no_epsilon_append]
  rfl

theorem to_vertical_edge_reverse {a : List α} : to_vertical_edge a.reverse = (to_vertical_edge a).reverse := by
  induction a with
  | nil => simp
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp [to_vertical_edge, List.nil_append]
    | cons head1 tail1 =>
      simp_all [to_vertical_edge, List.append_assoc, List.reverse_cons, List.reverse_append]

theorem to_vertical_edge_length_pos {a : List α} : (to_vertical_edge a).length > 0 := by
  induction a with
  | nil => simp
  | cons head tail ih => cases tail; all_goals simp

@[simp]
theorem to_horizontal_edge_no_epsilon_nil : to_horizontal_edge_no_epsilon ([] : List (α)) = [] := rfl

@[simp]
theorem to_horizontal_edge_no_epsilon_one : to_horizontal_edge_no_epsilon (1 : FreeMonoid α) = [] := rfl

@[simp]
theorem to_horizontal_edge_no_epsilon_singleton (a : α) : to_horizontal_edge_no_epsilon [a] = [(a, true)] := rfl

@[simp]
theorem to_horizontal_edge_no_epsilon_pair (a : α) : to_horizontal_edge_no_epsilon [a, b] = [(a, true), (b, true)] := rfl

@[simp]
theorem to_horizontal_edge_no_epsilon_cons (a : α) (b : List α) : to_horizontal_edge_no_epsilon (a :: b) = (a, true) :: to_horizontal_edge_no_epsilon b := by
  simp [to_horizontal_edge_no_epsilon]

@[simp]
theorem to_horizontal_edge_no_epsilon_cons_cons : to_horizontal_edge_no_epsilon (a :: b :: c) = (a, true) :: to_horizontal_edge_no_epsilon (b :: c) := by
  simp [to_horizontal_edge_no_epsilon]

@[simp]
theorem to_horizontal_edge_no_epsilon_append {a b : List α} :
  to_horizontal_edge_no_epsilon (a ++ b) = to_horizontal_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b := by
  simp [to_horizontal_edge_no_epsilon]

@[simp]
theorem to_horizontal_edge_no_epsilon_mul {a b : FreeMonoid α} :
  to_horizontal_edge_no_epsilon (a * b) = to_horizontal_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b := by
  rw [← to_horizontal_edge_no_epsilon_append]
  rfl

theorem to_horizontal_edge_no_epsilon_eq_nil (h : to_horizontal_edge_no_epsilon a = []) : a = [] := by
  cases a
  · rfl
  simp at h

theorem to_horizontal_edge_no_epsilon_eq_append {a : List (α)} (h : to_horizontal_edge_no_epsilon a = b ++ c) :
  ∃ a₁ a₂, a = a₁ ++ a₂ ∧ to_horizontal_edge_no_epsilon a₁ = b ∧ to_horizontal_edge_no_epsilon a₂ = c := by
  induction a generalizing b with
  | nil =>
    rw [to_horizontal_edge_no_epsilon_nil] at h
    rcases List.append_eq_nil_iff.mp h.symm with ⟨hb, hc⟩
    exact ⟨[], [], rfl, by rw [to_horizontal_edge_no_epsilon_nil, hb],
      by rw [to_horizontal_edge_no_epsilon_nil, hc]⟩
  | cons head tail ih =>
    rw [to_horizontal_edge_no_epsilon_cons] at h
    match b with
    | [] =>
      rw [List.nil_append] at h
      exact ⟨[], head :: tail, rfl, to_horizontal_edge_no_epsilon_nil,
        by rw [to_horizontal_edge_no_epsilon_cons, h]⟩
    | hb :: tb =>
      rw [List.cons_append, List.cons.injEq] at h
      rcases ih h.2 with ⟨a₁, a₂, ha, h1, h2⟩
      refine ⟨head :: a₁, a₂, by rw [ha, List.cons_append], ?_, h2⟩
      rw [to_horizontal_edge_no_epsilon_cons, h1, ← h.1]

@[simp]
theorem to_horizontal_edge_no_epsilon_length : (to_horizontal_edge_no_epsilon a).length = a.length := by
  unfold to_horizontal_edge_no_epsilon
  simp

@[simp]
theorem to_horizontal_edge_nil : to_horizontal_edge ([] : List (α)) = [(none, true)] := rfl

@[simp]
theorem to_horizontal_edge_one : to_horizontal_edge (1 : FreeMonoid α) = [(none, true)] := rfl

@[simp]
theorem to_horizontal_edge_singleton (a : α) : to_horizontal_edge [a] = [(some a, true)] := rfl

@[simp]
theorem to_horizontal_edge_pair (a : α) : to_horizontal_edge [a, b] = [(some a, true), (some b, true)] := rfl

@[simp]
theorem to_horizontal_edge_cons_cons : to_horizontal_edge (a :: b :: c) = (some a, true) :: to_horizontal_edge (b :: c):= by
  simp [to_horizontal_edge]

theorem to_horizontal_edge_length_pos {a : List (α)} : (to_horizontal_edge a).length > 0 := by
  induction a with
  | nil => simp
  | cons head tail ih => cases tail; all_goals simp

theorem to_horizontal_edge_eq_cons (c : List (α)) : ∃ a b, to_horizontal_edge c = (a, true) :: b := by
  induction c with
  | nil => use none, []; rfl
  | cons head tail ih =>
    cases tail
    · use some head, []
      rfl
    simp

theorem to_horizontal_edge_append (ha : a.length > 0) (hb : b.length > 0) :
  to_horizontal_edge (a ++ b) = to_horizontal_edge a ++ to_horizontal_edge b := by
  unfold to_horizontal_edge
  aesop

theorem to_horizontal_edge_options (c : List (α)) : (∃ a, to_horizontal_edge c = [(a, true)]) ∨ ∃ a b, to_horizontal_edge c = (some a, true) :: (to_horizontal_edge b) := by
  induction c with
  | nil => simp
  | cons head tail ih => cases tail; all_goals simp

theorem to_vertical_edge_no_epsilon_injective (h : to_vertical_edge_no_epsilon a = to_vertical_edge_no_epsilon b) : a = b := by
  unfold to_vertical_edge_no_epsilon at h
  apply List.reverse_inj.mp
  apply List.map_injective_iff.mpr _ h
  intro a b hab
  simp only [Prod.mk.injEq, and_true] at hab
  exact hab

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

theorem to_horizontal_edge_no_epsilon_injective : @Function.Injective _ (List (α × Bool)) to_horizontal_edge_no_epsilon := by
  intro a b h
  unfold to_horizontal_edge_no_epsilon at h
  apply List.map_injective_iff.mpr _ h
  intro a b hab
  simp only [Prod.mk.injEq, and_true] at hab
  exact hab

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

theorem to_vertical_edge_no_epsilon_no_bool {L : List (α × Bool)} (h : SignedList.is_false L) :
  to_vertical_edge_no_epsilon (List.map (fun x ↦ x.1) L.reverse) = L := by
  induction L using List.reverseRecOn with
  | nil => simp [to_vertical_edge_no_epsilon]
  | append_singleton l a ih =>
    have hl : SignedList.is_false l :=(SignedList.is_false_of_append h).1
    simp [to_vertical_edge_no_epsilon]
    constructor
    · unfold to_vertical_edge_no_epsilon at ih
      specialize ih hl
      rw [← ih]
      simp
    have ha : SignedList.is_false [a] := (SignedList.is_false_of_append h).2
    specialize ha a (by simp)
    simp [← ha]

theorem to_horizontal_edge_no_epsilon_no_bool {L : List (α × Bool)} (h : SignedList.is_true L) :
  to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) L) = L := by
  induction L with
  | nil => simp [to_horizontal_edge_no_epsilon]
  | cons head tail ih =>
    have tt : SignedList.is_true tail := (SignedList.is_true_of_cons h).2
    specialize ih tt
    simp only [to_horizontal_edge_no_epsilon, List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · have ht : SignedList.is_true [head] := (SignedList.is_true_of_cons h).1
      specialize ht head (by simp)
      simp [← ht]
    rw [← ih]
    unfold to_horizontal_edge_no_epsilon
    simp

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


@[simp]
theorem toList_to_vertical_edge_no_epsilon {a : List (α)} : SignedList.toList (to_vertical_edge_no_epsilon a) = a.reverse := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp [SignedList.toList, List.nil_append]
    | cons head1 tail1 =>
      simp_all [SignedList.toList_append, to_vertical_edge_no_epsilon]

@[simp]
theorem toList_to_vertical_edge_no_epsilon_rev {a : List (α)} : SignedList.toList (to_vertical_edge_no_epsilon a).reverse = a := by
  rw [← to_vertical_edge_no_epsilon_reverse, toList_to_vertical_edge_no_epsilon, List.reverse_reverse]

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
theorem toList_to_vertical_edge_rev {a : List (α)} : toList (to_vertical_edge a).reverse = a := by
  rw [← to_vertical_edge_reverse, toList_to_vertical_edge, List.reverse_reverse]

@[simp]
theorem toList_to_horizontal_edge_no_epsilon {a : List (α)} : SignedList.toList (to_horizontal_edge_no_epsilon a) = a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp [SignedList.toList]
    | cons head1 tail1 =>
      simp_all [to_horizontal_edge_no_epsilon]


@[simp]
theorem toList_to_horizontal_edge : toList (to_horizontal_edge a) = a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    simp only [to_horizontal_edge, List.map_cons, toList_cons_some, List.cons.injEq, true_and]
    cases tail with
    | nil => simp
    | cons head tail => exact ih

@[simp]
theorem toList_invRev_to_vertical_edge : toList (FreeGroup.invRev (to_vertical_edge a1)) = a1 := by
  rw [FreeGroup.invRev_to_vertical_edge, toList_to_horizontal_edge]

theorem toSignedOptionList_to_vertical_edge_no_epsilon (ha : a.length > 0) :
  SignedList.to_SignedOptionList (to_vertical_edge_no_epsilon a) = to_vertical_edge a := by
  unfold to_vertical_edge
  split
  · simp at ha
  simp [to_vertical_edge_no_epsilon, SignedList.to_SignedOptionList]

theorem toSignedOptionList_to_horizontal_edge_no_epsilon (ha : a.length > 0) :
  SignedList.to_SignedOptionList (to_horizontal_edge_no_epsilon a) = to_horizontal_edge a := by
  unfold to_horizontal_edge
  split
  · simp at ha
  simp [to_horizontal_edge_no_epsilon, SignedList.to_SignedOptionList]

theorem toSignedList_to_vertical_edge {a : List (α)} :
    SignedOptionList.toSignedList (to_vertical_edge a) = to_vertical_edge_no_epsilon a := by
  induction a with
  | nil => simp
  | cons head tail ih =>
    cases tail with
    | nil => simp
    | cons head1 tail1 => simp_all

theorem toSignedList_to_horizontal_edge {a : List (α)} :
    SignedOptionList.toSignedList (to_horizontal_edge a) = to_horizontal_edge_no_epsilon a := by
  induction a with
  | nil => simp
  | cons head tail ih =>
    cases tail with
    | nil => simp
    | cons head1 tail1 => simp_all


def is_false_to_vertical_edge_no_epsilon : SignedList.is_false (to_vertical_edge_no_epsilon a) := by
  cases a ; all_goals simp [to_vertical_edge_no_epsilon, SignedList.is_false]

def is_false_to_vertical_edge : SignedList.is_false (to_vertical_edge a) := by
  cases a ; all_goals simp [to_vertical_edge, SignedList.is_false]

def is_true_to_horizontal_edge_no_epsilon : SignedList.is_true (to_horizontal_edge_no_epsilon a) := by
  cases a ; all_goals simp [to_horizontal_edge_no_epsilon, SignedList.is_true]

def is_true_to_horizontal_edge : SignedList.is_true (to_horizontal_edge a) := by
  cases a ; all_goals simp [to_horizontal_edge, SignedList.is_true]


theorem to_horizontal_edge_no_epsilon_toList_eq_toSignedList
    {b : List (Option α × Bool)} (h : SignedList.is_true b) :
    to_horizontal_edge_no_epsilon (SignedOptionList.toList b) = SignedOptionList.toSignedList b := by
  induction b with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [to_horizontal_edge_no_epsilon, SignedOptionList.toSignedList,
        ← ih (SignedList.is_true_of_cons h).2, SignedOptionList.toList]
    | (some _, true) =>
      simp [to_horizontal_edge_no_epsilon, SignedOptionList.toSignedList,
        ← ih (SignedList.is_true_of_cons h).2, SignedOptionList.toList]
    | (some a, false) =>
      have H := (SignedList.is_true_of_cons h).1 (some a, false) (by simp)
      simp at H

theorem to_vertical_edge_no_epsilon_toList_rev_eq_toSignedList
    {a : List (Option α × Bool)} (h : SignedList.is_false a) :
    to_vertical_edge_no_epsilon (SignedOptionList.toList a.reverse)
      = SignedOptionList.toSignedList a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [to_vertical_edge_no_epsilon, SignedOptionList.toSignedList,
        ← ih (SignedList.is_false_of_cons h).2, SignedOptionList.toList_append,
        SignedOptionList.toList]
    | (some a, true) =>
      have H := (SignedList.is_false_of_cons h).1 (some a, true) (by simp)
      simp at H
    | (some _, false) =>
      simp [to_vertical_edge_no_epsilon, SignedOptionList.toSignedList,
        ← ih (SignedList.is_false_of_cons h).2, SignedOptionList.toList_append,
        SignedOptionList.toList]

theorem to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList
    {a : List (Option α × Bool)} (h : SignedList.is_false a) :
    to_vertical_edge_no_epsilon (SignedOptionList.toList (FreeGroup.invRev a))
      = SignedOptionList.toSignedList a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [to_vertical_edge_no_epsilon, SignedOptionList.toSignedList,
        ← ih (SignedList.is_false_of_cons h).2,
        SignedOptionList.toList]
    | (some a, true) =>
      have H := (SignedList.is_false_of_cons h).1 (some a, true) (by simp)
      simp at H
    | (some _, false) =>
      simp [to_vertical_edge_no_epsilon, SignedOptionList.toSignedList,
        ← ih (SignedList.is_false_of_cons h).2,
        SignedOptionList.toList]

theorem toSignedList_eq_to_vertical_edge_no_epsilon_iff
    {a : List (Option α × Bool)} {m : List α} (ha : SignedList.is_false a) :
    toSignedList a = to_vertical_edge_no_epsilon m ↔ m = toList (FreeGroup.invRev a) := by
  constructor
  · intro h
    apply to_vertical_edge_no_epsilon_injective
    rw [to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList ha, ← h]
  intro h
  rw [h, to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList ha]

theorem toSignedList_prefix_to_vertical_edge_no_epsilon_iff
    {a : List (Option α × Bool)} {m : List α} (ha : SignedList.is_false a) :
    toSignedList a <+: to_vertical_edge_no_epsilon m ↔ toList (FreeGroup.invRev a) <:+ m := by
  constructor
  · intro h
    rcases h with ⟨r, hr⟩
    rcases @to_vertical_edge_no_epsilon_eq_append α _ _ _ hr.symm with ⟨b, c, rfl, hb, hc⟩
    use b
    congr
    exact ((toSignedList_eq_to_vertical_edge_no_epsilon_iff ha).mp hc.symm).symm
  intro h
  rcases h with ⟨r, rfl⟩
  rw [to_vertical_edge_no_epsilon_append, to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList ha]
  simp

theorem toSignedList_suffix_to_vertical_edge_no_epsilon_iff
    {a : List (Option α × Bool)} {m : List α} (ha : SignedList.is_false a) :
    toSignedList a <:+ to_vertical_edge_no_epsilon m ↔ toList (FreeGroup.invRev a) <+: m := by
  constructor
  · intro h
    rcases h with ⟨r, hr⟩
    rcases to_vertical_edge_no_epsilon_eq_append hr.symm with ⟨b, c, rfl, hb, hc⟩
    use c
    congr
    exact ((toSignedList_eq_to_vertical_edge_no_epsilon_iff ha).mp hb.symm).symm
  intro h
  rcases h with ⟨r, rfl⟩
  rw [to_vertical_edge_no_epsilon_append, to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList ha]
  simp

theorem toSignedList_eq_to_horizontal_edge_no_epsilon_iff
    {a : List (Option α × Bool)} {m : List α} (ha : SignedList.is_true a) :
    toSignedList a = to_horizontal_edge_no_epsilon m ↔ m = toList a := by
  constructor
  · intro h
    apply to_horizontal_edge_no_epsilon_injective
    rw [to_horizontal_edge_no_epsilon_toList_eq_toSignedList ha, ← h]
  intro h
  rw [h, to_horizontal_edge_no_epsilon_toList_eq_toSignedList ha]

theorem toSignedList_prefix_to_horizontal_edge_no_epsilon_iff
    {a : List (Option α × Bool)} {m : List α} (ha : SignedList.is_true a) :
    toSignedList a <+: to_horizontal_edge_no_epsilon m ↔ toList a <+: m := by
  constructor
  · intro h
    rcases h with ⟨r, hr⟩
    rcases to_horizontal_edge_no_epsilon_eq_append hr.symm with ⟨b, c, rfl, hb, hc⟩
    use c
    congr
    exact ((toSignedList_eq_to_horizontal_edge_no_epsilon_iff ha).mp hb.symm).symm
  intro h
  rcases h with ⟨r, rfl⟩
  rw [to_horizontal_edge_no_epsilon_append, to_horizontal_edge_no_epsilon_toList_eq_toSignedList ha]
  simp

theorem toList_to_SignedOptionList_to_vertical_edge_no_epsilon_reverse (a : List α) :
    SignedOptionList.toList (SignedList.to_SignedOptionList (to_vertical_edge_no_epsilon a)).reverse = a := by
  induction a with
  | nil => simp [SignedList.to_SignedOptionList, to_vertical_edge_no_epsilon]
  | cons a1 a2 ih =>
    simp_all [SignedList.to_SignedOptionList, to_vertical_edge_no_epsilon]

theorem toList_to_SignedOptionList_to_horizontal_edge_no_epsilon (b : List α) :
    SignedOptionList.toList (SignedList.to_SignedOptionList (to_horizontal_edge_no_epsilon b)) = b := by
  induction b with
  | nil => simp [SignedList.to_SignedOptionList, to_horizontal_edge_no_epsilon]
  | cons b1 b2 ih =>
    simp_all [SignedList.to_SignedOptionList, to_horizontal_edge_no_epsilon]

theorem recover_of_toSignedList_to_horizontal_edge_no_epsilon
    (h : to_horizontal_edge_no_epsilon c = SignedOptionList.toSignedList bot) :
    SignedOptionList.toList bot = c := by
  induction bot generalizing c with
  | nil => unfold to_horizontal_edge_no_epsilon at h; simp_all
  | cons head tail ih =>
    match head with
    | (none, bo) => simp [ih h]
    | (some hh, bo) =>
      simp only [SignedOptionList.toSignedList_cons_some] at h
      change _ = [(hh, bo)] ++ _ at h
      rcases to_horizontal_edge_no_epsilon_eq_append h with ⟨a₁, a₂, ha, ha₁, ha₂⟩
      simp only [SignedOptionList.toList_cons_some]
      rw [ih ha₂, ha]
      simp_all [to_horizontal_edge_no_epsilon]

theorem recover_of_toSignedList_to_vertical_edge_no_epsilon
    (h : SignedOptionList.toSignedList up = to_vertical_edge_no_epsilon d) :
    SignedOptionList.toList up.reverse = d := by
  induction up generalizing d with
  | nil => exact to_vertical_edge_no_epsilon_injective h
  | cons head tail ih =>
    rw [List.reverse_cons, SignedOptionList.toList_append]
    rw [SignedOptionList.toSignedList_cons] at h
    match head with
    | (none, bo) => simp [ih h]
    | (some hh, bo) =>
      simp only [SignedOptionList.toSignedList_cons_some, SignedOptionList.toSignedList_nil] at h
      rcases to_vertical_edge_no_epsilon_eq_append h.symm with ⟨a₁, a₂, ha, ha₁, ha₂⟩
      rw [ih ha₁.symm, ha, List.append_right_inj]
      unfold to_vertical_edge_no_epsilon at ha₂
      simp only [List.map_reverse, List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append,
        List.map_eq_singleton_iff, Prod.mk.injEq, Bool.false_eq, ↓existsAndEq, true_and] at ha₂
      simp [ha₂.1]

def NegPosData.of_to_vertical_edge_no_epsilon_to_horizontal_edge_no_epsilon :
    SignedList.NegPosData (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) := by
  use to_vertical_edge_no_epsilon a, to_horizontal_edge_no_epsilon b
  constructor
  constructor
  · exact is_false_to_vertical_edge_no_epsilon
  constructor
  · exact is_true_to_horizontal_edge_no_epsilon
  rfl

def PosNegData.of_to_horizontal_edge_no_epsilon_to_vertical_edge_no_epsilon :
    SignedList.PosNegData (to_horizontal_edge_no_epsilon a ++ to_vertical_edge_no_epsilon b) := by
  use to_horizontal_edge_no_epsilon a, to_vertical_edge_no_epsilon b
  constructor
  constructor
  · exact is_true_to_horizontal_edge_no_epsilon
  constructor
  · exact is_false_to_vertical_edge_no_epsilon
  rfl

open SignedList

theorem not_false_true_infix_horizontal_vertical_edge_no_epsilon
    (h : to_horizontal_edge_no_epsilon d ++ to_vertical_edge_no_epsilon c = k ++ [(a1, false), (b1, true)] ++ l) : False := by
  induction k generalizing d with
  | nil =>
    simp at h
    cases d with
    | nil =>
      simp only [to_horizontal_edge_no_epsilon_nil, List.nil_append] at h
      have := @is_false_to_vertical_edge_no_epsilon _ c
      rw [h] at this
      specialize this (b1, true) (by simp)
      simp at this
    | cons head tail => simp [to_horizontal_edge_no_epsilon] at h
  | cons head tail ih =>
    cases d with
    | nil =>
      simp only [to_horizontal_edge_no_epsilon_nil, List.nil_append] at h
      have := @is_false_to_vertical_edge_no_epsilon _ c
      rw [h] at this
      specialize this (b1, true) (by simp)
      simp at this
    | cons head2 tail2 =>
      apply @ih tail2
      simp only [to_horizontal_edge_no_epsilon_cons, List.cons_append, List.append_assoc,
        List.nil_append, List.cons.injEq] at h
      simp [h.2]

theorem not_false_true_infix_horizontal_vertical_edge
    (h : to_horizontal_edge d ++ to_vertical_edge c = k ++ [(a1, false), (b1, true)] ++ l) : False := by
  induction k generalizing d with
  | nil =>
    rcases to_horizontal_edge_eq_cons d with ⟨w, w2, hw⟩
    grind
  | cons head tail ih =>
    rcases to_horizontal_edge_options d with h1 | h2
    · rcases h1 with ⟨a3, h3⟩
      rw [h3] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at h
      have : SignedList.is_false (tail ++ (a1, false) :: (b1, true) :: l) := by
        rw [← h.2]
        exact is_false_to_vertical_edge
      specialize this (b1, true)
      simp at this
    grind

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
