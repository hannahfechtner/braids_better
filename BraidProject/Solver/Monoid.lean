import BraidProject.PartialGrid.Bounded
import BraidProject.PartialGrid.Build
import BraidProject.SemiThueReversing
import BraidProject.Solver.FindOpenPair

namespace Braid

open Relations

private theorem SemiThueDataDerivation.reversing.length_le_ab_len_non_nil_inputs
    (h : SemiThueDataDerivation reversing
      (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
    (ha : a.length > 0) (hb : b.length > 0) :
    SemiThueDataDerivation.length reversing.length h ≤ ab_len a b := by
  rcases PartialGrid.of_SemiThueData_reversing (SemiThueDataDerivation.toSemiThueData h) ha hb
    with ⟨c, d, e, h1, hl⟩
  unfold reversing.length
  rw [← SemiThueDataDerivation.toSemiThueData_length, hl.1.1]
  exact PartialGrid.length_le_grid_length _ _ rfl rfl

theorem SemiThueDataDerivation.reversing.length_le_ab_len
    (h : SemiThueDataDerivation reversing
      (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c) :
    SemiThueDataDerivation.length reversing.length h ≤ ab_len a b := by
  match a with
  | [] =>
    rw [length_zero_of_SemiThueDataDerivation_reversing_true h]
    · simp
    rw [to_vertical_edge_no_epsilon_nil, List.nil_append]
    exact is_true_to_horizontal_edge_no_epsilon
  | a1 :: a2 =>
  match b with
  | [] =>
    rw [length_zero_of_SemiThueDataDerivation_reversing_false h]
    · simp
    rw [to_horizontal_edge_no_epsilon_nil, List.append_nil]
    exact is_false_to_vertical_edge_no_epsilon
  | b1 :: b2 => apply SemiThueDataDerivation.reversing.length_le_ab_len_non_nil_inputs h (by simp) (by simp)

abbrev triangle (a b : List ℕ) : Type := (c : List (ℕ × Bool)) ×
  (SemiThueDataDerivation reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)

open Braid

namespace Triangle

noncomputable def length (a : triangle a1 a2) : ℕ := ab_len a1 a2 - (SemiThueDataDerivation.length reversing.length a.2)

end Triangle

open Triangle

def reverse_triangle {a1 a2} (a : triangle a1 a2) :
    triangle a1 a2 :=
  match hb' : FindOpenPair a.1 with
  | none => a
  | some (c, d, e) =>
    match hd : d.1.dist d.2 with
    | 0 => reverse_triangle ⟨c ++ [] ++ e,
        by
          have := a.2
          rw [FindOpenPair.spec hb'] at this
          apply SemiThueDataDerivation.step this (reversing.basic hd)⟩
    | 1 => reverse_triangle ⟨(c ++ [(d.2, true), (d.1, true), (d.2, false), (d.1, false)] ++ e),
        by
          have := a.2
          rw [FindOpenPair.spec hb'] at this
          apply SemiThueDataDerivation.step this (reversing.close hd)⟩
    | Nat.succ (Nat.succ n) => reverse_triangle ⟨(c ++ [(d.2, true), (d.1, false)] ++ e),
        by
          have := a.2
          rw [FindOpenPair.spec hb'] at this
          apply SemiThueDataDerivation.step this (reversing.apart (by omega))⟩
    termination_by length a
    decreasing_by
    all_goals
      apply (tsub_lt_tsub_iff_left_of_le_of_le (SemiThueDataDerivation.reversing.length_le_ab_len _)
        (SemiThueDataDerivation.reversing.length_le_ab_len _)).mpr
      rcases a with ⟨a3, a4⟩
      rcases FindOpenPair.spec hb' with ⟨b1, b2, b3⟩
      simp [SemiThueDataDerivation.length, reversing.length]

theorem reverse_triangle_FindOpenPair_none {a1 a2}
    (a : triangle a1 a2) : FindOpenPair (reverse_triangle a).1= none := by
  induction ha : length a using Nat.strongRecOn generalizing a
  rw [reverse_triangle]
  split
  · assumption
  split
  · rename_i ih l m o p hd
    apply @ih (length ⟨l ++ [] ++ o, by
          have := a.2
          rw [FindOpenPair.spec p] at this
          apply SemiThueDataDerivation.step this (reversing.basic hd)⟩)
    rw [← ha]
    rcases a with ⟨a3, a4⟩
    rcases FindOpenPair.spec p with ⟨b1, b2, b3⟩
    apply (tsub_lt_tsub_iff_left_of_le_of_le (SemiThueDataDerivation.reversing.length_le_ab_len _)
      (SemiThueDataDerivation.reversing.length_le_ab_len _)).mpr
    · simp [SemiThueDataDerivation.length, reversing.length]
    rfl
  · rename_i ih m n o p hd
    apply @ih (length ⟨(m ++ [(n.2, true), (n.1, true), (n.2, false), (n.1, false)] ++ o), by
          have := a.2
          rw [FindOpenPair.spec p] at this
          apply SemiThueDataDerivation.step this (reversing.close hd)⟩)
    rcases a with ⟨a3, a4⟩
    rcases FindOpenPair.spec p with ⟨b1, b2, b3⟩
    rw [← ha]
    apply (tsub_lt_tsub_iff_left_of_le_of_le (SemiThueDataDerivation.reversing.length_le_ab_len _)
      (SemiThueDataDerivation.reversing.length_le_ab_len _)).mpr
    · simp [SemiThueDataDerivation.length, reversing.length]
    rfl
  rename_i ih l m n o p hd
  apply @ih (length ⟨(l ++ [(m.2, true), (m.1, false)] ++ n), by
          have := a.2
          rw [FindOpenPair.spec o] at this
          apply SemiThueDataDerivation.step this (reversing.apart (by omega))⟩)
  rw [← ha]
  apply (tsub_lt_tsub_iff_left_of_le_of_le (SemiThueDataDerivation.reversing.length_le_ab_len _) (SemiThueDataDerivation.reversing.length_le_ab_len _)).mpr
  rcases a with ⟨a3, a4⟩
  rcases FindOpenPair.spec o with ⟨b1, b2, b3⟩
  · simp [SemiThueDataDerivation.length, reversing.length]
  rfl

open SignedList

def reverse_pair (a b) :=
  reverse_triangle ⟨to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b, SemiThueDataDerivation.refl ⟩

def reverse_pair_PosNegData (a b) :
    SignedList.PosNegData (reverse_pair a b).1 :=
  SignedList.PosNegData_of_FindOpenPair_none
    (reverse_triangle_FindOpenPair_none ⟨to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b, SemiThueDataDerivation.refl ⟩)

def reverse_pair_spec : SemiThueDataDerivation reversing
    (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) (reverse_pair a b).1 := (reverse_pair a b).2

def monoid_solver (a b : List ℕ) : Bool := (@reverse_pair a b).1 = []
