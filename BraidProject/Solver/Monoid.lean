import BraidProject.PartialGrid.Bounded
import BraidProject.PartialGrid.Build
import BraidProject.Solver.FindOpenPair
import BraidProject.GridData_length

namespace Braid

theorem st_smaller_than_g (h : SemiThueDataDerivation reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)
  (ha : a.length > 0) (hb : b.length > 0):
    ab_len a b ≥ SemiThueDataDerivation.reversing.length h := by
  have := SemiThueDataDerivation.reversing.toSemiThueData_with_length h
  rcases PartialGrid.of_SemiThueData_reversing this.1 ha hb with ⟨c, d, e, h1, hl⟩
  rw [this.2.1, hl.1.1]
  exact straight_pg_sm_g _ _ rfl rfl

abbrev triangle (a b : List ℕ) : Type := (c : List (ℕ × Bool)) ×
  (SemiThueDataDerivation reversing (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) c)

open Braid

namespace Triangle

noncomputable def length (a : triangle a1 a2) : ℕ := ab_len a1 a2 - (SemiThueDataDerivation.reversing.length a.2)

end Triangle

open Triangle

def reverse_triangle {a1 a2} (ha1 : a1.length > 0) (ha2 : a2.length > 0) (a : triangle a1 a2) :
    triangle a1 a2 :=
  match hb' : FindOpenPair a.1 with
  | none => a
  | some (c, d, e) =>
    match hd : d.1.dist d.2 with
    | 0 => reverse_triangle ha1 ha2 ⟨c ++ [] ++ e,
        by
          have := a.2
          rw [FindOpenPair.spec hb'] at this
          apply SemiThueDataDerivation.step this (reversing.basic hd)⟩
    | 1 => reverse_triangle ha1 ha2 ⟨(c ++ [(d.2, true), (d.1, true), (d.2, false), (d.1, false)] ++ e),
        by
          have := a.2
          rw [FindOpenPair.spec hb'] at this
          apply SemiThueDataDerivation.step this (reversing.close hd)⟩
    | Nat.succ (Nat.succ n) => reverse_triangle ha1 ha2 ⟨(c ++ [(d.2, true), (d.1, false)] ++ e),
        by
          have := a.2
          rw [FindOpenPair.spec hb'] at this
          apply SemiThueDataDerivation.step this (reversing.apart (by omega))⟩
    termination_by length a
    decreasing_by
    all_goals
      apply (tsub_lt_tsub_iff_left_of_le_of_le (st_smaller_than_g _ ha1 ha2)
        (st_smaller_than_g _ ha1 ha2)).mpr
      rcases a with ⟨a3, a4⟩
      rcases FindOpenPair.spec hb' with ⟨b1, b2, b3⟩
      simp [SemiThueDataDerivation.reversing.length]

theorem reverse_triangle_FindOpenPair_none {a1 a2} {ha1 : a1.length > 0} {ha2 : a2.length > 0}
    (a : triangle a1 a2) : FindOpenPair (reverse_triangle ha1 ha2 a).1= none := by
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
    apply (tsub_lt_tsub_iff_left_of_le_of_le (st_smaller_than_g _ ha1 ha2) (st_smaller_than_g _ ha1 ha2)).mpr
    · simp [SemiThueDataDerivation.reversing.length]
    rfl
  · rename_i ih m n o p hd
    apply @ih (length ⟨(m ++ [(n.2, true), (n.1, true), (n.2, false), (n.1, false)] ++ o), by
          have := a.2
          rw [FindOpenPair.spec p] at this
          apply SemiThueDataDerivation.step this (reversing.close hd)⟩)
    rcases a with ⟨a3, a4⟩
    rcases FindOpenPair.spec p with ⟨b1, b2, b3⟩
    rw [← ha]
    apply (tsub_lt_tsub_iff_left_of_le_of_le (st_smaller_than_g _ ha1 ha2) (st_smaller_than_g _ ha1 ha2)).mpr
    simp [SemiThueDataDerivation.reversing.length]
    rfl
  rename_i ih l m n o p hd
  apply @ih (length ⟨(l ++ [(m.2, true), (m.1, false)] ++ n), by
          have := a.2
          rw [FindOpenPair.spec o] at this
          apply SemiThueDataDerivation.step this (reversing.apart (by omega))⟩)
  rw [← ha]
  apply (tsub_lt_tsub_iff_left_of_le_of_le (st_smaller_than_g _ ha1 ha2) (st_smaller_than_g _ ha1 ha2)).mpr
  rcases a with ⟨a3, a4⟩
  rcases FindOpenPair.spec o with ⟨b1, b2, b3⟩
  simp [SemiThueDataDerivation.reversing.length]
  rfl

open SignedList

def reverse_pair (a b) (ha : List.length a > 0) (hb : List.length b > 0) :=
  reverse_triangle ha hb ⟨to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b, SemiThueDataDerivation.refl ⟩

def reverse_pair_PosNegData (a b) (ha : List.length a > 0) (hb : List.length b > 0) :
    SignedList.PosNegData (reverse_pair a b ha hb).1 :=
  SignedList.PosNegData_of_FindOpenPair_none
    (reverse_triangle_FindOpenPair_none ⟨to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b, SemiThueDataDerivation.refl ⟩)

def reverse_pair_spec (ha : List.length a > 0) (hb : List.length b > 0)  : SemiThueDataDerivation reversing
    (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) (reverse_pair a b ha hb).1 := (reverse_pair a b ha hb).2

def monoid_solver (a b : List ℕ) : Bool :=
  match a with
  | [] =>
    match b with
    | [] => true
    | b1 :: b2 => false
  | a1 :: a2 =>
    match b with
    | [] => false
    | b1 :: b2 => (@reverse_pair (a1 :: a2) (b1 :: b2) (by simp) (by simp)).1 = []
