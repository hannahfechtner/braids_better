import BraidProject.SemiThue_C
import BraidProject.Relations
import BraidProject.TrueFalse_C
import BraidProject.Irreducibility

namespace Braid

def concatenate_reduction (a : Option ℕ × Bool) (L : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
  match L with
  | (none, true) :: tail =>
    match a with
    | (_, true) => a :: L
    | (_, false) => (none, true) :: concatenate_reduction a tail
  | (some b, true) :: tail =>
    match a with
    | (none, false) => (some b, true) :: concatenate_reduction a tail
    | (_, _) => a :: L
  | _ => a :: L

@[simp]
theorem concatenate_reduction_nil : concatenate_reduction a [] = [a] := rfl

@[simp]
theorem concatenate_reduction_none_true : concatenate_reduction (none, true) L = (none, true) :: L := by
  induction L
  · rfl
  conv => lhs; unfold concatenate_reduction
  split
  all_goals aesop

@[simp]
theorem concatenate_reduction_to_none_false : concatenate_reduction a ((none, false) :: tail) = a :: ((none, false) :: tail) := by rfl

@[simp]
theorem concatenate_reduction_some_some : concatenate_reduction (some a1, b1) ((some a2, b2) :: tail) = (some a1, b1) :: (some a2, b2) :: tail := by
  unfold concatenate_reduction
  split
  all_goals aesop

@[simp]
theorem concatenate_reduction_none_false_end : concatenate_reduction a (L ++ [(none, false)]) =
    concatenate_reduction a L ++ [(none, false)] := by
  have : ∀ t a L, L.length = t → concatenate_reduction a (L ++ [(none, false)]) =
      concatenate_reduction a L ++ [(none, false)] := by
    intro t
    induction t with
    | zero =>
      intro a L len
      simp [List.length_eq_zero_iff.mp len]
    | succ n ih =>
      intro a L len
      match a with
      | (none, true) => simp
      | (none, false) =>
        match L with
        | [] => simp
        | (none, true) :: tail =>
          simp only [List.cons_append, concatenate_reduction, List.cons.injEq, true_and]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at len
          exact ih _ _ len
        | (none, false) :: tail =>
          simp [concatenate_reduction]
        | (some c, true) :: tail1 =>
          simp only [List.cons_append, concatenate_reduction, List.cons.injEq, true_and]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at len
          exact ih _ _ len
        | (some c, false) :: tail1 =>
          simp [concatenate_reduction]
      | (some b, true) =>
        match L with
        | [] => simp
        | (none, true) :: tail => simp [concatenate_reduction]
        | (none, false) :: tail => simp [concatenate_reduction]
        | (some c, true) :: tail1 => simp [concatenate_reduction]
        | (some c, false) :: tail1 => simp [concatenate_reduction]
      | (some b, false) =>
        match L with
        | [] => simp
        | (none, true) :: tail =>
          simp only [List.cons_append, concatenate_reduction, List.cons.injEq, true_and]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at len
          exact ih _ _ len
        | (none, false) :: tail => simp [concatenate_reduction]
        | (some c, true) :: tail1 => simp [concatenate_reduction]
        | (some c, false) :: tail1 => simp [concatenate_reduction]
  exact this _ _ _ rfl

theorem concatenate_reduction_length (h : L.length = n) : (concatenate_reduction a L).length = n + 1 := by
  induction L generalizing n with
  | nil => simp [h]
  | cons head tail ih =>
  simp only [List.length_cons] at h
  specialize @ih (tail.length) rfl
  match a with
  | (none, true) =>
    simp [concatenate_reduction_none_true, h]
  | (none, false) =>
    match head with
    | (none, true) => simp [ih, h, concatenate_reduction]
    | (none, false) => simp [h]
    | (some c, true) => simp [concatenate_reduction, ih, h]
    | (some c, false) => simp [concatenate_reduction, h]
  | (some a, true) =>
    match head with
    | (none, true) => simp [h, concatenate_reduction]
    | (none, false) => simp [h]
    | (some c, true) => simp [concatenate_reduction, h]
    | (some c, false) => simp [concatenate_reduction, h]
  | (some a, false) =>
      match head with
    | (none, true) => simp [ih, h, concatenate_reduction]
    | (none, false) => simp [h]
    | (some c, true) => simp [concatenate_reduction, h]
    | (some c, false) => simp [concatenate_reduction, h]

noncomputable def concatenate_reduction_equiv_grid_style : SemiThue grid_style (a :: L) (concatenate_reduction a L) := by
  have H : ∀ t L a, L.length ≤ t → SemiThue grid_style (a :: L) (concatenate_reduction a L) := by
    intro t
    induction t
    · intro L a len
      simp only [nonpos_iff_eq_zero, List.length_eq_zero_iff] at len
      rw [len]
      exact SemiThue.refl
    rename_i n ih
    intro L a len
    match a with
    | (none, true) =>
      simp only [concatenate_reduction_none_true]
      exact SemiThue.refl
    | (none, false) =>
      match L with
      | [] => exact SemiThue.refl
      | (none, true) :: tail =>
        simp only [List.length_cons, add_le_add_iff_right] at len
        exact SemiThue.trans (SemiThue.append_right (SemiThue.of_rel grid_style.empty)) (SemiThue.cons (ih tail _ len))
      | (none, false) :: tail => exact SemiThue.refl
      | (some c, true) :: tail1 =>
        simp only [List.length_cons, add_le_add_iff_right] at len
        specialize ih tail1 (none, false) len
        exact SemiThue.trans (SemiThue.append_right (SemiThue.of_rel (grid_style.up c))) (SemiThue.cons ih)
      | (some c, false) :: tail1 =>
        exact SemiThue.refl
    | (some b, true) =>
      match L with
      | [] => exact SemiThue.refl
      | (none, true) :: tail => exact SemiThue.refl
      | (none, false) :: tail => exact SemiThue.refl
      | (some c, true) :: tail1 => exact SemiThue.refl
      | (some c, false) :: tail1 => exact SemiThue.refl
    | (some b, false) =>
      match L with
      | [] => exact SemiThue.refl
      | (none, true) :: tail =>
        simp only [List.length_cons, add_le_add_iff_right] at len
        specialize ih tail (some b, false) len
        exact SemiThue.trans (SemiThue.append_right (SemiThue.of_rel (grid_style.over b))) (SemiThue.cons ih)
      | (none, false) :: tail => exact SemiThue.refl
      | (some c, true) :: tail1 => exact SemiThue.refl
      | (some c, false) :: tail1 => exact SemiThue.refl
  exact H L.length _ _ (by simp)

noncomputable def concatenate_reduction_equiv_grid_style_trivial : SemiThue grid_style_trivial (a :: L) (concatenate_reduction a L) := by
  have H : ∀ t L a, L.length ≤ t → SemiThue grid_style_trivial (a :: L) (concatenate_reduction a L) := by
    intro t
    induction t
    · intro L a len
      simp only [nonpos_iff_eq_zero, List.length_eq_zero_iff] at len
      rw [len]
      exact SemiThue.refl
    rename_i n ih
    intro L a len
    match a with
    | (none, true) =>
      simp only [concatenate_reduction_none_true]
      exact SemiThue.refl
    | (none, false) =>
      match L with
      | [] => exact SemiThue.refl
      | (none, true) :: tail =>
        simp only [List.length_cons, add_le_add_iff_right] at len
        exact SemiThue.trans (SemiThue.append_right (SemiThue.of_rel grid_style_trivial.empty)) (SemiThue.cons (ih tail _ len))
      | (none, false) :: tail => exact SemiThue.refl
      | (some c, true) :: tail1 =>
        simp only [List.length_cons, add_le_add_iff_right] at len
        specialize ih tail1 (none, false) len
        exact SemiThue.trans (SemiThue.append_right (SemiThue.of_rel (grid_style_trivial.up c))) (SemiThue.cons ih)
      | (some c, false) :: tail1 =>
        exact SemiThue.refl
    | (some b, true) =>
      match L with
      | [] => exact SemiThue.refl
      | (none, true) :: tail => exact SemiThue.refl
      | (none, false) :: tail => exact SemiThue.refl
      | (some c, true) :: tail1 => exact SemiThue.refl
      | (some c, false) :: tail1 => exact SemiThue.refl
    | (some b, false) =>
      match L with
      | [] => exact SemiThue.refl
      | (none, true) :: tail =>
        simp only [List.length_cons, add_le_add_iff_right] at len
        specialize ih tail (some b, false) len
        exact SemiThue.trans (SemiThue.append_right (SemiThue.of_rel (grid_style_trivial.over b))) (SemiThue.cons ih)
      | (none, false) :: tail => exact SemiThue.refl
      | (some c, true) :: tail1 => exact SemiThue.refl
      | (some c, false) :: tail1 => exact SemiThue.refl
  exact H L.length _ _ (by simp)

open SignedOptionList

@[simp]
theorem toSignedList_concatenate_reduction_none : toSignedList (concatenate_reduction (none, b) L) = toSignedList L := by
  induction L
  · simp [toSignedList]
  rename_i head tail ih
  match head with
  | (none, true) =>
    cases b
    all_goals
    simp [concatenate_reduction, toSignedList, ih]
  | (none, false) => simp [concatenate_reduction, toSignedList]
  | (some a, true) =>
    cases b
    all_goals
    simp [concatenate_reduction, toSignedList, ih]
  | (some a, false) => simp [concatenate_reduction, toSignedList]

@[simp]
theorem toSignedList_concatenate_reduction_some : toSignedList (concatenate_reduction (some a, b) L) = (a, b) :: toSignedList L := by
  induction L
  · simp [toSignedList]
  rename_i head tail ih
  match head with
  | (none, true) =>
    cases b
    all_goals
    simp [concatenate_reduction, toSignedList, ih]
  | (none, false) => simp [concatenate_reduction, toSignedList]
  | (some a, true) =>
    cases b
    all_goals
    simp [concatenate_reduction, toSignedList]
  | (some a, false) => simp [concatenate_reduction, toSignedList]

def move_ones (L : List (Option ℕ × Bool)) :=
  match L with
  | [] => []
  | head :: tail => concatenate_reduction head (move_ones tail)

@[simp]
theorem moves_ones_nil : move_ones [] = [] := rfl

@[simp]
theorem move_ones_singleton : move_ones [a] = [a] := by
  unfold move_ones
  unfold concatenate_reduction
  simp

@[simp]
theorem move_ones_length : (move_ones L).length = L.length := by
  induction L
  · rfl
  unfold move_ones
  rename_i ih
  simp [concatenate_reduction_length, ih]

@[simp]
theorem move_ones_none_true : move_ones ((none, true)::a) = (none, true) :: move_ones a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    conv => lhs; unfold move_ones
    simp

@[simp]
theorem move_ones_none_false_end : move_ones (a ++ [(none, false)]) = move_ones a ++ [(none, false)] := by
  induction a
  · simp
  simp [move_ones]
  rename_i ih
  rw [ih, concatenate_reduction_none_false_end]

noncomputable def equiv_move_ones : SemiThue grid_style L (move_ones L) := by
  induction L
  · exact SemiThue.refl
  rename_i head tail ih
  exact SemiThue.trans (SemiThue.cons ih) (concatenate_reduction_equiv_grid_style)

noncomputable def equiv_move_ones_grid_style_trivial : SemiThue grid_style_trivial L (move_ones L) := by
  induction L
  · exact SemiThue.refl
  rename_i head tail ih
  exact SemiThue.trans (SemiThue.cons ih) (concatenate_reduction_equiv_grid_style_trivial)

theorem toSignedList_move_ones : toSignedList (move_ones L) = toSignedList L := by
  induction L
  · simp
  rename_i head tail ih
  match head with
  | (none, true) => simp [move_ones, toSignedList, ih]
  | (none, false) =>
    simp [toSignedList, move_ones, ih]
  | (some a, true) => simp [move_ones, toSignedList, ih]
  | (some a, false) => simp [move_ones, toSignedList, ih]

def concatenate_reduction_irreducible (h : irreducible L) : irreducible (concatenate_reduction a L) := by
  have H : ∀ t a L, L.length = t → irreducible L → irreducible (concatenate_reduction a L) := by
    intro t
    induction t with
    | zero =>
      intro a L len h
      simp only [List.length_eq_zero_iff.mp len, concatenate_reduction_nil]
      exact irreducible_singleton
    | succ n ih =>
      intro a L m irr
      match a with
      | (none, true) =>
        simp only [concatenate_reduction_none_true]
        exact irreducible_cons_true irr
      | (none, false) =>
        match hl : L with
        | [] =>
          simp only [concatenate_reduction_nil]
          exact irreducible_singleton
        | (none, true) :: tail =>
          simp only [concatenate_reduction]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at m
          exact irreducible_cons_true (ih _ _ m (irreducible_tail irr))
        | (none, false) :: tail =>
          simp only [concatenate_reduction]
          apply irreducible_cons_cons_bool_eq irr
        | (some b, true) :: tail =>
          simp only [concatenate_reduction]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at m
          exact irreducible_cons_true (ih _ _ m (irreducible_tail irr))
        | (some b, false) :: tail =>
          simp only [concatenate_reduction]
          apply irreducible_cons_cons_bool_eq irr
      | (some b, true) =>
        match hl : L with
        | [] =>
          simp only [concatenate_reduction_nil]
          exact irreducible_singleton
        | (none, true) :: tail =>
          simp only [concatenate_reduction]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at m
          apply irreducible_cons_cons_bool_eq
          apply irreducible_cons_true
          exact irreducible_tail irr
        | (none, false) :: tail =>
          simp only [concatenate_reduction]
          apply irreducible_cons_true irr
        | (some b, true) :: tail =>
          simp only [concatenate_reduction]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at m
          apply irreducible_cons_true irr
        | (some b, false) :: tail =>
          simp only [concatenate_reduction]
          apply irreducible_cons_true irr
      | (some c, false) =>
        match hl : L with
        | [] =>
          simp only [concatenate_reduction_nil]
          exact irreducible_singleton
        | (none, true) :: tail =>
          simp only [concatenate_reduction]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at m
          exact irreducible_cons_true (ih _ _ m (irreducible_tail irr))
        | (none, false) :: tail =>
          simp only [concatenate_reduction]
          apply irreducible_cons_cons_bool_eq irr
        | (some b, true) :: tail =>
          simp only [concatenate_reduction]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at m
          apply irreducible_cons_some_cons_some irr
        | (some b, false) :: tail =>
          simp only [concatenate_reduction]
          apply irreducible_cons_cons_bool_eq irr
  exact H _ _ _ rfl h

def move_ones_irreducible : irreducible (move_ones L) := by
  induction L
  · simp
    exact irreducible_nil
  rename_i head tail ih
  unfold move_ones
  exact concatenate_reduction_irreducible ih

theorem concatenate_reduction_of_irreducible {head : Option ℕ × Bool} {tail : List (Option ℕ × Bool)} (h : irreducible (head :: tail)) : concatenate_reduction head tail = head :: tail := by
  match head with
  | (none, true) => simp
  | (none, false) =>
    match hl : tail with
    | [] => simp
    | (none, true) :: tail =>
      simp only [concatenate_reduction]
      apply Empty.elim
      apply (h 0).2.2
      use [], tail
      simp only [List.nil_append, List.cons_append]
      exact {down := trivial}
    | (none, false) :: tail => simp only [concatenate_reduction]
    | (some b, true) :: tail =>
      simp only [concatenate_reduction]
      apply Empty.elim
      apply (h b).2.1
      use [], tail
      simp only [List.nil_append, List.cons_append]
      exact {down := trivial}
    | (some b, false) :: tail =>
      simp only [concatenate_reduction]
  | (some b, true) =>
    match hl : tail with
    | [] => simp
    | (none, true) :: tail => simp only [concatenate_reduction]
    | (none, false) :: tail => simp only [concatenate_reduction]
    | (some b, true) :: tail => simp only [concatenate_reduction]
    | (some b, false) :: tail => simp only [concatenate_reduction]
  | (some c, false) =>
    match hl : tail with
    | [] => simp
    | (none, true) :: tail =>
      simp only [concatenate_reduction]
      apply Empty.elim
      apply (h c).1
      use [], tail
      simp only [List.nil_append, List.cons_append]
      exact {down := trivial}
    | (none, false) :: tail => simp only [concatenate_reduction]
    | (some b, true) :: tail => simp only [concatenate_reduction]
    | (some b, false) :: tail => simp only [concatenate_reduction]

theorem move_ones_of_irreducible (h : irreducible L) : move_ones L = L := by
  induction L
  · simp
  rename_i head tail ih
  simp [move_ones]
  specialize ih (irreducible_tail h)
  rw [ih, concatenate_reduction_of_irreducible h]

theorem move_ones_move_ones : move_ones (move_ones L) = move_ones L :=
  move_ones_of_irreducible move_ones_irreducible
