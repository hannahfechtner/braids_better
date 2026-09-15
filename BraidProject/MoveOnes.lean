import BraidProject.DataCarrying.SemiThue
import BraidProject.Irreducibility
import BraidProject.Relations

namespace Braid

open Relations

def concatenate_reduction (a : Option ℕ × Bool) (L : List (Option ℕ × Bool)) :
    List (Option ℕ × Bool) :=
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
theorem concatenate_reduction_true :
  concatenate_reduction (a, true) L = (a, true) :: L := by
  induction L
  · rfl
  conv => lhs; unfold concatenate_reduction
  split
  all_goals aesop

@[simp]
theorem concatenate_reduction_to_false :
  concatenate_reduction a ((b, false) :: tail) = a :: ((b, false) :: tail) := by
  cases b with
  | none => rfl
  | some val => simp [concatenate_reduction]

@[simp]
theorem concatenate_reduction_some_some :
    concatenate_reduction (some a1, b1) ((some a2, b2) :: tail) =
    (some a1, b1) :: (some a2, b2) :: tail := by
  unfold concatenate_reduction
  split
  all_goals aesop

@[simp]
theorem concatenate_reduction_none_false_to_true :
    concatenate_reduction (none, false) ((a, true) :: tail) =
    (a, true) :: (concatenate_reduction (none, false) tail) := by
   cases a with
   | none => rfl
   | some val => rfl

@[simp]
theorem concatenate_reduction_false_end : concatenate_reduction a (L ++ [(b, false)]) =
    concatenate_reduction a L ++ [(b, false)] := by
  have : ∀ t a L, L.length = t → concatenate_reduction a (L ++ [(b, false)]) =
      concatenate_reduction a L ++ [(b, false)] := by
    intro t
    induction t with
    | zero =>
      intro a L len
      simp [List.length_eq_zero_iff.mp len]
    | succ n ih =>
      intro a L len
      match a with
      | (_, true) => simp
      | (none, false) =>
        match L with
        | [] => simp [concatenate_reduction]
        | (_, true) :: tail =>
          simp only [List.cons_append, concatenate_reduction_none_false_to_true, List.cons.injEq,
            true_and]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at len
          exact ih _ _ len
        | (none, false) :: tail =>
          simp [concatenate_reduction]
        | (some c, false) :: tail1 =>
          simp [concatenate_reduction]
      | (some b, false) =>
        match L with
        | [] => simp [concatenate_reduction]
        | (none, true) :: tail =>
          simp only [List.cons_append, concatenate_reduction, List.cons.injEq, true_and]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at len
          exact ih _ _ len
        | (_, false) :: tail => simp
        | (some c, true) :: tail1 => simp [concatenate_reduction]
  exact this _ _ _ rfl

noncomputable def PosNegData_concatenate_reduction (h : SignedList.PosNegData b)
    (hr : SignedList.PosNegData (SignedOptionList.toSignedList (a :: b))) :
    SignedList.PosNegData (concatenate_reduction a b) := by
  induction hb : b.length generalizing a b with
  | zero =>
    rw [List.eq_nil_iff_length_eq_zero.mpr hb]
    simp [concatenate_reduction]; exact SignedList.PosNegData.singleton
  | succ n ih =>
    match b with
    | [] => simp at hb
    | (e, false) :: tail =>
      simp only [concatenate_reduction_to_false]
      rcases h with ⟨c, d, c_true, d_false, cd_is⟩
      have H : c = [] := by
        match c with
        | [] => rfl
        | c1 :: c2 =>
          simp at cd_is
          rw [← cd_is.1] at c_true
          specialize c_true (e, false) (by simp)
          simp at c_true
      rw [H, List.nil_append] at cd_is
      match a with
      | (a1, false) =>
        use [], (a1, false) :: d
        rw [cd_is, List.nil_append]
        exact ⟨⟨SignedList.is_true_nil, SignedList.is_false_cons d d_false, rfl⟩⟩
      | (a1, true) =>
        use [(a1, true)], d
        rw [cd_is]
        exact ⟨⟨SignedList.is_true_cons [] SignedList.is_true_nil, d_false, rfl⟩⟩
    | (none, true) :: tail =>
      match a with
      | (a1, true) =>
        simp only [concatenate_reduction]
        rcases h with ⟨c, d, c_true, d_false, cd_is⟩
        use (a1, true) :: c, d
        rw [cd_is]
        exact ⟨⟨SignedList.is_true_cons c c_true, d_false, rfl⟩⟩
      | (a1, false) =>
        simp only [concatenate_reduction]
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hb
        rw [SignedOptionList.toSignedList_cons, SignedOptionList.toSignedList, ← SignedOptionList.toSignedList_append] at hr
        specialize @ih tail (a1, false) (SignedList.PosNegData.tail h) hr hb
        rcases ih with ⟨c, d, c_true, d_false, cd_is⟩
        use (none, true) :: c, d
        rw [cd_is]
        exact ⟨⟨SignedList.is_true_cons c c_true, d_false, rfl⟩⟩
    | (some a1, true) :: tail =>
      match a with
      | (e, true) =>
        simp only [concatenate_reduction]
        rcases h with ⟨c, d, c_true, d_false, hcd⟩
        use (e, true) :: c, d
        rw [hcd]
        exact ⟨⟨SignedList.is_true_cons c c_true, d_false, rfl⟩⟩
      | (none, false) =>
        simp only [concatenate_reduction]
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hb
        rw [SignedOptionList.toSignedList_cons, SignedOptionList.toSignedList, SignedOptionList.toSignedList, SignedOptionList.toSignedList_nil, List.nil_append] at hr
        specialize @ih tail (none, false) (SignedList.PosNegData.tail h)
          (by rw [SignedOptionList.toSignedList_cons, SignedOptionList.toSignedList, SignedOptionList.toSignedList_nil,
          List.nil_append]; exact SignedList.PosNegData.tail hr) hb
        rcases ih with ⟨c, d, c_true, d_false, hcd⟩
        use (some a1, true) :: c, d
        rw [hcd]
        exact ⟨⟨SignedList.is_true_cons c c_true, d_false, rfl⟩⟩
      | (some a2, false) =>
        simp only [SignedOptionList.toSignedList] at hr
        rcases hr with ⟨c, d, c_true, d_false, hcd⟩
        have H : c = [] := by
          match c with
          | [] => rfl
          | c1 :: c2 =>
            simp at hcd
            rw [← hcd.1] at c_true
            specialize c_true (a2, false) (by simp)
            simp at c_true
        rw [H, List.nil_append] at hcd
        rw [← hcd] at d_false
        specialize d_false (a1, true) (by simp)
        simp at d_false

theorem concatenate_reduction_length (h : L.length = n) :
    (concatenate_reduction a L).length = n + 1 := by
  induction L generalizing n with
  | nil => simp [h]
  | cons head tail ih =>
  simp only [List.length_cons] at h
  specialize @ih (tail.length) rfl
  match a with
  | (_, true) =>
    simp [h]
  | (none, false) =>
    match head with
    | (_, true) => simp [ih, h]
    | (_, false) => simp [h]
  | (some a, false) =>
      match head with
    | (none, true) => simp [ih, h, concatenate_reduction]
    | (_, false) => simp [h]
    | (some c, true) => simp [concatenate_reduction, h]

noncomputable def concatenate_reduction_equiv_grid_style_trivial :
    SemiThueData grid_style_trivial (a :: L) (concatenate_reduction a L) := by
  have H : ∀ t L a, L.length ≤ t →
      SemiThueData grid_style_trivial (a :: L) (concatenate_reduction a L) := by
    intro t
    induction t
    · intro L a len
      simp only [nonpos_iff_eq_zero, List.length_eq_zero_iff] at len
      rw [len]
      exact SemiThueData.refl
    rename_i n ih
    intro L a len
    match a with
    | (_, true) =>
      simp only [concatenate_reduction_true]
      exact SemiThueData.refl
    | (none, false) =>
      match L with
      | [] => exact SemiThueData.refl
      | (none, true) :: tail =>
        simp only [List.length_cons, add_le_add_iff_right] at len
        exact SemiThueData.trans
          (SemiThueData.append_right (SemiThueData.of_rel grid_style_trivial.empty))
          (SemiThueData.cons (ih tail _ len))
      | (_, false) :: tail => simp; exact SemiThueData.refl
      | (some c, true) :: tail1 =>
        simp only [List.length_cons, add_le_add_iff_right] at len
        specialize ih tail1 (none, false) len
        exact SemiThueData.trans
          (SemiThueData.append_right (SemiThueData.of_rel (grid_style_trivial.up c)))
          (SemiThueData.cons ih)
    | (some b, false) =>
      match L with
      | [] => exact SemiThueData.refl
      | (none, true) :: tail =>
        simp only [List.length_cons, add_le_add_iff_right] at len
        specialize ih tail (some b, false) len
        exact SemiThueData.trans
          (SemiThueData.append_right (SemiThueData.of_rel (grid_style_trivial.over b)))
          (SemiThueData.cons ih)
      | (_, false) :: tail => simp; exact SemiThueData.refl
      | (some c, true) :: tail1 => exact SemiThueData.refl
  exact H L.length _ _ (by simp)

noncomputable def concatenate_reduction_equiv_grid_style :
    SemiThueData grid_style (a :: L) (concatenate_reduction a L) :=
  SemiThueData.rel_subset (concatenate_reduction_equiv_grid_style_trivial)
    (fun _ _ => grid_style.of_grid_style_trivial)

theorem concatenate_reduction_equiv_grid_style_length :
    SemiThueData.length grid_style.length (@concatenate_reduction_equiv_grid_style a L) = 0 := by
  unfold concatenate_reduction_equiv_grid_style
  rw [← SemiThueData.length_rel_subset (rel₁_length := grid_style_trivial.length)
    (rel₂_length := grid_style.length) _ (fun _ _ => grid_style.of_grid_style_trivial)
    (fun _ _ h1 => by cases h1 <;> rfl)]
  exact SemiThueData.length_eq_zero _ (by simp [grid_style_trivial.length])

open SignedOptionList

@[simp]
theorem toSignedList_concatenate_reduction_none :
    toSignedList (concatenate_reduction (none, b) L) = toSignedList L := by
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
theorem toSignedList_concatenate_reduction_some :
    toSignedList (concatenate_reduction (some a, b) L) = (a, b) :: toSignedList L := by
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
theorem move_ones_true : move_ones ((b, true)::a) = (b, true) :: move_ones a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    conv => lhs; unfold move_ones
    simp

@[simp]
theorem move_ones_none_false_end : move_ones (a ++ [(b, false)]) = move_ones a ++ [(b, false)] := by
  induction a
  · simp
  simp [move_ones]
  rename_i ih
  rw [ih, concatenate_reduction_false_end]

noncomputable def equiv_move_ones : SemiThueData grid_style L (move_ones L) := by
  induction L
  · exact SemiThueData.refl
  rename_i ih
  exact SemiThueData.trans (SemiThueData.cons ih) (concatenate_reduction_equiv_grid_style)

@[simp]
theorem equiv_move_ones_length_zero {b} : SemiThueData.length grid_style.length (@equiv_move_ones b) = 0 := by
  induction b with
  | nil => simp [equiv_move_ones]
  | cons head tail ih =>
    unfold equiv_move_ones
    simp only [SemiThueData.length_trans, Nat.add_eq_zero_iff]
    constructor
    · simp only [SemiThueData.length_cons, ← ih]
      rfl
    exact concatenate_reduction_equiv_grid_style_length

noncomputable def equiv_move_ones_grid_style_trivial : SemiThueData grid_style_trivial L (move_ones L) := by
  induction L
  · exact SemiThueData.refl
  rename_i ih
  exact SemiThueData.trans (SemiThueData.cons ih) (concatenate_reduction_equiv_grid_style_trivial)

theorem toSignedList_move_ones : toSignedList (move_ones L) = toSignedList L := by
  induction L
  · simp
  rename_i head tail ih
  match head with
  | (_, true) =>
    rw [move_ones_true, toSignedList_cons, ih]
    conv => rhs; rw [toSignedList_cons]
  | (none, false) => simp [toSignedList, move_ones, ih]
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
      | (_, true) =>
        simp
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
        | (_, false) :: tail =>
          simp only [concatenate_reduction]
          apply irreducible_cons_cons_bool_eq irr
        | (some b, true) :: tail =>
          simp only [concatenate_reduction]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at m
          exact irreducible_cons_true (ih _ _ m (irreducible_tail irr))
      | (some c, false) =>
        match hl : L with
        | [] =>
          simp only [concatenate_reduction_nil]
          exact irreducible_singleton
        | (none, true) :: tail =>
          simp only [concatenate_reduction]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at m
          exact irreducible_cons_true (ih _ _ m (irreducible_tail irr))
        | (_, false) :: tail =>
          simp only [concatenate_reduction]
          apply irreducible_cons_cons_bool_eq irr
        | (some b, true) :: tail =>
          simp only [concatenate_reduction]
          simp only [List.length_cons, Nat.add_right_cancel_iff] at m
          apply irreducible_cons_some_cons_some irr
  exact H _ _ _ rfl h

def move_ones_irreducible : irreducible (move_ones L) := by
  induction L
  · exact irreducible_nil
  rename_i head tail ih
  exact concatenate_reduction_irreducible ih

theorem concatenate_reduction_of_irreducible {head : Option ℕ × Bool}
    {tail : List (Option ℕ × Bool)} (h : irreducible (head :: tail)) :
    concatenate_reduction head tail = head :: tail := by
  match head with
  | (_, true) => simp
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
    | (_, false) :: tail => simp only [concatenate_reduction]
    | (some b, true) :: tail =>
      simp only [concatenate_reduction]
      apply Empty.elim
      apply (h b).2.1
      use [], tail
      simp only [List.nil_append, List.cons_append]
      exact {down := trivial}
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
    | (_, false) :: tail => simp only [concatenate_reduction]
    | (some b, true) :: tail => simp only [concatenate_reduction]

theorem move_ones_of_irreducible (h : irreducible L) : move_ones L = L := by
  induction L
  · simp
  rename_i head tail ih
  simp [move_ones]
  specialize ih (irreducible_tail h)
  rw [ih, concatenate_reduction_of_irreducible h]

theorem move_ones_move_ones : move_ones (move_ones L) = move_ones L :=
  move_ones_of_irreducible move_ones_irreducible
