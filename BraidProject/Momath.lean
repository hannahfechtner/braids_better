import BraidProject.Solver_G


def solver_helper_list (a : triangle) : List (List (ℕ × Bool)) × List (ℕ × Bool) × List (ℕ × Bool) :=
  match hb': find_it a.2.2.1 with
  | none => by
    have H := in_order_of_find_it_none hb'
    rcases H with ⟨a1, a2, spec⟩
    exact ([a.2.2.1], a1, a2)
  | some (c, d, e) =>
    match hd : d.1.dist d.2 with
    | 0 => ([c ++ ([(d.1, false), (d.2, true)]) ++ e] ++ (solver_helper_list ⟨a.1, ⟨a.2.1, ⟨c ++ [] ++ e,
        ⟨a.2.2.2.1,
        by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.basic hd)⟩⟩⟩⟩).1,
          (solver_helper_list ⟨a.1, ⟨a.2.1, ⟨c ++ [] ++ e,
        ⟨a.2.2.2.1,
        by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.basic hd)⟩⟩⟩⟩).2)
    | 1 => ([c ++ ([(d.1, false), (d.2, true)]) ++ e] ++ (solver_helper_list ⟨a.1, ⟨a.2.1, ⟨(c ++ [(d.2, true), (d.1, true), (d.2, false), (d.1, false)] ++ e),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.close hd)⟩ ⟩⟩⟩).1,
        (solver_helper_list ⟨a.1, ⟨a.2.1, ⟨(c ++ [(d.2, true), (d.1, true), (d.2, false), (d.1, false)] ++ e),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.close hd)⟩ ⟩⟩⟩).2)
    | Nat.succ (Nat.succ n) => ([c ++ ([(d.1, false), (d.2, true)]) ++ e] ++ (solver_helper_list ⟨a.1, ⟨a.2.1, ⟨(c ++ [(d.2, true), (d.1, false)] ++ e),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.apart (by omega))⟩⟩⟩⟩).1, (solver_helper_list ⟨a.1, ⟨a.2.1, ⟨(c ++ [(d.2, true), (d.1, false)] ++ e),
        ⟨ a.2.2.2.1, by
          apply a.2.2.2.2.trans
          rw [find_it_spec hb']
          exact SemiThue.reduction (reversing.apart (by omega))⟩⟩⟩⟩).2)
    termination_by get_n' a
    decreasing_by
    · rcases a with ⟨a1, a2, a3, a4⟩
      simp only
      rcases find_it_spec hb' with ⟨b1, b2, b3⟩
      rcases d with ⟨x, y⟩
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · simp [rw_length_rev]
      · apply st_smaller_than_g
        simp only [gt_iff_lt, a4.1.1.1]
        simp [a4.1.1.2]
      apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    · rcases a with ⟨a1, a2, a3, a4⟩
      rcases find_it_spec hb' with ⟨b1, b2, b3⟩
      rcases d with ⟨x, y⟩
      apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
      · simp [rw_length_rev]
      · apply st_smaller_than_g
        simp [a4.1.1.1]
        simp [a4.1.1.2]
      apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    rcases a with ⟨a1, a2, a3, a4⟩
    rcases find_it_spec hb' with ⟨b1, b2, b3⟩
    rcases d with ⟨x, y⟩
    apply (@tsub_lt_tsub_iff_left_of_le_of_le Nat _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
    · simp [rw_length_rev]
    · apply st_smaller_than_g
      simp [a4.1.1.1]
      simp [a4.1.1.2]
    apply st_smaller_than_g
    simp [a4.1.1.1]
    simp [a4.1.1.2]

#check solver_long

def to_triangle (a b : List ℕ) (ha : List.length a > 0) (hb : List.length b > 0) : triangle :=
  ⟨a, ⟨b, ⟨to_up_plain a ++ to_over_plain b, by simp [to_up_plain, to_over_plain]; exact ⟨⟨ha, hb⟩, by apply SemiThue.refl _ ⟩⟩⟩⟩

-- gives off the list of steps, as well as the true part and the false part of the result
def fraction_form (L : List (ℕ × Bool)) : List (List (ℕ × Bool)) × (List (ℕ × Bool)) × List (ℕ × Bool) :=
  match L with
  | [] => ([], [], [])
  | l1 :: l2 =>
  match hs : separate_first_pair (l1 :: l2) with
  | ([], (b, c)) => by
    -- b is true
    have hc : c.length < (l1 :: l2).length := by
      have H := separate_first_pair_correct (l1 :: l2)
      have c_is : c = (separate_first_pair (l1 :: l2)).2.2 := by simp [hs]
      rw [c_is]
      apply congr_arg List.length at H
      simp only [List.append_assoc, List.length_append, List.length_cons] at H
      rw [List.length_cons, ← H, ← add_assoc]
      refine Nat.lt_add_of_pos_left ?_
      apply separate_first_pair_length ?_
      simp
    use ((List.map (fun entry => b ++ entry) (fraction_form c).1))
    use (b ++ (fraction_form c).2.1), (fraction_form c).2.2
  | (a1::a2, ([], c)) => by
    have hc : c = [] := c_nil_of_separate_no_true hs
    use [a1 :: a2], [], a1 :: a2
  | (a1::a2, (b1::b2, c)) => by
    have H := solver_helper_list (to_triangle (List.map (fun x => x.1) (a1 :: a2).reverse)
      (List.map (fun x => x.1) (b1 :: b2)) (by simp) (by simp))
    have hc : c.length < (l1 :: l2).length := by
      have H := separate_first_pair_correct (l1 :: l2)
      have c_is : c = (separate_first_pair (l1 :: l2)).2.2 := by simp [hs]
      rw [c_is]
      apply congr_arg List.length at H
      simp only [List.append_assoc, List.length_append, List.length_cons] at H
      rw [List.length_cons, ← H, ← add_assoc]
      refine Nat.lt_add_of_pos_left ?_
      apply separate_first_pair_length ?_
      simp
    match H.2.2 with
    | [] =>
      use (List.map (fun x => x ++ c) H.1) ++ (List.map (fun x => H.2.1 ++ H.2.2 ++ x) (fraction_form c).1)
      use H.2.1 ++ (fraction_form c).2.1, (fraction_form c).2.2
    | e1 :: e2 =>
    match (fraction_form c).2.1 with
    | [] =>
      use (List.map (fun x => x ++ c) H.1) ++ (List.map (fun x => H.2.1 ++ H.2.2 ++ x) (fraction_form c).1)
      use H.2.1, H.2.2 ++ (fraction_form c).2.2
    | f1 :: f2 =>
    have H2 := (solver_helper_list
        (to_triangle (List.map (fun x => x.1) (e1 :: e2))
        (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)))
    use (List.map (fun x => x ++ c) H.1) ++
      (List.map (fun x => H.2.1 ++ H.2.2 ++ x) (fraction_form c).1) ++
      (List.map (fun x => H.2.1 ++ x ++ (fraction_form c).2.2) H2.1)
    use H.2.1 ++ H2.2.1, H2.2.2 ++ (fraction_form c).2.2
  termination_by L.length

#show_braid_word_help ((fraction_form ([(1, false), (2, false), (1, true), (2, true), (3, false), (4, false)] : List (ℕ × Bool))).1 : List (List (ℕ × Bool)))
#show_braid_word_help ((fraction_form [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true)]).1 : List (List (ℕ × Bool)))
#show_braid_word_help ((fraction_form [(1, true), (2, false), (2, false), (1, true), (2, false), (3, true), (4, true)]).1 : List (List (ℕ × Bool)))
