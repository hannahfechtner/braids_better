import BraidProject.Solver.Examples
import BraidProject.Widgets

open Braid Relations

def solver_helper_list (a : triangle a1 b1) :
    List (List (ℕ × Bool)) × List (ℕ × Bool) × List (ℕ × Bool) :=
  match hb' : FindOpenPair a.1 with
  | none => by
    rcases SignedList.PosNegData_of_FindOpenPair_none hb' with ⟨c, d, spec⟩
    exact ([a.1], c, d)
  | some (c, d, e) =>
    match hd : d.1.dist d.2 with
    | 0 =>
      let rest := solver_helper_list (⟨c ++ [] ++ e, by
        have := a.2
        rw [FindOpenPair.spec hb'] at this
        exact SemiThueDataDerivation.step this (reversing.basic hd)⟩ : triangle a1 b1)
      ([a.1] ++ rest.1, rest.2)
    | 1 =>
      let rest := solver_helper_list
        (⟨c ++ [(d.2, true), (d.1, true), (d.2, false), (d.1, false)] ++ e, by
          have := a.2
          rw [FindOpenPair.spec hb'] at this
          exact SemiThueDataDerivation.step this (reversing.close hd)⟩ : triangle a1 b1)
      ([a.1] ++ rest.1, rest.2)
    | Nat.succ (Nat.succ n) =>
      let rest := solver_helper_list (⟨c ++ [(d.2, true), (d.1, false)] ++ e, by
        have := a.2
        rw [FindOpenPair.spec hb'] at this
        exact SemiThueDataDerivation.step this (reversing.apart (by omega))⟩ : triangle a1 b1)
      ([a.1] ++ rest.1, rest.2)
  termination_by Triangle.length a
  decreasing_by
    all_goals
      apply (tsub_lt_tsub_iff_left_of_le_of_le
        (SemiThueDataDerivation.reversing.length_le_ab_len _)
        (SemiThueDataDerivation.reversing.length_le_ab_len _)).mpr
      rcases a with ⟨a3, a4⟩
      rcases FindOpenPair.spec hb' with ⟨c1, c2, c3⟩
      simp [SemiThueDataDerivation.length, reversing.length]

def to_triangle (a b : List ℕ) : triangle a b :=
  ⟨to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b, SemiThueDataDerivation.refl⟩

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
      (List.map (fun x => x.1) (b1 :: b2)))
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
        (List.map (fun x => x.1) (f1 :: f2))))
    use (List.map (fun x => x ++ c) H.1) ++
      (List.map (fun x => H.2.1 ++ H.2.2 ++ x) (fraction_form c).1) ++
      (List.map (fun x => H.2.1 ++ x ++ (fraction_form c).2.2) H2.1)
    use H.2.1 ++ H2.2.1, H2.2.2 ++ (fraction_form c).2.2
  termination_by L.length
  decreasing_by
    all_goals exact hc

#show_braid_word_help ((fraction_form ([(1, false), (2, false), (1, true), (2, true), (3, false), (4, false)] : List (ℕ × Bool))).1 : List (List (ℕ × Bool)))
#show_braid_word_help ((fraction_form [(1, false), (0, false), (2, false), (2, false), (3, true), (3, true), (4, true)]).1 : List (List (ℕ × Bool)))
#show_braid_word_help ((fraction_form [(1, true), (2, false), (2, false), (1, true), (2, false), (3, true), (4, true)]).1 : List (List (ℕ × Bool)))
