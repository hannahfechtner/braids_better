import BraidProject.Solver.Monoid
import BraidProject.Solver.SeparatePair

namespace Braid

structure ReverseResult (L : List (ℕ × Bool)) where
  out : List (ℕ × Bool)
  ordered : SignedList.PosNegData out
  steps : SemiThueData reversing L out

open SignedList in
def reverse_word_helper_from_reverse_pair_nonempty_false_suffix_empty_true_prefix (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (sfpc : (separate_first_pair (l1 :: l2)).1 ++
      (separate_first_pair (l1 :: l2)).2.1 ++
      (separate_first_pair (l1 :: l2)).2.2 = l1 :: l2)
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool))
    (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (d : List (ℕ × Bool))
    (H2 : ReverseResult c)
    (g : List (ℕ × Bool))
    (hfg : SignedList.is_true ([] : List (ℕ × Bool)) ∧ SignedList.is_false g ∧ H2.out = [] ++ g)
    (e1 : ℕ × Bool) (e2 : List (ℕ × Bool))
    (htrue : SignedList.is_true d)
    (hfalse : SignedList.is_false (e1 :: e2))
    (hout :
      ((reverse_pair
        (List.map (fun x ↦ x.1) (a1 :: a2).reverse)
        (List.map (fun x ↦ x.1) (b1 :: b2))
        (by simp) (by simp))).1 = d ++ e1 :: e2)
    (H3' :
      SemiThueData reversing
        (to_vertical_edge_no_epsilon (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
          to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) (b1 :: b2)))
        ((reverse_pair
          (List.map (fun x ↦ x.1) (a1 :: a2).reverse)
          (List.map (fun x ↦ x.1) (b1 :: b2))
          (by simp) (by simp))).1) :
    ReverseResult (l1 :: l2) := by
  use d ++ (e1 :: e2) ++ g
  use d, (e1 :: e2) ++ g
  constructor
  constructor
  · exact htrue
  constructor
  · apply SignedList.is_false_append hfalse hfg.2.1
  · simp only [List.append_assoc, List.cons_append]
  simp only [hs, List.cons_append, List.append_assoc] at sfpc
  rw [List.nil_append] at hfg
  rw [← sfpc, ← hout, ← hfg.2.2,
    ← List.cons_append, ← List.cons_append, ← List.append_assoc]
  apply SemiThueData.append
  · have H4 :
        (to_vertical_edge_no_epsilon (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
          to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) (b1 :: b2))) =
        a1 :: a2 ++ b1 :: b2 := by
      have af := separate_first_pair_first_false (l1 :: l2)
      rw [hs] at af
      have bt := separate_first_pair_second_true (l1 :: l2)
      rw [hs] at bt
      rw [to_vertical_edge_no_epsilon_no_bool af, to_horizontal_edge_no_epsilon_no_bool bt]
    rw [← H4]
    exact H3'
  exact H2.steps

def reverse_word_helper_from_reverse_pair_nonempty_false_suffix_nonempty_true_prefix (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (sfpc : (separate_first_pair (l1 :: l2)).1 ++
      (separate_first_pair (l1 :: l2)).2.1 ++
      (separate_first_pair (l1 :: l2)).2.2 = l1 :: l2)
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool))
    (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (d : List (ℕ × Bool))
    (H2 : ReverseResult c)
    (f1 : ℕ × Bool) (f2 g : List (ℕ × Bool))
    (hfg : SignedList.is_true (f1 :: f2) ∧ SignedList.is_false g ∧ H2.out = (f1 :: f2) ++ g)
    (e1 : ℕ × Bool) (e2 : List (ℕ × Bool))
    (htrue : SignedList.is_true d)
    (hfalse : SignedList.is_false (e1 :: e2))
    (hout :
      ((reverse_pair
        (List.map (fun x ↦ x.1) (a1 :: a2).reverse)
        (List.map (fun x ↦ x.1) (b1 :: b2))
        (by simp) (by simp))).1 = d ++ e1 :: e2)
    (H3' :
      SemiThueData reversing
        (to_vertical_edge_no_epsilon (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
          to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) (b1 :: b2)))
        ((reverse_pair
          (List.map (fun x ↦ x.1) (a1 :: a2).reverse)
          (List.map (fun x ↦ x.1) (b1 :: b2))
          (by simp) (by simp))).1) :
    ReverseResult (l1 :: l2) := by
        have H3 := reverse_pair (List.map (fun x => x.1) (e1 :: e2).reverse)
          (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)
        have H4 : SignedList.PosNegData _ := reverse_pair_PosNegData (List.map (fun x => x.1) (e1 :: e2).reverse)
          (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)
        rcases H4 with ⟨i, j, hij⟩
        use d ++ i ++ j ++ g
        use (d ++ i), j ++ g
        constructor
        constructor
        · apply SignedList.is_true_append htrue hij.1.1
        constructor
        · apply SignedList.is_false_append hij.1.2.1 hfg.2.1
        simp
        simp only [hs, List.cons_append, List.append_assoc] at sfpc
        rw [← sfpc, List.append_assoc d i j, ← hij.1.2.2]
        have H5 := @SemiThueData.append_left_right _ _ _ _ d g (@reverse_pair_spec (List.map (fun x => x.1) (e1 :: e2).reverse)
            (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp))
        apply SemiThueData.trans _ H5
        have H6 : (to_vertical_edge_no_epsilon (List.map (fun x ↦ x.1) (e1 :: e2).reverse) ++
            to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) (f1 :: f2))) = e1 :: e2 ++ f1 :: f2 := by
          rw [to_vertical_edge_no_epsilon_no_bool hfalse, to_horizontal_edge_no_epsilon_no_bool hfg.1]
        have H7 : SemiThueData reversing (a1 :: (a2 ++ b1 :: (b2 ++ c)))
          (d ++ (e1 :: e2 ++ f1 :: f2 ++ g)) := by
          rw [List.append_assoc (e1 :: e2), ← List.append_assoc d,
            ← List.cons_append, ← List.cons_append, ← List.append_assoc]
          apply SemiThueData.append
          · rw [← hout]
            apply SemiThueData.trans _ H3'
            convert SemiThueData.refl
            · apply to_vertical_edge_no_epsilon_no_bool
              have a_is : a1 :: a2 = (separate_first_pair (l1 :: l2)).1 := by simp only [hs]
              rw [a_is]
              exact separate_first_pair_first_false _
            apply to_horizontal_edge_no_epsilon_no_bool
            have b_is : b1 :: b2 = (separate_first_pair (l1 :: l2)).2.1 := by simp only [hs]
            rw [b_is]
            exact separate_first_pair_second_true _
          rw [← hfg.2.2]
          exact H2.steps
        rw [H6]
        apply H7.trans
        rw [← List.append_assoc]
        apply SemiThueData.refl

def reverse_word_helper_from_reverse_pair_nonempty_false_suffix (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (sfpc : (separate_first_pair (l1 :: l2)).1 ++ (separate_first_pair (l1 :: l2)).2.1 ++ (separate_first_pair (l1 :: l2)).2.2 =
      l1 :: l2)
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool)) (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (d : List (ℕ × Bool))
    (H2 : ReverseResult c)
    (f g : List (ℕ × Bool))
    (hfg : SignedList.is_true f ∧ SignedList.is_false g ∧ H2.out = f ++ g)
    (e1 : ℕ × Bool)
    (e2 : List (ℕ × Bool))
    (htrue : SignedList.is_true d)
      (hfalse : SignedList.is_false (e1 :: e2))

          (hout : (((reverse_pair (List.map (fun x ↦ x.1) (a1 :: a2).reverse) (List.map (fun x ↦ x.1) (b1 :: b2)) (by simp)
                      (by simp))).1 =
            d ++ e1 :: e2))
    (H3' : SemiThueData reversing
      (to_vertical_edge_no_epsilon (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++ to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) (b1 :: b2)))
      ((reverse_pair (List.map (fun x ↦ x.1) (a1 :: a2).reverse) (List.map (fun x ↦ x.1) (b1 :: b2)) (by simp) (by simp))).1)
    : ReverseResult (l1 :: l2) := by
    match f with
    | [] =>
      exact reverse_word_helper_from_reverse_pair_nonempty_false_suffix_empty_true_prefix
        l1 l2 sfpc a1 a2 b1 b2 c hs d H2 g hfg e1 e2 htrue hfalse hout H3'
    | f1 :: f2 =>
      exact reverse_word_helper_from_reverse_pair_nonempty_false_suffix_nonempty_true_prefix
        l1 l2 sfpc a1 a2 b1 b2 c hs d H2 f1 f2 g hfg e1 e2 htrue hfalse hout H3'

def reverse_word_helper_from_reverse_pair (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (sfpc : (separate_first_pair (l1 :: l2)).1 ++ (separate_first_pair (l1 :: l2)).2.1 ++ (separate_first_pair (l1 :: l2)).2.2 =
      l1 :: l2)
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool)) (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (d e : List (ℕ × Bool)) (htrue : SignedList.is_true d) (hfalse : SignedList.is_false e)
    (hout : ((reverse_pair (List.map (fun x ↦ x.1) (a1 :: a2).reverse) (List.map (fun x ↦ x.1) (b1 :: b2)) (by simp) (by simp))).1 =
      d ++ e) (H2 : ReverseResult c) (f g : List (ℕ × Bool))
    (hfg : SignedList.is_true f ∧ SignedList.is_false g ∧ H2.out = f ++ g) : ReverseResult (l1 :: l2) := by
  match e with
    | [] =>
      use (d++f++g)
      use (d ++ f), g
      constructor
      constructor
      · apply SignedList.is_true_append htrue hfg.1
      constructor
      · exact hfg.2.1
      constructor
      simp only [hs, List.cons_append, List.append_assoc] at sfpc
      rw [List.append_nil] at hout
      rw [← sfpc, ← hout, List.append_assoc _ f g, ← hfg.2.2,
        ← List.cons_append, ← List.cons_append, ← List.append_assoc]
      apply SemiThueData.append
      · have H'' := @reverse_pair_spec (List.map (fun x => x.1) (a1 :: a2).reverse)
          (List.map (fun x => x.1) (b1 :: b2)) (by simp only [List.reverse_cons, List.map_append, List.map_reverse, List.map_cons, List.map_nil, List.length_append,
          List.length_reverse, List.length_map, List.length_cons, List.length_nil, zero_add, gt_iff_lt, lt_add_iff_pos_left,
          add_pos_iff, zero_lt_one, or_true]) (by simp only [List.map_cons, List.length_cons, List.length_map, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff,
          zero_lt_one, or_true])
        have H3 : (to_vertical_edge_no_epsilon (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
          to_horizontal_edge_no_epsilon (List.map (fun x ↦ x.1) (b1 :: b2))) = a1 :: a2 ++ b1 :: b2 := by
          have af := (separate_first_pair_first_false (l1 :: l2))
          rw [hs] at af
          have bt := (separate_first_pair_second_true (l1 :: l2))
          rw [hs] at bt
          rw [to_vertical_edge_no_epsilon_no_bool af, to_horizontal_edge_no_epsilon_no_bool bt]
        rw [← H3]
        exact H''
      apply H2.steps
     | e1 :: e2 =>
      have H3' := @reverse_pair_spec (List.map (fun x => x.1) (a1 :: a2).reverse)
            (List.map (fun x => x.1) (b1 :: b2)) (by simp only [List.reverse_cons, List.map_append, List.map_reverse, List.map_cons, List.map_nil, List.length_append,
            List.length_reverse, List.length_map, List.length_cons, List.length_nil, zero_add, gt_iff_lt, lt_add_iff_pos_left,
            add_pos_iff, zero_lt_one, or_true]) (by simp only [List.map_cons, List.length_cons, List.length_map, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff,
            zero_lt_one, or_true])
      exact reverse_word_helper_from_reverse_pair_nonempty_false_suffix l1 l2 sfpc a1 a2 b1 b2 c
        hs d H2 f g hfg e1 e2 htrue hfalse hout H3'

def reverse_word_pair_case
    (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool))
    (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (H2 : ReverseResult c) :
    ReverseResult (l1 :: l2) := by
  have H1 : SignedList.PosNegData _ :=
    reverse_pair_PosNegData
      (List.map (fun x => x.1) (a1 :: a2).reverse)
      (List.map (fun x => x.1) (b1 :: b2))
      (by
        simp only [List.reverse_cons, List.map_append, List.map_reverse,
          List.map_cons, List.map_nil, List.length_append, List.length_reverse,
          List.length_map, List.length_cons, List.length_nil, zero_add,
          gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true])
      (by
        simp only [List.map_cons, List.length_cons, List.length_map,
          gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true])
  rcases H1 with ⟨d, e, htrue, hfalse, hout⟩
  rcases H2.ordered with ⟨f, g, hfg⟩
  have sfpc := separate_first_pair_correct (l1 :: l2)
  exact reverse_word_helper_from_reverse_pair l1 l2 sfpc a1 a2 b1 b2 c hs d e htrue hfalse hout H2 f g hfg.1

def reverse_word (L : List (ℕ × Bool)) : ReverseResult L :=
  match L with
  | [] => by
    use [], SignedList.PosNegData.nil
    exact SemiThueData.refl
  | l1 :: l2 =>
  match hs : separate_first_pair (l1 :: l2) with
  | ([], (b, c)) => by
    have hc : c.length < (l1 :: l2).length := separate_tail_length hs (by simp)
    let rc := reverse_word c
    use (b++ rc.1)
    have H : SignedList.is_true b := by
      have H : b = (separate_first_pair (l1 :: l2)).2.1 := by simp only [hs]
      rw [H]
      apply separate_first_pair_second_true
    rcases rc.ordered with ⟨d, e, hde⟩
    use (b++d), e
    constructor
    constructor
    · apply SignedList.is_true_append H hde.1.1
    constructor
    · exact hde.1.2.1
    rw [hde.1.2.2]
    simp only [List.append_assoc]
    have sfpc := separate_first_pair_correct (l1 :: l2)
    simp only [hs, List.nil_append] at sfpc
    rw [← sfpc]
    apply SemiThueData.append_left rc.steps
  | (a1::a2, ([], c)) => by
    have hc : c = [] := c_nil_of_separate_no_true hs
    use a1 :: a2
    have af : SignedList.is_false (a1 :: a2) := by
      have H := separate_first_pair_first_false (l1 :: l2)
      rw [hs] at H
      exact H
    exact SignedList.PosNegData.of_false af
    have sfpc := separate_first_pair_correct (l1 :: l2)
    have : l1 :: l2 = a1 :: a2 := by
      rw [hc] at hs
      rw [hs] at sfpc
      rw [← sfpc]
      simp only [List.append_nil]
    rw [this]
    exact SemiThueData.refl
  | (a1::a2, (b1::b2, c)) => by
    have hc : c.length < (l1 :: l2).length := separate_tail_length hs (by simp)
    let H2 := reverse_word c
    exact reverse_word_pair_case l1 l2 a1 a2 b1 b2 c hs H2
  termination_by L.length
  decreasing_by
  · assumption
  · assumption

def group_solver (L1 L2 : List (ℕ × Bool)) : Bool := by
  rcases (reverse_word (L1 ++ (FreeGroup.invRev L2))).ordered with ⟨d, e, hde⟩
  exact monoid_solver (List.map (fun x => x.1) e.reverse) (List.map (fun x => x.1) d)
