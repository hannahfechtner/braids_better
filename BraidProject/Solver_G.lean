import BraidProject.Solver_ST
import BraidProject.BraidGroup
import BraidProject.OreLocalizationPresented
import BraidProject.Cancellability
import Mathlib.Tactic.Group
--import BraidProject.Widgets

-- give a list, returns the maximal true prefix, and then the rest as a pair
def separate_maximal_true_prefix (c : List (ℕ × Bool)) : List (ℕ × Bool) × List (ℕ × Bool) :=
  match c with
  | [] => ([], [])
  | (c1, false) :: c2 => ([], (c1, false) :: c2)
  | (c1, true) :: c2 => ((c1, true) :: (separate_maximal_true_prefix c2).1, (separate_maximal_true_prefix c2).2)

theorem separate_maximal_true_prefix_correct :
    (separate_maximal_true_prefix L).1 ++ (separate_maximal_true_prefix L).2 = L := by
  induction L with
  | nil => exact List.append_nil _
  | cons d e ih =>
    match d with
    | (d1, false) => exact List.nil_append _
    | (d2, true) =>
      simp only [separate_maximal_true_prefix, List.cons_append, ih]

open SignedList

def separate_maximal_true_prefix_is_true : is_true (separate_maximal_true_prefix L).1 := by
  induction L with
  | nil =>
    exact is_true_nil
  | cons d e ih =>
    match d with
    | (d1, false) =>
      exact is_true_nil
    | (d2, true) =>
      exact is_true_cons _ ih

-- give a list, returns the maximal false prefix, and then the rest as a pair
def separate_maximal_false_prefix (c : List (ℕ × Bool)) : List (ℕ × Bool) × List (ℕ × Bool) :=
  match c with
  | [] => ([], [])
  | (c2, true) :: c1 => ([], (c2, true) :: c1)
  | (d, false) :: e => ((d, false) :: (separate_maximal_false_prefix e).1, (separate_maximal_false_prefix e).2)

theorem separate_maximal_false_prefix_correct :
    (separate_maximal_false_prefix L).1 ++ (separate_maximal_false_prefix L).2 = L := by
  induction L with
  | nil => simp [separate_maximal_false_prefix]
  | cons d e ih =>
    match d with
    | (d1, true) =>
      simp [separate_maximal_false_prefix]
    | (d2, false) =>
      simp [separate_maximal_false_prefix, ih]

def separate_maximal_false_prefix_is_false : is_false (separate_maximal_false_prefix L).1 := by
  induction L with
  | nil =>
    simp [separate_maximal_false_prefix]
  | cons d e =>
    match d with
    | (d1, true) =>
      simp [separate_maximal_false_prefix]
    | (d2, false) =>
      simp [separate_maximal_false_prefix]
      apply is_false_cons
      assumption

-- makes a list into the first run of falses, then the run of trues, then the rest
def separate_first_pair (L) := ((separate_maximal_false_prefix L).1,
  (separate_maximal_true_prefix (separate_maximal_false_prefix L).2).1,
  (separate_maximal_true_prefix (separate_maximal_false_prefix L).2).2)

theorem separate_first_pair_correct (L) :
    (separate_first_pair L).1 ++ (separate_first_pair L).2.1 ++ (separate_first_pair L).2.2 = L := by
  unfold separate_first_pair
  simp [separate_maximal_true_prefix_correct, separate_maximal_false_prefix_correct]

def separate_first_pair_first_false (L) : is_false (separate_first_pair L).1 := by
  apply separate_maximal_false_prefix_is_false

def separate_first_pair_second_true (L) : is_true (separate_first_pair L).2.1 := by
  apply separate_maximal_true_prefix_is_true

theorem separate_first_pair_length_disj (hl : L.length > 0) :
    (separate_first_pair L).1.length > 0 ∨ (separate_first_pair L).2.1.length > 0 := by
  match L with
  | [] => simp at hl
  | (a, false) :: L1 =>
    simp [separate_first_pair, separate_maximal_false_prefix]
  | (b, true) :: L2 =>
    simp [separate_first_pair, separate_maximal_false_prefix, separate_maximal_true_prefix]

theorem separate_first_pair_length (hl : L.length > 0) :
    (separate_first_pair L).1.length + (separate_first_pair L).2.1.length > 0 := by
  match L with
  | [] => simp at hl
  | (a, false) :: L1 =>
    simp [separate_first_pair, separate_maximal_false_prefix]
  | (b, true) :: L2 =>
    simp [separate_first_pair, separate_maximal_false_prefix, separate_maximal_true_prefix]

theorem separate_first_pair_nil_nil (h : separate_first_pair L = ([], [], c)) : c = [] := by
  match c with
  | [] => rfl
  | c1 :: c2 =>
    have H := separate_first_pair_correct L
    have H : L = c1 :: c2 := by simp_all
    have H2 := @separate_first_pair_length L (by rw [H]; simp)
    simp_all

open Braid

theorem to_vertical_edge_plain_no_bool {L : List (ℕ × Bool)} (h : is_false L) :
  to_vertical_edge_plain (List.map (fun x ↦ x.1) L.reverse) = L := by
  induction L using List.reverseRecOn with
  | nil => simp [to_vertical_edge_plain]
  | append_singleton l a ih =>
    have hl : is_false l :=(is_false_of_append h).1
    simp [to_vertical_edge_plain]
    constructor
    · unfold to_vertical_edge_plain at ih
      specialize ih hl
      rw [← ih]
      simp
    have ha : is_false [a] := (is_false_of_append h).2
    specialize ha a (by simp)
    simp [← ha]

theorem to_horizontal_edge_plain_no_bool {L : List (ℕ × Bool)} (h : is_true L) :
  to_horizontal_edge_plain (List.map (fun x ↦ x.1) L) = L := by
  induction L with
  | nil => simp [to_horizontal_edge_plain]
  | cons head tail ih =>
    have tt : is_true tail := (is_true_of_cons h).2
    specialize ih tt
    simp only [to_horizontal_edge_plain, List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · have ht : is_true [head] := (is_true_of_cons h).1
      specialize ht head (by simp)
      simp [← ht]
    rw [← ih]
    unfold to_horizontal_edge_plain
    simp

theorem separate_first_pair_cons_false(h : separate_first_pair L = (a, b, c)) :
  separate_first_pair ((d, false) :: L) = ((d, false) :: a, b, c) := by
  unfold separate_first_pair
  simp [separate_maximal_false_prefix]
  unfold separate_first_pair at h
  simp_all

theorem c_nil_of_separate_no_true (h : separate_first_pair L = (a, ([], c))) : c = [] := by
  induction L generalizing a c with
  | nil =>
    have H := separate_first_pair_correct []
    simp_all
  | cons head tail ih =>
    match head with
    | (d, false) =>
      have H := separate_first_pair_correct (head :: tail)
      simp_all
      match a with
      | [] =>
        apply separate_first_pair_nil_nil h
      | a1 :: a2 =>
        simp [separate_first_pair, separate_maximal_false_prefix] at h
        specialize @ih a2 c
        apply ih
        unfold separate_first_pair
        simp_all
    | (d, true) =>
      match a with
      | [] =>
        apply separate_first_pair_nil_nil h
      | a1 :: a2 =>
        simp [separate_first_pair, separate_maximal_false_prefix] at h
structure ReverseResult (L : List (ℕ × Bool)) where
  out : List (ℕ × Bool)
  ordered : PosNegData out
  steps : SemiThue reversing L out

theorem separate_tail_length (h : separate_first_pair L = (a, b, c)) (hL : L.length > 0): c.length < L.length := by
  have H := separate_first_pair_correct L
  apply congr_arg List.length at H
  have H1 := separate_first_pair_length hL
  grind

def helper_for_f_nil (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (sfpc : (separate_first_pair (l1 :: l2)).1 ++
      (separate_first_pair (l1 :: l2)).2.1 ++
      (separate_first_pair (l1 :: l2)).2.2 = l1 :: l2)
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool))
    (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (d : List (ℕ × Bool))
    (H2 : ReverseResult c)
    (g : List (ℕ × Bool))
    (hfg : is_true ([] : List (ℕ × Bool)) ∧ is_false g ∧ H2.out = [] ++ g)
    (e1 : ℕ × Bool) (e2 : List (ℕ × Bool))
    (htrue : is_true d)
    (hfalse : is_false (e1 :: e2))
    (hout :
      ((solver_long
        (List.map (fun x ↦ x.1) (a1 :: a2).reverse)
        (List.map (fun x ↦ x.1) (b1 :: b2))
        (by simp) (by simp))).val.2.2.1 = d ++ e1 :: e2)
    (H3' :
      SemiThue reversing
        (to_vertical_edge_plain (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
          to_horizontal_edge_plain (List.map (fun x ↦ x.1) (b1 :: b2)))
        ((solver_long
          (List.map (fun x ↦ x.1) (a1 :: a2).reverse)
          (List.map (fun x ↦ x.1) (b1 :: b2))
          (by simp) (by simp))).val.snd.snd.fst) :
    ReverseResult (l1 :: l2) := by
  use d ++ (e1 :: e2) ++ g
  use d, (e1 :: e2) ++ g
  constructor
  constructor
  · exact htrue
  constructor
  · apply is_false_append hfalse hfg.2.1
  · simp only [List.append_assoc, List.cons_append]
  simp only [hs, List.cons_append, List.append_assoc] at sfpc
  rw [List.nil_append] at hfg
  rw [← sfpc, ← hout, ← hfg.2.2,
    ← List.cons_append, ← List.cons_append, ← List.append_assoc]
  apply SemiThue.append
  · have H4 :
        (to_vertical_edge_plain (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
          to_horizontal_edge_plain (List.map (fun x ↦ x.1) (b1 :: b2))) =
        a1 :: a2 ++ b1 :: b2 := by
      have af := separate_first_pair_first_false (l1 :: l2)
      rw [hs] at af
      have bt := separate_first_pair_second_true (l1 :: l2)
      rw [hs] at bt
      rw [to_vertical_edge_plain_no_bool af, to_horizontal_edge_plain_no_bool bt]
    rw [← H4]
    exact H3'
  exact H2.steps

def helper_for_f_cons (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (sfpc : (separate_first_pair (l1 :: l2)).1 ++
      (separate_first_pair (l1 :: l2)).2.1 ++
      (separate_first_pair (l1 :: l2)).2.2 = l1 :: l2)
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool))
    (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (d : List (ℕ × Bool))
    (H2 : ReverseResult c)
    (f1 : ℕ × Bool) (f2 g : List (ℕ × Bool))
    (hfg : is_true (f1 :: f2) ∧ is_false g ∧ H2.out = (f1 :: f2) ++ g)
    (e1 : ℕ × Bool) (e2 : List (ℕ × Bool))
    (htrue : is_true d)
    (hfalse : is_false (e1 :: e2))
    (hout :
      ((solver_long
        (List.map (fun x ↦ x.1) (a1 :: a2).reverse)
        (List.map (fun x ↦ x.1) (b1 :: b2))
        (by simp) (by simp))).val.2.2.1 = d ++ e1 :: e2)
    (H3' :
      SemiThue reversing
        (to_vertical_edge_plain (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
          to_horizontal_edge_plain (List.map (fun x ↦ x.1) (b1 :: b2)))
        ((solver_long
          (List.map (fun x ↦ x.1) (a1 :: a2).reverse)
          (List.map (fun x ↦ x.1) (b1 :: b2))
          (by simp) (by simp))).val.snd.snd.fst) :
    ReverseResult (l1 :: l2) := by
        have H3 := solver_long (List.map (fun x => x.1) (e1 :: e2).reverse)
          (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)
        have H4 : PosNegData _ := solver_long_PosNegData (List.map (fun x => x.1) (e1 :: e2).reverse)
          (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp)
        rcases H4 with ⟨i, j, hij⟩
        use d ++ i ++ j ++ g
        use (d ++ i), j ++ g
        constructor
        constructor
        · apply is_true_append htrue hij.1.1
        constructor
        · apply is_false_append hij.1.2.1 hfg.2.1
        simp
        simp only [hs, List.cons_append, List.append_assoc] at sfpc
        rw [← sfpc, List.append_assoc d i j, ← hij.1.2.2]
        have H5 := @SemiThue.append_left_right _ _ _ _ d g (@solver_equiv (List.map (fun x => x.1) (e1 :: e2).reverse)
            (List.map (fun x => x.1) (f1 :: f2)) (by simp) (by simp))
        apply SemiThue.trans _ H5
        have H6 : (to_vertical_edge_plain (List.map (fun x ↦ x.1) (e1 :: e2).reverse) ++
            to_horizontal_edge_plain (List.map (fun x ↦ x.1) (f1 :: f2))) = e1 :: e2 ++ f1 :: f2 := by
          rw [to_vertical_edge_plain_no_bool hfalse, to_horizontal_edge_plain_no_bool hfg.1]
        have H7 : SemiThue reversing (a1 :: (a2 ++ b1 :: (b2 ++ c)))
          (d ++ (e1 :: e2 ++ f1 :: f2 ++ g)) := by
          rw [List.append_assoc (e1 :: e2), ← List.append_assoc d,
            ← List.cons_append, ← List.cons_append, ← List.append_assoc]
          apply SemiThue.append
          · rw [← hout]
            apply SemiThue.trans _ H3'
            convert SemiThue.refl
            · apply to_vertical_edge_plain_no_bool
              have a_is : a1 :: a2 = (separate_first_pair (l1 :: l2)).1 := by simp only [hs]
              rw [a_is]
              exact separate_first_pair_first_false _
            apply to_horizontal_edge_plain_no_bool
            have b_is : b1 :: b2 = (separate_first_pair (l1 :: l2)).2.1 := by simp only [hs]
            rw [b_is]
            exact separate_first_pair_second_true _
          rw [← hfg.2.2]
          exact H2.steps
        rw [H6]
        apply H7.trans
        rw [← List.append_assoc]
        apply SemiThue.refl

def helper_for_f (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (sfpc : (separate_first_pair (l1 :: l2)).1 ++ (separate_first_pair (l1 :: l2)).2.1 ++ (separate_first_pair (l1 :: l2)).2.2 =
      l1 :: l2)
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool)) (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (d : List (ℕ × Bool))
    (H2 : ReverseResult c)
    (f g : List (ℕ × Bool))
    (hfg : is_true f ∧ is_false g ∧ H2.out = f ++ g)
    (e1 : ℕ × Bool)
    (e2 : List (ℕ × Bool))
    (htrue : is_true d)
      (hfalse : is_false (e1 :: e2))

          (hout : (((solver_long (List.map (fun x ↦ x.1) (a1 :: a2).reverse) (List.map (fun x ↦ x.1) (b1 :: b2)) (by simp)
                      (by simp))).val.2.2.1 =
            d ++ e1 :: e2))
    (H3' : SemiThue reversing
      (to_vertical_edge_plain (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++ to_horizontal_edge_plain (List.map (fun x ↦ x.1) (b1 :: b2)))
      ((solver_long (List.map (fun x ↦ x.1) (a1 :: a2).reverse) (List.map (fun x ↦ x.1) (b1 :: b2)) (by simp) (by simp))).val.snd.snd.fst)
    : ReverseResult (l1 :: l2) := by
    match f with
    | [] =>
      exact helper_for_f_nil
        l1 l2 sfpc a1 a2 b1 b2 c hs d H2 g hfg e1 e2 htrue hfalse hout H3'
    | f1 :: f2 =>
      exact helper_for_f_cons
        l1 l2 sfpc a1 a2 b1 b2 c hs d H2 f1 f2 g hfg e1 e2 htrue hfalse hout H3'

def helper_for_e (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (sfpc : (separate_first_pair (l1 :: l2)).1 ++ (separate_first_pair (l1 :: l2)).2.1 ++ (separate_first_pair (l1 :: l2)).2.2 =
      l1 :: l2)
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool)) (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (d e : List (ℕ × Bool)) (htrue : is_true d) (hfalse : is_false e)
    (hout : ((solver_long (List.map (fun x ↦ x.1) (a1 :: a2).reverse) (List.map (fun x ↦ x.1) (b1 :: b2)) (by simp) (by simp))).val.snd.snd.fst =
      d ++ e) (H2 : ReverseResult c) (f g : List (ℕ × Bool))
    (hfg : is_true f ∧ is_false g ∧ H2.out = f ++ g) : ReverseResult (l1 :: l2) := by
  match e with
    | [] =>
      use (d++f++g)
      use (d ++ f), g
      constructor
      constructor
      · apply is_true_append htrue hfg.1
      constructor
      · exact hfg.2.1
      constructor
      simp only [hs, List.cons_append, List.append_assoc] at sfpc
      rw [List.append_nil] at hout
      rw [← sfpc, ← hout, List.append_assoc _ f g, ← hfg.2.2,
        ← List.cons_append, ← List.cons_append, ← List.append_assoc]
      apply SemiThue.append
      · have H'' := @solver_equiv (List.map (fun x => x.1) (a1 :: a2).reverse)
          (List.map (fun x => x.1) (b1 :: b2)) (by simp only [List.reverse_cons, List.map_append, List.map_reverse, List.map_cons, List.map_nil, List.length_append,
          List.length_reverse, List.length_map, List.length_cons, List.length_nil, zero_add, gt_iff_lt, lt_add_iff_pos_left,
          add_pos_iff, zero_lt_one, or_true]) (by simp only [List.map_cons, List.length_cons, List.length_map, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff,
          zero_lt_one, or_true])
        have H3 : (to_vertical_edge_plain (List.map (fun x ↦ x.1) (a1 :: a2).reverse) ++
          to_horizontal_edge_plain (List.map (fun x ↦ x.1) (b1 :: b2))) = a1 :: a2 ++ b1 :: b2 := by
          have af := (separate_first_pair_first_false (l1 :: l2))
          rw [hs] at af
          have bt := (separate_first_pair_second_true (l1 :: l2))
          rw [hs] at bt
          rw [to_vertical_edge_plain_no_bool af, to_horizontal_edge_plain_no_bool bt]
        rw [← H3]
        exact H''
      apply H2.steps
     | e1 :: e2 =>
      have H3' := @solver_equiv (List.map (fun x => x.1) (a1 :: a2).reverse)
            (List.map (fun x => x.1) (b1 :: b2)) (by simp only [List.reverse_cons, List.map_append, List.map_reverse, List.map_cons, List.map_nil, List.length_append,
            List.length_reverse, List.length_map, List.length_cons, List.length_nil, zero_add, gt_iff_lt, lt_add_iff_pos_left,
            add_pos_iff, zero_lt_one, or_true]) (by simp only [List.map_cons, List.length_cons, List.length_map, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff,
            zero_lt_one, or_true])
      exact helper_for_f l1 l2 sfpc a1 a2 b1 b2 c hs d H2 f g hfg e1 e2 htrue hfalse hout H3'

def reverse_complex_pair_case
    (l1 : ℕ × Bool) (l2 : List (ℕ × Bool))
    (a1 : ℕ × Bool) (a2 : List (ℕ × Bool))
    (b1 : ℕ × Bool) (b2 c : List (ℕ × Bool))
    (hs : separate_first_pair (l1 :: l2) = (a1 :: a2, b1 :: b2, c))
    (H2 : ReverseResult c) :
    ReverseResult (l1 :: l2) := by
  have H1 : PosNegData _ :=
    solver_long_PosNegData
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
  exact helper_for_e l1 l2 sfpc a1 a2 b1 b2 c hs d e htrue hfalse hout H2 f g hfg.1

-- set_option trace.profiler.useHeartbeats true in
-- set_option trace.profiler true in
def reverse_complex (L : List (ℕ × Bool)) : ReverseResult L :=
  match L with
  | [] => by
    use [], PosNegData.nil
    exact SemiThue.refl
  | l1 :: l2 =>
  match hs : separate_first_pair (l1 :: l2) with
  | ([], (b, c)) => by
    have hc : c.length < (l1 :: l2).length := separate_tail_length hs (by simp)
    let rc := reverse_complex c
    use (b++ rc.1)
    have H : is_true b := by
      have H : b = (separate_first_pair (l1 :: l2)).2.1 := by simp only [hs]
      rw [H]
      apply separate_first_pair_second_true
    rcases rc.ordered with ⟨d, e, hde⟩
    use (b++d), e
    constructor
    constructor
    · apply is_true_append H hde.1.1
    constructor
    · exact hde.1.2.1
    rw [hde.1.2.2]
    simp only [List.append_assoc]
    have sfpc := separate_first_pair_correct (l1 :: l2)
    simp only [hs, List.nil_append] at sfpc
    rw [← sfpc]
    apply SemiThue.append_left rc.steps
  | (a1::a2, ([], c)) => by
    have hc : c = [] := c_nil_of_separate_no_true hs
    use a1 :: a2
    have af : is_false (a1 :: a2) := by
      have H := separate_first_pair_first_false (l1 :: l2)
      rw [hs] at H
      exact H
    exact PosNegData.of_false af
    have sfpc := separate_first_pair_correct (l1 :: l2)
    have : l1 :: l2 = a1 :: a2 := by
      rw [hc] at hs
      rw [hs] at sfpc
      rw [← sfpc]
      simp only [List.append_nil]
    rw [this]
    exact SemiThue.refl
  | (a1::a2, (b1::b2, c)) => by
    have hc : c.length < (l1 :: l2).length := separate_tail_length hs (by simp)
    let H2 := reverse_complex c
    exact reverse_complex_pair_case l1 l2 a1 a2 b1 b2 c hs H2
  termination_by L.length
structure ReverseResult' (L : List (ℕ × Bool)) where
  out : List (ℕ × Bool)
  ordered : PosNegData out
  steps : SemiThue reversing L out

def solver_g (L1 L2 : List (ℕ × Bool)) : Bool := by
  rcases (reverse_complex (L1 ++ (FreeGroup.invRev L2))).ordered with ⟨d, e, hde⟩
  exact final_solver (List.map (fun x => x.1) e.reverse) (List.map (fun x => x.1) d)


-- lemma mul_inv_mem_of_mk_eq_mk {rels : Set (FreeGroup α)} {x y : FreeGroup α}
--   (h :  PresentedGroup.mk rels x = PresentedGroup.mk rels y) : x * y⁻¹ ∈ rels:= by
--   sorry
--   --eq_of_mul_inv_eq_one <| one_of_mem hx

theorem SemiThue_reversing_to_braid_group_equiv (h : SemiThue reversing a b) :
  Braid.BraidGroupInf.mk (FreeGroup.mk a) =
  Braid.BraidGroupInf.mk (FreeGroup.mk b) := by
  induction h with
  | refl => rfl
  | step h =>
    rename_i e f g i
    unfold Braid.BraidGroupInf.mk
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
      PresentedGroup.mk_mul, PresentedGroup.mk_mul, PresentedGroup.mk_mul, PresentedGroup.mk_mul,
      mul_left_inj, mul_right_inj]
    cases h with
    | basic =>
      rename_i i j hij
      apply Nat.eq_of_dist_eq_zero at hij
      rw [← hij]
      change (PresentedGroup.mk ((ArtinTits.Group.relation_set Braid.BraidMatrixInf)))
        (FreeGroup.mk ([(i, false)] ++ [(i, true)])) = _
      rw [← FreeGroup.mul_mk]
      unfold FreeGroup.mk
      congr
      exact eq_div_iff_mul_eq'.mp rfl
    | apart h =>
      rename_i i j
      change (Braid.σ i)⁻¹ * Braid.σ j = Braid.σ j * (Braid.σ i)⁻¹
      apply (mul_right_inj (Braid.σ i)).mp
      apply (mul_left_inj (Braid.σ i)).mp
      group
      symm
      exact Braid.BraidGroupInf.comm h
    | close h =>
      rename_i i j
      change (Braid.σ i)⁻¹ * Braid.σ j = Braid.σ j *  Braid.σ i * (Braid.σ j)⁻¹ * (Braid.σ i)⁻¹
      apply (mul_right_inj (Braid.σ i)).mp
      apply (mul_left_inj (Braid.σ i)).mp
      apply (mul_left_inj (Braid.σ j)).mp
      group
      symm
      exact Braid.BraidGroupInf.braid h
  | trans _ _ ih1 ih2 =>
    exact ih1.trans ih2

theorem to_horizontal_edge_plain_of (i : ℕ) : to_horizontal_edge_plain (FreeMonoid.of i) = [(i, true)] := by rfl

open Braid in
theorem bm_to_bg (h : BraidMonoidInf.mk a =
  BraidMonoidInf.mk b) :
  BraidGroupInf.mk (FreeGroup.mk (to_horizontal_edge_plain a)) =
  BraidGroupInf.mk (FreeGroup.mk (to_horizontal_edge_plain b)) := by
  apply PresentedMonoid.exact at h
  induction h with
  | of x y h =>
    cases h with
    | adjacent i => exact Braid.BraidGroupInf.braid dist_succ
    | separated i j h =>
      apply Braid.BraidGroupInf.comm
      apply or_dist_iff.mpr
      left; exact h
  | refl x => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | mul _ _ ih1 ih2 =>
    rw [to_horizontal_edge_plain_mul, to_horizontal_edge_plain_mul, ← FreeGroup.mul_mk,  ← FreeGroup.mul_mk,
      map_mul, map_mul, ih1, ih2]

theorem PresentedGroup.mk_inv {rels : Set (FreeGroup α)} : (PresentedGroup.mk rels a)⁻¹ =
  (PresentedGroup.mk rels) a⁻¹ := by rfl

theorem pg_mk_fg_inv : (Braid.BraidGroupInf.mk (FreeGroup.mk a))⁻¹ =
  Braid.BraidGroupInf.mk (FreeGroup.mk (FreeGroup.invRev a)) := by
  rw [← map_inv, FreeGroup.inv_mk]

open Braid
theorem pg_mk_to_horizontal_edge_plain_inv :
  (BraidGroupInf.mk (FreeGroup.mk (to_horizontal_edge_plain a)))⁻¹ =
  BraidGroupInf.mk (FreeGroup.mk (to_vertical_edge_plain a)) := by
  rw [pg_mk_fg_inv]
  congr
  unfold to_horizontal_edge_plain to_vertical_edge_plain FreeGroup.invRev
  simp

theorem to_vertical_edge_plain_reverse : to_vertical_edge_plain a.reverse = (to_vertical_edge_plain a).reverse := by
  simp [to_vertical_edge_plain]

theorem recover_from_is_false (h : is_false d) : to_vertical_edge_plain (List.map (fun x ↦ x.1) d).reverse = (d : List (ℕ × Bool)) := by
  rw [to_vertical_edge_plain_reverse]
  have H : (to_vertical_edge_plain (List.map (fun x ↦ x.1) d)).reverse.reverse = d.reverse := by
    rw [List.reverse_reverse]
    induction d with
    | nil => simp [to_vertical_edge_plain]
    | cons head tail ih =>
      have tf : is_false tail := (is_false_of_cons h).2
      unfold to_vertical_edge_plain at ih
      simp [to_vertical_edge_plain, ih tf]
      have H2 := (is_false_of_cons h).1
      specialize H2 head (by simp)
      simp [← H2]
  exact List.reverse_injective H

theorem recover_from_is_true (h : is_true d) : to_horizontal_edge_plain (List.map (fun x ↦ x.1) d) = (d : List (ℕ × Bool)) := by
  induction d with
  | nil => simp [to_horizontal_edge_plain]
  | cons head tail ih =>
    have tt : is_true tail := (is_true_of_cons h).2
    specialize ih tt
    simp only [to_horizontal_edge_plain, List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · have ht : is_true [head] := (is_true_of_cons h).1
      specialize ht head (by simp)
      simp [← ht]
    rw [← ih]
    unfold to_horizontal_edge_plain
    simp

open Braid

theorem solver_g_correct_one_direction : solver_g a b = true →
    BraidGroupInf.mk (FreeGroup.mk a) =
    BraidGroupInf.mk (FreeGroup.mk b) := by
  intro h
  unfold solver_g at h
  rcases dede : (reverse_complex (a ++ (FreeGroup.invRev b))).ordered with ⟨d, e, hde⟩
  have H := correct_one_dir h
  have H2 := SemiThue_reversing_to_braid_group_equiv ((reverse_complex (a ++ (FreeGroup.invRev b))).steps)
  rw [hde.1.2.2] at H2
  rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul] at H2
  have d_is : (reverse_complex (a ++ FreeGroup.invRev b)).ordered.fst = d := by aesop
  rw [d_is] at H
  have e_is : (reverse_complex (a ++ FreeGroup.invRev b)).ordered.2.1 = e := by
    rw [dede]
  rw [e_is] at H
  apply bm_to_bg at H
  apply (mul_right_inj (BraidGroupInf.mk
    (FreeGroup.mk (to_horizontal_edge_plain (List.map (fun x ↦ x.1) e.reverse))))⁻¹).mpr at H
  simp at H
  rw [pg_mk_to_horizontal_edge_plain_inv, recover_from_is_true hde.1.1, recover_from_is_false hde.1.2.1] at H
  apply (mul_right_inj ((BraidGroupInf.mk
        (FreeGroup.mk e))⁻¹)).mpr at H
  apply (mul_left_inj (BraidGroupInf.mk
        (FreeGroup.mk e))).mpr at H
  rw [mul_one, inv_mul_cancel, inv_mul_cancel_left] at H
  rw [← H] at H2
  apply (mul_left_inj (BraidGroupInf.mk
    (FreeGroup.mk (FreeGroup.invRev b)))⁻¹).mpr at H2
  rw [mul_inv_cancel_right, one_mul] at H2
  rw [H2, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev_invRev]

def invRev_true_of_is_false (h : is_false e) : is_true (FreeGroup.invRev e) := by
  intro a ha
  unfold FreeGroup.invRev at ha
  simp only [List.mem_reverse, List.mem_map, Prod.exists, Bool.exists_bool, Bool.not_false,
    Bool.not_true] at ha
  rcases ha with ⟨c, hc | hd⟩
  · simp [← hc.2]
  exfalso
  specialize h (c, true) hd.1
  simp only [Bool.true_eq_false] at h

theorem lift_of_group : (FreeMonoid.lift FreeGroup.of) (FreeMonoid.of i) = FreeGroup.of i := by rfl

theorem lift_of_group_two {a : FreeMonoid ℕ} : (FreeMonoid.lift FreeGroup.of) a =
  FreeGroup.mk (to_horizontal_edge_plain a) := by
  induction a using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of b a ih =>
    simp [to_horizontal_edge_plain_mul, ih, ← FreeGroup.mul_mk]
    change FreeGroup.of b = FreeGroup.mk [(b, true)]
    rfl

open FreeMonoid in
inductive braid_rels_m_inf_one_symm : FreeMonoid ℕ → FreeMonoid ℕ → Prop
  | adjacent (i j : ℕ) (h : i.dist j = 1) : braid_rels_m_inf_one_symm (of i * of j * of i) (of j * of i * of j)
  | separated (i j : ℕ) (h : i.dist j ≥ 2) : braid_rels_m_inf_one_symm (of i * of j) (of j * of i)
  | basic (i) : braid_rels_m_inf_one_symm (of i) (of i)

theorem connect_monoid_group_braid_rels : PresentedGroup.free_group_set_of_function braid_rels_m_inf_one_symm =
  Braid.braidRelationInf := by
  unfold PresentedGroup.free_group_set_of_function
  ext
  rename_i y
  constructor
  · intro h
    simp at h
    rcases h with ⟨a, b, hbr, hl⟩
    rw [← hl, lift_of_group_two, lift_of_group_two]
    cases hbr with
    | adjacent i j hd =>
      simp only [to_horizontal_edge_plain_mul, ← FreeGroup.mul_mk]
      simp only [to_horizontal_edge_plain_of]
      unfold Braid.braidRelationInf
      use (i, j)
      simp only [Function.uncurry_apply_pair, ArtinTits.Group.relation, BraidMatrixInf_adjacent, Monoid.alternate, hd]
      rfl
    | separated i j h =>
      simp only [to_horizontal_edge_plain_mul, ← FreeGroup.mul_mk]
      simp only [to_horizontal_edge_plain_of]
      unfold Braid.braidRelationInf
      use (i, j)
      have H : ∃ n, i.dist (j) = Nat.succ (Nat.succ n) := by
        match hij : i.dist j with
        | 0 =>
          have : i = j := Nat.eq_of_dist_eq_zero hij
          omega
        | Nat.succ n1 =>
          match n1 with
          | 0 =>
            have H := or_dist_iff_eq.mp hij
            omega
          | Nat.succ n2 => use n2
      rcases H with ⟨n, hn⟩
      simp only [Function.uncurry_apply_pair, ArtinTits.Group.relation, BraidMatrixInf_separated h, Monoid.alternate]
      rfl
    | basic i =>
      rw [mul_inv_cancel (FreeGroup.mk (to_horizontal_edge_plain (FreeMonoid.of i)))]
      use (i, i)
      simp [Function.uncurry_apply_pair, ArtinTits.Group.relation]
  intro h
  simp only [Set.mem_setOf_eq, Prod.exists]
  unfold Braid.braidRelationInf at h
  unfold ArtinTits.Group.relation_set at h
  simp at h
  rcases h with ⟨a, b, br⟩
  unfold ArtinTits.Group.relation at br
  cases hab : a.dist b with
  | zero =>
    have : a = b := Nat.eq_of_dist_eq_zero hab
    rw [this] at br
    simp at br
    rw [← br]
    use [27], [27]
    constructor
    · apply braid_rels_m_inf_one_symm.basic _
    simp
  | succ n =>
    cases hn : n with
    | zero =>
      simp [BraidMatrixInf_adjacent, hn, hab] at br
      rw [← br]
      use [a, b, a], [b, a, b]
      constructor
      · rw [hn, zero_add] at hab
        exact braid_rels_m_inf_one_symm.adjacent _ _ hab
      rfl
    | succ n2 =>
      have : a.dist b > 1 := by linarith
      simp [BraidMatrixInf_separated this] at br
      rw [← br]
      use [a, b], [b, a]
      constructor
      · apply braid_rels_m_inf_one_symm.separated
        aesop
      rfl

open PresentedMonoid in
theorem one_symm_is_really_the_same : mk braid_monoid_rels_inf a = mk braid_monoid_rels_inf b ↔
  mk braid_rels_m_inf_one_symm a = mk braid_rels_m_inf_one_symm b := by
  constructor
  · intro h
    apply PresentedMonoid.exact at h
    apply PresentedMonoid.sound
    induction h with
    | of x y h2 =>
      cases h2 with
      | adjacent i =>
        exact PresentedMonoid.rels_alone <| braid_rels_m_inf_one_symm.adjacent _ _ dist_succ
      | separated i j h =>
        apply PresentedMonoid.rels_alone
        apply braid_rels_m_inf_one_symm.separated
        apply or_dist_iff.mpr
        left; exact h
    | refl x => exact PresentedMonoid.refl
    | symm _ ih => exact PresentedMonoid.symm ih
    | trans _ _ ih1 ih2 => exact PresentedMonoid.trans ih1 ih2
    | mul _ _ ih1 ih2 => exact mul ih1 ih2
  intro h
  apply PresentedMonoid.exact at h
  apply PresentedMonoid.sound
  induction h with
  | of x y h =>
    cases h with
    | adjacent i j h =>
      apply or_dist_iff_eq.mp at h
      rcases h with h | h
      · rw [← h]
        apply rels_alone
        apply braid_monoid_rels_inf.adjacent

      apply PresentedMonoid.symm
      apply rels_alone
      rw [← h]
      exact braid_monoid_rels_inf.adjacent j
    | separated i j h =>
      apply or_dist_iff.mp at h
      rcases h with h | h
      · exact rels_alone <| braid_monoid_rels_inf.separated _ _ h
      exact PresentedMonoid.symm <| rels_alone <| braid_monoid_rels_inf.separated _ _ h
    | basic i => exact BraidMonoidInf.exact rfl
  | refl x => exact BraidMonoidInf.exact rfl
  | symm _ ih => exact PresentedMonoid.symm ih
  | trans _ _ ih1 ih2 => exact PresentedMonoid.trans ih1 ih2
  | mul _ _ ih1 ih2 => exact mul ih1 ih2

variable {rels : FreeMonoid ℕ → FreeMonoid ℕ → Prop} {h : IsRightCancelMul (PresentedMonoid rels)} {h1 : IsCommonLeftMultipleMul (PresentedMonoid rels)}

variable {h : IsRightCancelMul (PresentedMonoid braid_rels_m_inf)} {h1 : IsCommonLeftMultipleMul (PresentedMonoid braid_rels_m_inf)}

theorem right_cancel_extends [h2 : IsRightCancelMul BraidMonoidInf] :
  IsRightCancelMul (PresentedMonoid braid_rels_m_inf_one_symm) where
  mul_right_cancel := by
    intro a b c h
    rcases Quotient.exists_rep a with ⟨a1, ha1⟩
    rcases Quotient.exists_rep b with ⟨b1, hb1⟩
    rcases Quotient.exists_rep c with ⟨c1, hc1⟩
    rw [← ha1, ← hb1, ← hc1] at h
    apply one_symm_is_really_the_same.mpr at h
    simp only [PresentedMonoid.mk_mul] at h
    change BraidMonoidInf.mk b1 * _ = _ * _ at h
    rw  [mul_left_inj] at h
    rw [← hb1, ← hc1]
    exact one_symm_is_really_the_same.mp h

theorem left_cancel_extends [h2 : IsLeftCancelMul BraidMonoidInf] :
  IsLeftCancelMul (PresentedMonoid braid_rels_m_inf_one_symm) where
  mul_left_cancel := by
    intro a b c h
    rcases Quotient.exists_rep a with ⟨a1, ha1⟩
    rcases Quotient.exists_rep b with ⟨b1, hb1⟩
    rcases Quotient.exists_rep c with ⟨c1, hc1⟩
    rw [← ha1, ← hb1, ← hc1] at h
    change ⟦a1 * b1⟧ = ⟦a1 * c1⟧ at h
    apply one_symm_is_really_the_same.mpr at h
    change BraidMonoidInf.mk _ = BraidMonoidInf.mk _ at h
    rw [map_mul, map_mul, mul_right_inj] at h
    rw [← hb1, ← hc1]
    exact one_symm_is_really_the_same.mp h

theorem fm_lift_pm_of_eq_pm_mk : (FreeMonoid.lift (PresentedMonoid.of rels)) a =
    PresentedMonoid.mk rels a := by
  induction a using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of b a ih =>
    simp [ih]
    rfl

noncomputable def map_to_one_symm : (PresentedMonoid braid_monoid_rels_inf) →*
  PresentedMonoid braid_rels_m_inf_one_symm := by
  apply PresentedMonoid.lift (PresentedMonoid.of braid_rels_m_inf_one_symm)
  intro a b cg
  apply PresentedMonoid.sound at cg
  apply one_symm_is_really_the_same.mp at cg
  rw [fm_lift_pm_of_eq_pm_mk, fm_lift_pm_of_eq_pm_mk]
  exact cg

noncomputable def map_from_one_symm : (PresentedMonoid braid_rels_m_inf_one_symm) →*
  PresentedMonoid braid_monoid_rels_inf := by
  apply PresentedMonoid.lift (PresentedMonoid.of braid_monoid_rels_inf)
  intro a b cg
  apply PresentedMonoid.sound at cg
  apply one_symm_is_really_the_same.mpr at cg
  rw [fm_lift_pm_of_eq_pm_mk, fm_lift_pm_of_eq_pm_mk]
  exact cg

noncomputable def one_symm_type_iso_me : (PresentedMonoid braid_rels_m_inf_one_symm) ≃*
  PresentedMonoid braid_monoid_rels_inf := by
  refine MonoidHom.toMulEquiv map_from_one_symm map_to_one_symm ?_ ?_
  exact PresentedMonoid.ext_iff.mpr (congrFun rfl)
  exact PresentedMonoid.ext_iff.mpr (congrFun rfl)

noncomputable def left_multiple_iso [Mul A] [Mul B] [h2 : IsCommonLeftMultipleMul A] (e : A ≃* B) :
  IsCommonLeftMultipleMul B where
  common_left_multiple := by
    intro a b
    have := (h2.common_left_multiple (e.symm a) (e.symm b))
    rcases this with ⟨c, d, hcd⟩
    apply congr_arg e at hcd
    simp at hcd
    use e c, e d

noncomputable def cancel_mul_iso [Mul A] [Mul B] [h2 : IsCancelMul A] (e : A ≃* B) :
  IsCancelMul B where
  mul_left_cancel := by
    intro a b c h
    apply congr_arg e.symm at h
    rw [map_mul, map_mul] at h
    apply (h2.mul_left_cancel (e.symm a)) at h
    rw [EmbeddingLike.apply_eq_iff_eq] at h
    exact h
  mul_right_cancel := by
    intro a b c h
    apply congr_arg e.symm at h
    rw [map_mul, map_mul] at h
    apply (h2.mul_right_cancel (e.symm a)) at h
    rw [EmbeddingLike.apply_eq_iff_eq] at h
    exact h

-- this is now in orelocalizatinpresented pg_to_pm_fg_mk

theorem invRev_remove_eq_reverse {e : List (α × Bool)} :
  (List.map (fun x ↦ x.1) e).reverse =
  (List.map ((fun x ↦ x.1) ∘ fun g ↦ (g.1, !g.2)) e).reverse := by simp

set_option maxHeartbeats 2000000
theorem solver_g_correct_other_direction :
    BraidGroupInf.mk (FreeGroup.mk a) =
    BraidGroupInf.mk (FreeGroup.mk b) →
    solver_g a b = true := by
  intro h
  unfold solver_g
  apply correct_other_dir
  rcases dede : (reverse_complex (a ++ (FreeGroup.invRev b))).ordered with ⟨d, e, hde⟩
  have d_is : (reverse_complex (a ++ FreeGroup.invRev b)).ordered.fst = d := by aesop
  have e_is : (reverse_complex (a ++ FreeGroup.invRev b)).ordered.2.1 = e := by
    rw [dede]
  rw [d_is, e_is]
  have H2 := SemiThue_reversing_to_braid_group_equiv ((reverse_complex (a ++ (FreeGroup.invRev b))).steps)
  rw [hde.1.2.2, ← FreeGroup.mul_mk, map_mul, h, ← FreeGroup.inv_mk,
    map_inv, mul_inv_cancel, ← FreeGroup.mul_mk, map_mul] at H2
  apply (mul_left_inj (BraidGroupInf.mk
    (FreeGroup.mk e))⁻¹).mpr at H2
  rw [one_mul, mul_inv_cancel_right, ← map_inv, FreeGroup.inv_mk] at H2
  have : IsCommonLeftMultipleMul (PresentedMonoid braid_rels_m_inf_one_symm) := by
    have : IsCommonLeftMultipleMul (PresentedMonoid braid_monoid_rels_inf) := by
      change IsCommonLeftMultipleMul BraidMonoidInf
      infer_instance
    apply left_multiple_iso one_symm_type_iso_me.symm
  have : IsCancelMul (PresentedMonoid braid_rels_m_inf_one_symm) := by
    have : IsCancelMul (PresentedMonoid braid_monoid_rels_inf) := by
      change IsCancelMul BraidMonoidInf
      infer_instance
    apply cancel_mul_iso one_symm_type_iso_me.symm
  unfold BraidGroupInf.mk at H2
  rw [← connect_monoid_group_braid_rels] at H2
  have H := @OreLocalization.Presented.presentedMonoid_mk_eq_of_presentedGroup_mk_eq_of_positive _ _ _ _ _ _ _ H2
  specialize H hde.1.1 (invRev_true_of_is_false hde.1.2.1)
  apply one_symm_is_really_the_same.mpr at H
  unfold BraidMonoidInf.mk
  erw [← H]
  congr 1
  simp [FreeGroup.invRev, invRev_remove_eq_reverse]

theorem solver_g_correct : solver_g a b ↔
  BraidGroupInf.mk (FreeGroup.mk a) =
  BraidGroupInf.mk (FreeGroup.mk b) := by
  constructor
  · exact solver_g_correct_one_direction
  exact solver_g_correct_other_direction

-- theorem solver_g_correct_cons {a b : (PresentedGroup Braid.braid_rels_coexeter) } :
--   solver_g (Classical.choose (Quot.exists_rep (Classical.choose (Quotient.exists_rep a))))
--     (Classical.choose (Quot.exists_rep (Classical.choose (Quotient.exists_rep b)))) ↔
--   a = b := by
--   have Ha' := (Classical.choose_spec (Quot.exists_rep (Classical.choose (Quotient.exists_rep a))))
--   have Hb' := (Classical.choose_spec (Quot.exists_rep (Classical.choose (Quotient.exists_rep b))))
--   have Ha'' := (Classical.choose_spec (Quotient.exists_rep a))
--   have Hb'' := (Classical.choose_spec (Quotient.exists_rep b))
--   constructor
--   · intro it
--     rw [← Ha'', ← Hb'']
--     rw [← Ha', ← Hb']
--     exact solver_g_correct_one_direction it
--   intro it
--   rw [← Ha'', ← Hb''] at it
--   rw [← Ha', ← Hb'] at it
--   exact solver_g_correct_other_direction it --sorry --exact solver_g_correct_other_direction

--start with elements of the free group
def solver_fg (a b : FreeGroup ℕ) : Bool := by
  apply @Quot.lift₂ _ _ _ FreeGroup.Red.Step FreeGroup.Red.Step solver_g _ _ a b
  · intro a1 b1 c1 relsy
    have HAC := Quot.sound relsy
    change FreeGroup.mk _ = FreeGroup.mk _ at HAC
    cases hi : solver_g a1 b1
    · symm
      apply eq_false_of_ne_true
      intro h1
      apply solver_g_correct_one_direction at h1
      rw [← HAC] at h1
      apply solver_g_correct_other_direction at h1
      aesop
    apply solver_g_correct.1 at hi
    symm
    apply solver_g_correct_other_direction
    rw [← HAC, hi]
  intro a1 b1 c1 relsy
  have HBC := Quot.sound relsy
  change FreeGroup.mk _ = FreeGroup.mk _ at HBC
  cases hi : solver_g a1 c1
  · symm
    apply eq_false_of_ne_true
    intro h1
    apply solver_g_correct_one_direction at h1
    rw [← HBC] at h1
    apply solver_g_correct_other_direction at h1
    aesop
  apply solver_g_correct.1 at hi
  symm
  apply solver_g_correct_other_direction
  rw [← HBC, hi]

theorem solver_fg_correct : solver_fg a b ↔
    BraidGroupInf.mk a =
    BraidGroupInf.mk b := by
  rcases Quot.exists_rep a with ⟨a, rfl⟩
  rcases Quot.exists_rep b with ⟨b, rfl⟩
  exact solver_g_correct

def braid_solver (a b : BraidGroupInf) : Bool := by
  apply Quotient.lift₂ solver_fg _ a b
  intro a b c d hac hbd
  have HAC := Quotient.sound hac
  change BraidGroupInf.mk a = BraidGroupInf.mk c at HAC
  have HBD := Quotient.sound hbd
  change BraidGroupInf.mk b = BraidGroupInf.mk d at HBD
  cases hi : solver_fg a b
  · symm
    apply eq_false_of_ne_true
    intro h1
    apply solver_fg_correct.1 at h1
    rw [← HAC, ← HBD] at h1
    apply solver_fg_correct.2 at h1
    aesop
  apply solver_fg_correct.1 at hi
  symm
  apply solver_fg_correct.2
  aesop

theorem braid_solver_correct {a b : BraidGroupInf} : braid_solver a b ↔ a = b := by
  rcases Quotient.exists_rep a with ⟨a, rfl⟩
  rcases Quotient.exists_rep b with ⟨b, rfl⟩
  exact solver_fg_correct


instance braid_decidable_helper :
    DecidableEq (BraidGroupInf) := by
  intro a b
  by_cases h : braid_solver a b = true
  · exact isTrue (braid_solver_correct.mp h)
  · exact isFalse (by
      intro hEq
      apply braid_solver_correct.mpr at hEq
      aesop)

def solver_nonsense (a b : BraidGroupInf) : Bool := a = b


open Braid in
#eval braid_solver (σ 1 * σ 2 * σ 1) (σ 2 * σ 1 * σ 2 * (σ 3)⁻¹* (σ 3))

open Braid in
#eval solver_nonsense ((σ 1 * σ 2 * σ 1)) ((σ 2 * σ 1 * σ 2)⁻¹)

#eval solver_g [(1, true), (2, true), (4, true), (1, true)]
  [(2, true), (1, true), (2, true), (4, true)]

def foo1 := (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true)]).1

#eval foo1
#exit
#show_braid_word_help ([[(3, true), (2, true), (0, false), (3, true)],
  [(3, true), (2, true), (3, true), (0, false)],
  [(2, true), (3, true), (2, true), (0, false)]] : List (List ((ℕ × Bool))))


#show_braid_word_help ([foo1,
  [(3, true), (2, true), (3, true), (0, false)],
  [(2, true), (3, true), (2, true), (0, false)]] : List (List ((ℕ × Bool))))

#eval (reverse_complex [(3, false), (1, true), (2, true), (1, true)]).1
#show_braid_word_help ([(reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1, []] : List (List (ℕ × Bool)))
#eval (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1
#eval (reverse_complex [(3, false), (2, true), (2, true), (1, true)]).1.length
#eval (reverse_complex [(2, false), (2, false), (1, false), (1, false), (2, true), (2, true), (1, true), (1, true)]).1.length
#eval (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (4, true), (4, true)]).1.length
#eval (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1.length

#eval (reverse_complex [(0, false), (0, false), (1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1

#eval (reverse_complex [(1, false), (2, false), (2, false), (3, true), (4, true)]).1.length

-- set_option pp.proofs true in
-- def Quotient.exists_rep_C (a : Quotient new_rels) :
--   Σ b, PLift (Quotient.mk new_rels b = a) := by
--   --apply @Quotient.ind _ _ (fun x => Σ b, PLift (Quotient.mk new_rels b = x))
--   apply @Quot.hrecOn _ _ (fun x => Σ b, PLift (Quotient.mk new_rels b = x))
--      a (fun c => by use c; constructor; rfl)
--   intro a b hab
--   have H := Quotient.sound hab

--   -- unfold HEq
--   -- simp [H]
--   sorry



-- #check Quot.rec
-- noncomputable def braid_solver (a b : Braid.braid_group_inf) : Bool := by
--   rcases Quotient.exists_rep_C a with ⟨a1, ⟨ha1⟩⟩
--   rcases Quotient.exists_rep_C b with ⟨b1, ⟨hb1⟩⟩
--   sorry



  -- have hb := Classical.choose (Quotient.exists_rep b)
  -- have ha1 := Classical.choose (Quot.exists_rep ha)
  -- have hb1 := Classical.choose (Quot.exists_rep hb)
  -- exact solver_g ha1 hb1


#check Classical.choose
