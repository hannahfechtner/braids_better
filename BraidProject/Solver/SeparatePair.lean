import BraidProject.TrueFalse_C

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

theorem separate_first_pair_cons_false(h : separate_first_pair L = (a, b, c)) :
    separate_first_pair ((d, false) :: L) = ((d, false) :: a, b, c) := by
  unfold separate_first_pair at *
  simp_all [separate_maximal_false_prefix]

theorem c_nil_of_separate_no_true (h : separate_first_pair L = (a, ([], c))) : c = [] := by
  induction L generalizing a c with
  | nil =>
    have H := separate_first_pair_correct []
    simp_all
  | cons head tail ih =>
    match head with
    | (d, false) =>
      have H := separate_first_pair_correct (head :: tail)
      simp_all only [List.append_assoc]
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

theorem separate_tail_length (h : separate_first_pair L = (a, b, c)) (hL : L.length > 0): c.length < L.length := by
  have H := separate_first_pair_correct L
  apply congr_arg List.length at H
  have H1 := separate_first_pair_length hL
  grind
