import BraidProject.SemiThue
import BraidProject.Shortlex
import BraidProject.ListFact

import BraidProject.AlphabetRel

inductive reversing : List (ℕ × Bool) → List (ℕ × Bool) → Prop
| basic {n : ℕ} : reversing [(n, false), (n, true)] []
| apart {i j : ℕ} (h : Nat.dist i j > 1) : reversing [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : reversing [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

inductive reversing_option : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Prop
| basic {n : ℕ} : reversing_option [(n, false), (n, true)] []
| apart {i j : ℕ} (h : Nat.dist i j > 1) : reversing_option [(i, false), (j, true)]
    [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : reversing_option [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

inductive grid_style' : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Prop
| basic (n : ℕ) : grid_style' [(some n, false), (some n, true)] [(none, true), (none, false)]
| over (n : ℕ) : grid_style' [(n, false), (none, true)] [(none, true), (n, false)]
| up (n : ℕ) : grid_style' [(none, false), (some n, true)] [(n, true), (none, false)]
| empty : grid_style' [(none, false), (none, true)] [(none, true), (none, false)]
| apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style' [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style' [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

theorem List.map_eq_two (h : [a, b] = List.map f c) : ∃ d e, c = [d, e] ∧ f d = a ∧ f e = b := by
    have part_one := congr_arg List.length h
    simp at part_one
    have H2 := List.length_eq_two.mp part_one.symm
    rcases H2 with ⟨a1, a2, a_is⟩
    rw [a_is] at h
    simp at h
    rw [a_is]
    use a1, a2
    constructor
    · rfl
    exact ⟨h.1.symm, h.2.symm⟩

theorem List.length_eq_four {l : List α} : l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d] :=
  ⟨fun _ => let [a, b, c, d] := l; ⟨a, b, c, d, rfl⟩, fun ⟨_, _, _, _, e⟩ => e ▸ rfl⟩

theorem List.map_eq_four (h : [a, b, c, d] = List.map f e) : ∃ i j k l, e = [i, j, k, l] ∧
    f i = a ∧ f j = b ∧ f k = c ∧ f l = d := by
  have part_one := congr_arg List.length h
  simp at part_one
  have H2 := List.length_eq_four.mp part_one.symm
  rcases H2 with ⟨a1, a2, a3, a4, a_is⟩
  rw [a_is] at h
  simp at h
  rw [a_is]
  use a1, a2, a3, a4
  constructor
  · rfl
  exact ⟨h.1.symm, ⟨h.2.1.symm, ⟨h.2.2.1.symm, h.2.2.2.symm⟩⟩⟩

theorem prod_some (h : (some i.1, i.2) = (some j, b)) : i = (j, b) := by
  simp at h
  rw [← h.1, ← h.2]

theorem reversing_iff_option : reversing a b ↔ reversing_option (List.map (fun (x, y) =>
    (some x, y)) a) (List.map (fun (x, y) => (some x, y)) b) := by
  constructor
  · intro h
    induction h
    · exact reversing_option.basic
    · exact reversing_option.apart (by assumption)
    exact reversing_option.close (by assumption)
  intro h
  have H : ∀ m n, reversing_option m n → m = List.map (fun x ↦ (some x.1, x.2)) a →
      n = (List.map (fun x ↦ (some x.1, x.2)) b) → reversing a b := by
    intro m n
    intro h
    induction h
    · intro m_is n_is
      rename_i k
      have ha : a = [(k, false), (k, true)] := by
        have part_one := congr_arg List.length m_is
        simp at part_one
        have H2 := List.length_eq_two.mp part_one.symm
        rcases H2 with ⟨a1, a2, a_is⟩
        rw [a_is] at m_is
        simp at m_is
        rw [a_is]
        apply List.cons_eq_cons.mpr
        constructor
        · ext
          · exact m_is.1.1.symm
          exact m_is.1.2
        simp
        ext
        · exact m_is.2.1.symm
        exact m_is.2.2
      rw [ha, List.map_eq_nil_iff.mp n_is.symm]
      exact reversing.basic
    · intro h1 h2
      rcases List.map_eq_two h1 with ⟨d, e, hde⟩
      rcases List.map_eq_two h2 with ⟨f, g, hfg⟩
      rw [hde.1, hfg.1]
      rw [prod_some hde.2.1, prod_some hde.2.2, prod_some hfg.2.1, prod_some hfg.2.2]
      exact reversing.apart (by assumption)
    intro h
    rcases List.map_eq_two h with ⟨d, e, hde⟩
    rw [hde.1]
    rename_i i j dist
    rw [prod_some hde.2.1, prod_some hde.2.2]
    intro hb
    rcases List.map_eq_four hb with ⟨i, j, k, l, hijkl⟩
    rw [hijkl.1, prod_some hijkl.2.1, prod_some hijkl.2.2.1, prod_some hijkl.2.2.2.1,
      prod_some hijkl.2.2.2.2]
    exact reversing.close dist
  exact H _ _ h rfl rfl

def remove_ones : List (Option α × Bool) → List (α × Bool) :=
  fun a => match a with
  | [] => []
  | (some a, b) :: c => (a, b) :: remove_ones c
  | (none, _) :: c => remove_ones c

@[simp]
theorem remove_ones_nil : remove_ones ([] : List (Option α × Bool)) = [] := rfl

theorem reversing_iff_option_other_way : reversing_option a b → reversing (remove_ones a) (remove_ones b) := by
    intro h
    induction h
    · simp only [remove_ones]
      exact reversing.basic
    · simp only [remove_ones]
      exact reversing.apart (by assumption)
    simp only [remove_ones]
    exact reversing.close (by assumption)

def insert_one (a : Option ℕ × Bool) (L : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
  match L with
  | [] => [a]
  | (none, true) :: tail =>
    match a with
    | (_, true) => a :: L
    | (_, false)=> (none, true) :: insert_one a tail
  | (none, false) :: tail => a :: (none, false) :: tail
  | (some b, true) :: tail =>
    match a with
    | (none, true) => a :: L
    | (none, false) => (some b, true) :: insert_one a tail
    | (_, _) => a :: L
  | _ => a :: L

def move_ones_ind (L : List (Option ℕ × Bool)) :=
  match L with
  | [] => []
  | head :: tail => insert_one head (move_ones_ind tail)

@[simp]
theorem insert_one_nil : insert_one a [] = [a] := rfl
@[simp]
theorem moves_ones_nil : move_ones_ind [] = [] := rfl

@[simp]
theorem move_ones_singleton : move_ones_ind [a] = [a] := by
  unfold move_ones_ind
  unfold insert_one
  simp

theorem lt_of_none_true (h : lt_a a (none, true)) : a = (none, true) := by
  match a with
  | (none, true) => rfl
  | (_, false) => simp [lt_a] at h
  | (some a, true) => simp [lt_a] at h


theorem move_ones_pair (h : lt_a a b) : move_ones_ind [a, b] = [a, b] := by
  unfold move_ones_ind
  simp
  unfold insert_one
  split
  · aesop
  · rename_i _ _ h2
    simp at h2
    rw [h2.2, h2.1]
    rw [h2.1] at h
    apply lt_of_none_true at h
    rw [h]
  all_goals
    rename_i h1
    simp at h1
    simp [h1]
  · split
    any_goals rfl
    rw [h1.1] at h
    simp [lt_a] at h

def pairsTogether  (L : List (Option ℕ × Bool)) := ∀ a b, [(a, false), (b, true)] <:+: remove_ones L →
    [(some a, false), (some b, true)] <:+: L

theorem pairsTogether_empty : pairsTogether [] := by unfold pairsTogether; simp

theorem pairs_together_singleton : pairsTogether [a] := by
  intro c d hcd
  exfalso
  match a with
  | (none, _) =>
    change [(c, false), (d, true)] <:+: [] at hcd
    simp at hcd
  | (some a, b) =>
    change [(c, false), (d, true)] <:+: [(a, b)] at hcd
    rcases hcd with ⟨w, t, hwt⟩
    apply congr_arg List.length at hwt
    simp at hwt
    omega

@[simp]
theorem insert_one_singleton : insert_one (none, true) L = (none, true) :: L := by
  induction L
  · rfl
  conv => lhs; unfold insert_one
  rename_i head tail ih
  split
  all_goals aesop

@[simp]
theorem insert_one_none_true : insert_one (none, true) L = (none, true) :: L := by
  induction L
  · rfl
  conv => lhs; unfold insert_one
  rename_i head tail ih
  split
  all_goals aesop

-- @[simp]
-- theorem insert_one_to_none_true : insert_one a ((none, true) :: L) = (none, true) :: (insert_one a L) := by
--   match a with
--   | (_, true) =>
--     simp [insert_one]
--     sorry -- this should be easy
--   | (_, false) => rfl

@[simp]
theorem insert_one_to_none_false : insert_one a ((none, false) :: tail) = a :: ((none, false) :: tail) := by rfl

@[simp]
theorem insert_one_some_some : insert_one (some a1, b1) ((some a2, b2) :: tail) = (some a1, b1) :: (some a2, b2) :: tail := by
  unfold insert_one
  split
  all_goals aesop

theorem insert_one_length (h : L.length = n) : (insert_one a L).length = n + 1 := by
  induction L generalizing n
  · simp [h]
  simp at h
  rename_i ht tt htt
  specialize @htt (tt.length) rfl
  match a with
  | (none, true) =>
    simp [insert_one_none_true, h]
  | (none, false) =>
    match ht with
    | (none, true) => simp [htt, h, insert_one]
    | (none, false) => simp [h]
    | (some c, true) => simp [insert_one, htt, h]
    | (some c, false) => simp [insert_one, htt, h]
  | (some a, true) =>
    match ht with
    | (none, true) => simp [htt, h, insert_one]
    | (none, false) => simp [h]
    | (some c, true) => simp [insert_one, htt, h]
    | (some c, false) => simp [insert_one, htt, h]
  | (some a, false) =>
      match ht with
    | (none, true) => simp [htt, h, insert_one]
    | (none, false) => simp [h]
    | (some c, true) => simp [insert_one, htt, h]
    | (some c, false) => simp [insert_one, htt, h]

theorem move_ones_ind_length : (move_ones_ind L).length = L.length := by
  induction L
  · rfl
  unfold move_ones_ind
  rename_i ih
  simp [insert_one_length, ih]


theorem move_ones_none_true : move_ones_ind ((none, true)::a) = (none, true) :: move_ones_ind a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    conv => lhs; unfold move_ones_ind
    simp

theorem insert_none_false_end : insert_one a (L ++ [(none, false)]) = insert_one a L ++ [(none, false)] := by
  have H : ∀ t a L, L.length = t → insert_one a (L ++ [(none, false)]) = insert_one a L ++ [(none, false)] := by
    intro t
    induction t with
    | zero =>
      intro a L len
      simp at len
      simp [len]
    | succ n ih =>
      intro a L len
      match a with
      | (none, true) =>
        simp
      | (none, false) =>
        match L with
        | [] => simp
        | (none, true) :: tail =>
          simp [insert_one]
          apply ih
          simp at len
          exact len
        | (none, false) :: tail =>
          simp [insert_one]
        | (some c, true) :: tail1 =>
          simp [insert_one]
          apply ih
          simp at len
          exact len
        | (some c, false) :: tail1 =>
          simp [insert_one]
      | (some b, true) =>
        match L with
        | [] => simp
        | (none, true) :: tail => simp [insert_one]
        | (none, false) :: tail => simp [insert_one]
        | (some c, true) :: tail1 => simp [insert_one]
        | (some c, false) :: tail1 => simp [insert_one]
      | (some b, false) =>
        match L with
        | [] => simp
        | (none, true) :: tail =>
          simp [insert_one]
          apply ih
          simp at len
          exact len
        | (none, false) :: tail => simp [insert_one]
        | (some c, true) :: tail1 => simp [insert_one]
        | (some c, false) :: tail1 => simp [insert_one]
  exact H _ _ _ rfl

theorem move_ones_none_false_end : move_ones_ind (a ++ [(none, false)]) = move_ones_ind a ++ [(none, false)] := by
  induction a
  · simp
  simp [move_ones_ind]
  rename_i ih
  rw [ih, insert_none_false_end]

theorem infix_cons_cons_ne (h : a :: b <:+: c :: d) (ne : a ≠ c) : a :: b <:+: d := by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp at hwt
    exact (ne hwt.1).elim
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    use tail, t
    exact hwt.2

theorem infix_cons_cons_ne_double (h : [a, b] <:+: c1 :: c2 :: d) (ne : b ≠ c2) : [a, b] <:+: c2 :: d := by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp at hwt
    exact (ne hwt.2.1).elim
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    use tail, t
    exact hwt.2

theorem infix_cons_cons_def (h : [a, b] <:+: c :: d :: e) : a = c ∧ b =d ∨  [a, b] <:+: d :: e:= by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp at hwt
    left
    exact ⟨hwt.1, hwt.2.1⟩
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    right
    use tail, t
    exact hwt.2

theorem infix_append_right (h : l1 <:+: l2) : l1 <:+: (l2 ++ l3) := by
  rcases h with ⟨w, t, hwt⟩
  use w, t ++ l3
  rw [← hwt]
  simp

theorem infix_append_left (h : l1 <:+: l2) : l1 <:+: (l3 ++ l2) := by
  rcases h with ⟨w, t, hwt⟩
  use l3 ++ w, t
  rw [← hwt]
  simp

theorem infix_length_le (h : l1 <:+: l2) : l1.length ≤ l2.length := by
  rcases h with ⟨w, t, hwt⟩
  apply congr_arg List.length at hwt
  simp at hwt
  omega

-- theorem move_ones_eq_cons (h : move_ones_ind L = a :: b) : ∃ L1, move_ones_ind L1 = b := by
--   induction L generalizing a b with
--   | nil => simp [move_ones] at h
--   | cons head tail ih =>
--     match h : move_ones_ind tail with
--     | [] =>
--       have H : b = [] := by sorry
--       use []
--       simp [H]
--     | a1 :: b1 =>
--       sorry

def irreducible (L : List (Option ℕ × Bool)) :=
  ∀ a, ¬ [(some a, false), (none, true)] <:+: L ∧ ¬ [(none, false), (some a, true)] <:+: L ∧
   ¬ [(none, false), (none, true)] <:+: L

theorem irreducible_nil : irreducible [] := by simp [irreducible]

theorem irreducible_singleton : irreducible [a] := by
  simp [irreducible]
  intro a
  constructor
  · intro h
    apply infix_length_le at h
    simp at h
  constructor
  · intro h
    apply infix_length_le at h
    simp at h
  intro h
  apply infix_length_le at h
  simp at h

theorem irreducible_rest (h : irreducible (head :: tail)) : irreducible tail := by
  intro a
  constructor
  · intro h1
    specialize h a
    apply h.1
    exact List.infix_cons h1
  constructor
  · intro h1
    specialize h a
    apply h.2.1
    exact List.infix_cons h1
  intro h1
  specialize h a
  apply h.2.2
  exact List.infix_cons h1

theorem irreducible_cons_true (h : irreducible L) : irreducible ((a, true) :: L) := by
  intro a
  constructor
  · intro h1
    specialize h a
    apply h.1
    apply infix_cons_cons_ne h1 (by simp)
  constructor
  · intro h1
    specialize h a
    apply h.2.1
    apply infix_cons_cons_ne h1 (by simp)
  intro h1
  specialize h a
  apply h.2.2
  apply infix_cons_cons_ne h1 (by simp)

theorem irreducible_two_cons (h : irreducible (b :: L)) (h1 : a.2 = b.2 ∨ a.2 = true ∨ (∃ c d, a.1 = some c ∧ b.1 = some d)) :
    irreducible (a :: b :: L) := by
  intro a1
  rcases h1 with h1 | h2 | ⟨c, d, hcd⟩
  · constructor
    · intro h2
      specialize h a1
      apply h.1
      match hb : a with
      | (_, true) =>
        apply infix_cons_cons_ne h2
        simp [hb]
      | (_, false) =>
        match hbb : b with
        | (_, true) => simp at h1
        | (_, false) =>
          apply infix_cons_cons_ne_double h2
          simp
    constructor
    · intro h2
      specialize h a1
      apply h.2.1
      match hb : a with
      | (_, true) =>
        apply infix_cons_cons_ne h2
        simp [hb]
      | (_, false) =>
        match b with
        | (_, true) => simp at h1
        | (_, false) =>
          apply infix_cons_cons_ne_double h2
          simp
    intro h2
    specialize h a1
    apply h.2.2
    match hb : a with
    | (_, true) =>
      apply infix_cons_cons_ne h2
      simp [hb]
    | (_, false) =>
      match hbb : b with
      | (_, true) => simp at h1
      | (_, false) =>
        apply infix_cons_cons_ne_double h2
        simp
  · match a with
    | (fst, true) =>
      constructor
      · intro h3
        apply (h a1).1
        exact infix_cons_cons_ne h3 (by simp)
      constructor
      · intro h3
        apply (h a1).2.1
        exact infix_cons_cons_ne h3 (by simp)
      intro h3
      apply (h a1).2.2
      exact infix_cons_cons_ne h3 (by simp)
    | (fst, false) => simp at h2
  match ha : a with
  | (some a2, true) =>
    match b with
    | (some b2, _) =>
      constructor
      · intro h3
        apply (h a1).1
        apply infix_cons_cons_ne h3 (by simp)
      constructor
      · intro h3
        apply (h a1).2.1
        apply infix_cons_cons_ne h3 (by simp)
      intro h3
      apply (h a1).2.2
      apply infix_cons_cons_ne h3 (by simp)
    | (none, _) => simp at hcd
  | (some a2, false) =>
    match b with
    | (some b2, _) =>
      constructor
      · intro h3
        apply (h a1).1
        apply infix_cons_cons_ne_double h3 (by simp)
      constructor
      · intro h3
        apply (h a1).2.1
        apply infix_cons_cons_ne h3 (by simp)
      intro h3
      apply (h a1).2.2
      apply infix_cons_cons_ne h3 (by simp)
    | (none, _) => simp at hcd
  | (none, _) => simp at hcd


theorem irreducible_insert (h : irreducible L) : irreducible (insert_one a L) := by
  have H : ∀ t a L, L.length = t → irreducible L → irreducible (insert_one a L) := by
    intro t
    induction t with
    | zero =>
      intro a L len
      simp at len
      simp [len]
      intro h
      exact irreducible_singleton
    | succ n ih =>
      intro a L m irr
      match a with
      | (none, true) =>
        simp [insert_one]
        exact irreducible_cons_true irr
      | (none, false) =>
        match hl : L with
        | [] => simp [irreducible_singleton]
        | (none, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_cons_true (ih _ _ m (irreducible_rest irr))
        | (none, false) :: tail =>
          simp only [insert_one]
          exact irreducible_two_cons irr (Or.inl (by rfl))
        | (some b, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_cons_true (ih _ _ m (irreducible_rest irr))
        | (some b, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr (Or.inl (by rfl))
      | (some b, true) =>
        match hl : L with
        | [] => simp [irreducible_singleton]
        | (none, true) :: tail =>
          simp only [insert_one]
          simp at m
          apply irreducible_two_cons
          · apply irreducible_cons_true
            exact irreducible_rest irr
          left; rfl
        | (none, false) :: tail =>
          simp only [insert_one]
          exact irreducible_two_cons irr (Or.inr (Or.inl (by rfl)))
        | (some b, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_two_cons irr (Or.inr (Or.inl (by rfl)))
        | (some b, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr
          right; left; rfl
      | (some c, false) =>
        match hl : L with
        | [] => simp [irreducible_singleton]
        | (none, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_cons_true (ih _ _ m (irreducible_rest irr))
        | (none, false) :: tail =>
          simp only [insert_one]
          exact irreducible_two_cons irr (Or.inl (by rfl))
        | (some b, true) :: tail =>
          simp only [insert_one]
          simp at m
          apply irreducible_two_cons irr
          right; right
          use c
          use b
        | (some b, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr (Or.inl (by rfl))
  exact H _ _ _ rfl h

theorem big_attempt : irreducible (move_ones_ind L) := by
  induction L
  · simp [irreducible_nil]
  rename_i head tail ih
  unfold move_ones_ind
  exact irreducible_insert ih

theorem insert_irreducible (h : irreducible (head :: tail)) : insert_one head tail = head :: tail := by
  match head with
  | (none, true) => simp [insert_one]
  | (none, false) =>
    match hl : tail with
    | [] => simp [irreducible_singleton]
    | (none, true) :: tail =>
      simp only [insert_one]
      exfalso
      apply (h 0).2.2
      use [], tail
      rfl
    | (none, false) :: tail => simp only [insert_one]
    | (some b, true) :: tail =>
      simp only [insert_one]
      exfalso
      apply (h b).2.1
      use [], tail
      rfl
    | (some b, false) :: tail =>
      simp only [insert_one]
  | (some b, true) =>
    match hl : tail with
    | [] => simp [irreducible_singleton]
    | (none, true) :: tail => simp only [insert_one]
    | (none, false) :: tail => simp only [insert_one]
    | (some b, true) :: tail => simp only [insert_one]
    | (some b, false) :: tail => simp only [insert_one]
  | (some c, false) =>
    match hl : tail with
    | [] => simp [irreducible_singleton]
    | (none, true) :: tail =>
      simp only [insert_one]
      exfalso
      apply (h c).1
      use [], tail
      rfl
    | (none, false) :: tail => simp only [insert_one]
    | (some b, true) :: tail => simp only [insert_one]
    | (some b, false) :: tail => simp only [insert_one]

theorem move_irreducible (h : irreducible L) : move_ones_ind L = L := by
  induction L
  · simp
  rename_i head tail ih
  simp [move_ones_ind]
  specialize ih (irreducible_rest h)
  rw [ih, insert_irreducible h]

theorem move_ones_ind_rep : move_ones_ind (move_ones_ind L) = move_ones_ind L := by
  apply move_irreducible
  exact big_attempt

theorem elem_of_infix (h : a <:+: b) (h1 : a1 ∈ a) : a1 ∈ b := by
  exact List.IsInfix.mem h1 h

theorem pt_true (h : pairsTogether L) : pairsTogether ((a, true) :: L) := by
  intro b c hbc
  match a with
  | none =>
    simp [remove_ones] at hbc
    specialize h _ _ hbc
    exact List.infix_cons h
  | some a1 =>
    simp [remove_ones] at hbc
    apply infix_cons_cons_ne at hbc
    simp at hbc
    specialize h _ _ hbc
    exact List.infix_cons h

theorem pt_some_false (h : pairsTogether ((some b, false) :: L)) : pairsTogether ((a, b0) :: (some b, false) :: L) := by
  intro c d hcd
  match a with
  | none =>
    simp [remove_ones] at hcd
    specialize h _ _ hcd
    exact List.infix_cons h
  | some a1 =>
    simp [remove_ones] at hcd
    match b0 with
    | true =>
      apply infix_cons_cons_ne at hcd
      simp at hcd
      exact List.infix_cons (h _ _ hcd)
    | false =>
      apply infix_cons_cons_ne_double at hcd
      simp at hcd
      exact List.infix_cons (h _ _ hcd)

theorem pt_nf_nf (h : pairsTogether ((none, false) :: L)) : pairsTogether ((none, false) :: (none, false) :: L) := by
  intro c d hcd
  have H : remove_ones ((none, false) :: (none, false) :: L) = remove_ones ((none, false) :: L) := rfl
  rw [H] at hcd
  specialize h _ _ hcd
  exact List.infix_cons h

-- theorem pt_less (h : pairsTogether (head :: tail)) : pairsTogether tail := by
--   intro c d hcd
--   have H := h c d
--   sorry

theorem irr_helper (h : irreducible ((none, false) :: tail)) (h2 : remove_ones tail = (a, true) :: rest) : False := by
  have H : ∀ t L rest, L.length = t → irreducible ((none, false) :: L) → remove_ones L = (a, true) :: rest → False := by
    intro t
    induction t with
    | zero =>
      intro L rest len irr hin
      simp at len
      simp [len, remove_ones] at hin
    | succ n ih =>
      intro L rest len irr hin
      match L with
      | [] => simp at len
      | (none, true) :: tail1 =>
        apply (irr 0).2.2
        use [], tail1
        simp
      | (none, false) :: tail1 =>
        simp [remove_ones] at hin
        specialize ih tail1 rest
        simp at len
        exact ih len (irreducible_rest irr) hin
      | (some b, true) :: tail1 =>
        apply (irr b).2.1
        use [], tail1
        simp
      | (some b, false) :: tail1 => simp [remove_ones] at hin
  exact H _ _ _ rfl h h2

theorem funky_helper (irr : irreducible ((none, false) :: L)) (hin : [(c, false), (d, true)] <:+: (b, false) :: remove_ones L) :
    [(c, false), (d, true)] <:+: remove_ones L := by
  match hl : remove_ones L with
  | [] =>
    rw [hl] at hin
    apply infix_length_le at hin
    simp at hin
  | (a, true) :: tail =>
    exact (irr_helper irr hl).elim
  | (a, false) :: tail =>
    rw [hl] at hin
    apply infix_cons_cons_ne_double at hin
    simp at hin
    exact hin

theorem pt_of_irr (h : irreducible L) : pairsTogether L := by
  have H : ∀ t L, L.length ≤ t → irreducible L → pairsTogether L := by
    intro t
    induction t
    · intro L len
      simp at len
      intro h
      rw [len]
      exact pairsTogether_empty
    rename_i n ih
    intro L len irr c d h
    cases L with
    | nil =>
      apply infix_length_le at h
      simp at h
    | cons head tail =>
      match head with
      | (none, true) =>
        simp [remove_ones] at h
        simp at len
        exact List.infix_cons <| ih tail len (irreducible_rest irr) c d h
      | (none, false) =>
        match tail with
        | [] =>
          apply infix_length_le at h
          simp [remove_ones] at h
        | (none, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          exact ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) c d h
        | (none, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          exact ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) c d h
        | (some e, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply ih ((some e, true) :: tail1)
          · simp [len]
          apply irreducible_rest irr
          exact h
        | (some e, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply ih ((some e, false) :: tail1)
          · simp [len]
          apply irreducible_rest irr
          exact h
      | (some b, true) =>
        match tail with
        | [] =>
          apply infix_length_le at h
          simp [remove_ones] at h
        | (none, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          apply infix_cons_cons_ne at h
          simp at h
          exact h
        | (none, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          apply infix_cons_cons_ne at h
          simp at h
          exact h
        | (some e, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          apply infix_cons_cons_ne at h
          simp at h
          apply infix_cons_cons_ne at h
          simp at h
          exact h
        | (some c, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply ih ((some c, false) :: tail1)
          · simp [len]
          apply irreducible_rest irr
          apply infix_cons_cons_ne at h
          simp at h
          exact h
      | (some b, false) =>
        match tail with
        | [] =>
          apply infix_length_le at h
          simp [remove_ones] at h
        | (none, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          specialize irr b
          exfalso
          apply irr.1
          use [], tail1
          simp
        | (none, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          exact funky_helper (irreducible_rest irr) h
        | (some e, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          have H : (c = b ∧ e = d) ∨ (c ≠ b ∨ e ≠ d) := by
            rcases eq_or_ne c b with h1 | h2
            · rcases eq_or_ne e d with h3 | h4
              · left; simp [h1, h3]
              right; simp [h4]
            right; simp [h2]
          rcases H with h1 | h2 | h3
          · rw [h1.1, h1.2]
            use [], tail1
            simp
          · apply infix_cons_cons_ne at h
            simp [h2] at h
            apply infix_cons_cons_ne at h
            simp at h
            apply List.infix_cons
            apply List.infix_cons
            apply ih tail1 (by omega) (irreducible_rest (irreducible_rest irr))
            exact h
          apply infix_cons_cons_ne_double at h
          simp [h3.symm] at h
          apply infix_cons_cons_ne at h
          simp at h
          apply List.infix_cons
          apply List.infix_cons
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          exact h
        | (some e, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply ih ((some e, false) :: tail1) (by simp [len]) (irreducible_rest irr)
          apply infix_cons_cons_ne_double at h
          simp at h
          exact h
  exact H L.length L (by simp) h

theorem pt_move_ones : pairsTogether (move_ones_ind L) := pt_of_irr big_attempt

theorem equiv_insert : SemiThue grid_style' (a :: L) (insert_one a L) := by
  have H : ∀ t L a, L.length ≤ t → SemiThue grid_style' (a :: L) (insert_one a L) := by
    intro t
    induction t
    · intro L a len
      simp at len
      rw [len]
      exact SemiThue.refl [a]
    rename_i n ih
    intro L a len
    match a with
    | (none, true) =>
      simp
      exact SemiThue.refl ((none, true) :: L)
    | (none, false) =>
      match L with
      | [] => exact SemiThue.refl [(none, false)]
      | (none, true) :: tail =>
        simp at len
        exact SemiThue.trans _ _ _ (SemiThue_append_right (SemiThue_rel grid_style'.empty)) (SemiThue_cons (ih tail _ len))
      | (none, false) :: tail => exact SemiThue.refl ((none, false) :: (none, false) :: tail)
      | (some c, true) :: tail1 =>
        simp at len
        specialize ih tail1 (none, false) len
        exact SemiThue.trans _ _ _ (SemiThue_append_right (SemiThue_rel (grid_style'.up c))) (SemiThue_cons ih)
      | (some c, false) :: tail1 =>
        exact SemiThue.refl ((none, false) :: (some c, false) :: tail1)
    | (some b, true) =>
      match L with
      | [] => exact SemiThue.refl _
      | (none, true) :: tail => exact SemiThue.refl _
      | (none, false) :: tail => exact SemiThue.refl _
      | (some c, true) :: tail1 => exact SemiThue.refl _
      | (some c, false) :: tail1 => exact SemiThue.refl _
    | (some b, false) =>
      match L with
      | [] => exact SemiThue.refl _
      | (none, true) :: tail =>
        simp at len
        specialize ih tail (some b, false) len
        exact SemiThue.trans _ _ _ (SemiThue_append_right (SemiThue_rel (grid_style'.over b))) (SemiThue_cons ih)
      | (none, false) :: tail => exact SemiThue.refl _
      | (some c, true) :: tail1 => exact SemiThue.refl _
      | (some c, false) :: tail1 => exact SemiThue.refl _
  exact H L.length _ _ (by simp)


theorem equiv_move_ones : SemiThue grid_style' L (move_ones_ind L) := by
  induction L
  · exact SemiThue.refl []
  rename_i head tail ih
  exact SemiThue.trans _ _ _ (SemiThue_cons ih) (equiv_insert)

@[simp]
theorem remove_ones_insert_ones : remove_ones (insert_one (none, b) L) = remove_ones L := by
  induction L
  · simp [remove_ones]
  rename_i head tail ih
  match head with
  | (none, true) =>
    cases b
    all_goals
    simp [insert_one, remove_ones, ih]
  | (none, false) => simp [insert_one, remove_ones, ih]
  | (some a, true) =>
    cases b
    all_goals
    simp [insert_one, remove_ones, ih]
  | (some a, false) => simp [insert_one, remove_ones, ih]

@[simp]
theorem remove_ones_insert_some : remove_ones (insert_one (some a, b) L) = (a, b) :: remove_ones L := by
  induction L
  · simp [remove_ones]
  rename_i head tail ih
  match head with
  | (none, true) =>
    cases b
    all_goals
    simp [insert_one, remove_ones, ih]
  | (none, false) => simp [insert_one, remove_ones, ih]
  | (some a, true) =>
    cases b
    all_goals
    simp [insert_one, remove_ones, ih]
  | (some a, false) => simp [insert_one, remove_ones, ih]

theorem remove_ones_move_ones : remove_ones (move_ones_ind L) = remove_ones L := by
  induction L
  · simp
  rename_i head tail ih
  match head with
  | (none, true) => simp [move_ones_ind, remove_ones, ih]
  | (none, false) =>
    simp [remove_ones, move_ones_ind, ih]
  | (some a, true) => simp [move_ones_ind, remove_ones, ih]
  | (some a, false) => simp [move_ones_ind, remove_ones, ih]

theorem remove_ones_append : remove_ones (L1 ++ L2) = remove_ones L1 ++ remove_ones L2 := by
  induction L1
  · simp
  rename_i head tail ih
  match head with
  | (none, _) => simp [remove_ones, ih]
  | (some _, _) => simp [remove_ones, ih]

-- theorem helper : reversing_option a b → ∃ a' b', SemiThue grid_style' a' b' ∧
--   remove_ones a' = remove_ones a ∧ remove_ones b' = remove_ones b := by
--   intro h
--   cases h with
--   | basic =>
--     rename_i n
--     have H := @SemiThue.reduction _ _ _ _ [] [] (grid_style'.basic n)
--     simp at H
--     use [(some n, false), (some n, true)]
--     use [(none, true), (none, false)]
--     exact ⟨H, ⟨rfl, rfl⟩⟩
--   | apart h =>
--     have H := @SemiThue.reduction _ _ _ _ [] [] (grid_style'.apart h)
--     simp at H
--     rename_i i j
--     use [(some i, false), (some j, true)]
--     use [(some j, true), (some i, false)]
--   | close h =>
--     have H := @SemiThue.reduction _ _ _ _ [] [] (grid_style'.close h)
--     simp at H
--     rename_i i j
--     use [(some i, false), (some j, true)]
--     use [(some j, true), (some i, true), (some j, false), (some i, false)]

-- theorem helper' : reversing a b → ∃ a' b', SemiThue grid_style' a' b' ∧
--   remove_ones a' = a ∧ remove_ones b' = b := by
--   intro h
--   cases h with
--   | basic =>
--     rename_i n
--     have H := @SemiThue.reduction _ _ _ _ [] [] (grid_style'.basic n)
--     simp at H
--     use [(some n, false), (some n, true)]
--     use [(none, true), (none, false)]
--     exact ⟨H, ⟨rfl, rfl⟩⟩
--   | apart h =>
--     have H := @SemiThue.reduction _ _ _ _ [] [] (grid_style'.apart h)
--     simp at H
--     rename_i i j
--     use [(some i, false), (some j, true)]
--     use [(some j, true), (some i, false)]
--     exact ⟨H, ⟨rfl, rfl⟩⟩
--   | close h =>
--     have H := @SemiThue.reduction _ _ _ _ [] [] (grid_style'.close h)
--     simp at H
--     rename_i i j
--     use [(some i, false), (some j, true)]
--     use [(some j, true), (some i, true), (some j, false), (some i, false)]
--     exact ⟨H, ⟨rfl, rfl⟩⟩


def to_option (L : List (ℕ × Bool)) : List (Option ℕ × Bool) := (List.map (fun x ↦ (some x.1, x.2)) L)

theorem remove_map_helper {a : List (ℕ × Bool)} : remove_ones (to_option a) = a := by
  induction a
  · rfl
  rename_i ih
  simp [to_option, remove_ones]
  exact ih

theorem rg_of_rev_rel (d1) (h : SemiThue reversing g (e ++ (remove_ones d1) ++ f)) (gr : SemiThue grid_style' a' b') (a'_is : remove_ones a' = g)
    (b'_is : remove_ones b' = e ++ [(c1, false), (c2, true)] ++ f) (pt_b : pairsTogether b') (rel_holds : grid_style' [(some c1, false), (some c2, true)] d1): ∃ a' b', SemiThue grid_style' a' b' ∧
    remove_ones a' = g ∧ remove_ones b' = e ++ (remove_ones d1) ++ f ∧ pairsTogether b' := by
    rcases pt_b c1 c2 (by use e; use f; exact b'_is.symm) with ⟨w, t, hwt⟩
    use a'
    rw [← hwt] at b'_is
    rw [remove_ones_append, remove_ones_append] at b'_is
    have splits : (remove_ones w = e ∧ remove_ones t = f) ∨
      (∃ w1 w2, w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = remove_ones w1 ∧ f = remove_ones w2 ++ [(c1, false), (c2, true)] ++ remove_ones t) ∨
      (∃ t1 t2, t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧ e = remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t1 ∧ f = remove_ones t2) := by sorry
    simp only [remove_ones] at b'_is
    rcases splits with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
    · use move_ones_ind (w ++ d1 ++ t)
      constructor
      · apply SemiThue.trans _ _ _ gr
        have H : SemiThue grid_style' b' (w ++ d1 ++ t) := by
          rw [← hwt]
          apply SemiThue.reduction
          exact rel_holds
        apply SemiThue.trans _ _ _ H
        exact equiv_move_ones
      constructor
      · exact a'_is
      constructor
      · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, h2.1, h2.2]
        --simp [remove_ones]
      exact pt_move_ones
    · use move_ones_ind (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
      constructor
      · apply SemiThue.trans _ _ _ gr
        rw [← hwt]
        have H : SemiThue grid_style' (w ++ [(some c1, false), (some c2, true)] ++ t)
          (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t) := by
          apply SemiThue_append_right
          rw [hw.1]
          apply SemiThue_append_right
          apply SemiThue_append_right
          apply SemiThue_append_left
          apply SemiThue_rel
          exact rel_holds
        apply H.trans
        exact equiv_move_ones
      constructor
      · exact a'_is
      constructor
      · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, hw.2.1, hw.2.2]
        simp [remove_ones, remove_ones_append]
      exact pt_move_ones
    use move_ones_ind (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
    constructor
    · apply SemiThue.trans _ _ _ gr
      rw [← hwt]
      have H : SemiThue grid_style' (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2) := by
        rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
        apply SemiThue_append_left
        rw [List.append_assoc, List.append_assoc] at ht
        rw [ht.1]
        apply SemiThue_append_left
        apply SemiThue_append_left
        apply SemiThue_append_right
        apply SemiThue_rel
        exact rel_holds
      apply H.trans
      exact equiv_move_ones
    constructor
    · exact a'_is
    constructor
    · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, ht.2.1, ht.2.2]
      simp [remove_ones, remove_ones_append]
    exact pt_move_ones

theorem rev_to_grid (h : SemiThue reversing a b) : ∃ a' b', SemiThue grid_style' a' b' ∧
  remove_ones a' = a ∧ remove_ones b' = b ∧ pairsTogether b':= by
  induction one_step_equiv_reg.mp h with
  | refl a =>
    use to_option a
    use to_option a
    constructor
    · exact SemiThue.refl _
    constructor
    · exact remove_map_helper
    constructor
    · exact remove_map_helper
    intro c d rm
    rw [remove_map_helper] at rm
    rcases rm with ⟨w, t, hwt⟩
    use to_option w
    use to_option t
    rw [← hwt]
    simp [to_option]
  | one_step h1 h2 ih =>
    rename_i c d e f g
    specialize ih (one_step_equiv_reg.mpr h1)
    rcases ih with ⟨a', b', gr, a'_is, b'_is, pt_b⟩
    cases h2 with
    | basic =>
      exact rg_of_rev_rel ([(none, true), (none, false)]) h gr a'_is b'_is pt_b (grid_style'.basic _)
    | apart h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, false)]) h gr a'_is b'_is pt_b (grid_style'.apart h_dist)
    | close h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, true), (some j, false), (some i, false)]) h gr a'_is b'_is pt_b (grid_style'.close h_dist)
