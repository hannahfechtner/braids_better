import BraidProject.SemiThue
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

def pts (L) := ∀ L1, L1 <:+: L → pairsTogether L1

theorem pairsTogether_empty : pairsTogether [] := by unfold pairsTogether; simp

theorem pts_empty : pts [] := by unfold pts; intro L1 hl; unfold pairsTogether; simp at hl; simp [hl]

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

-- theorem pairs_together'_singleton : pts [a] := by
--   intro L1 hl c d hcd
--   exfalso
--   sorry
  -- match a with
  -- | (none, _) =>
  --   change [(c, false), (d, true)] <:+: [] at hcd
  --   simp at hcd
  -- | (some a, b) =>
  --   change [(c, false), (d, true)] <:+: [(a, b)] at hcd
  --   rcases hcd with ⟨w, t, hwt⟩
  --   apply congr_arg List.length at hwt
  --   simp at hwt
  --   omega

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

theorem List.infix_singleton (h : L <:+: [a]) : L = [] ∨ L = [a] := by
  match L with
  | [] => left; rfl
  | head :: tail =>
    match tail with
    | [] =>
      right
      rcases h with ⟨w, t, hwt⟩
      have H := congr_arg List.length hwt
      simp at H
      have hw : w = [] := length_eq_zero.mp (by omega)
      have ht : t = [] := length_eq_zero.mp (by omega)
      rw [hw, List.nil_append, ht, List.append_nil] at hwt
      exact hwt
    | t1 :: t2 =>
      rcases h with ⟨w, t, hwt⟩
      have H := congr_arg List.length hwt
      simp at H
      omega

theorem List.infix_cons_concat (h : L <:+: a :: b ++ [c]) : L =  a :: b ++ [c] ∨ L <:+: a :: b ∨ L <:+: a :: b ++ [c] := by
  induction L
  · right; left; exact nil_infix
  rename_i head tail ih
  rcases h with ⟨w, t, hwt⟩
  match w with
  | [] =>
    cases t using List.reverseRecOn
    · left; rw [List.append_nil, List.nil_append] at hwt; exact hwt
    rename_i tf tl _
    right; left
    use [], tf
    simp at hwt
    rw [hwt.1, List.nil_append]
    rw [← List.append_assoc, ← List.concat_eq_append, ← List.concat_eq_append] at hwt
    rw [← (List.concat_inj.mp hwt.2).1]
    rfl
  | w1 :: wr =>
    cases t using List.reverseRecOn
    · right; right; rw [List.append_nil] at hwt; simp at hwt; use a :: wr; use []; simp [hwt.2]
    rename_i tf tl _
    right; left
    use a :: wr, tf
    simp at hwt
    simp
    have H : wr ++ head :: (tail ++ (tf ++ [tl])) = wr ++ head :: tail ++ tf ++ [tl] := by simp
    rw [H] at hwt
    rw [← List.concat_eq_append, ← List.concat_eq_append] at hwt
    rw [← (List.concat_inj.mp hwt.2).1]
    simp

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

theorem pts_less (h : pts (a :: L)) : pts L := by
  intro L1 hl c d hcd
  exact h L1 (List.infix_cons hl) c d hcd

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

theorem List.infix_trans (h : L1 <:+: L2) (h2 : L2 <:+: L3) : L1 <:+: L3 := by
  rcases h with ⟨w1, t1, hwt1⟩
  rcases h2 with ⟨w2, t2, hwt2⟩
  rw [← hwt1] at hwt2
  use w2 ++ w1
  use t1 ++ t2
  rw [← hwt2]
  simp

theorem irr_infix (h : irreducible L) (h2 : L1 <:+: L) : irreducible L1 := by
  intro a
  constructor
  · exact fun ha => (h a).1 (List.infix_trans ha h2)
  constructor
  · exact fun ha => (h a).2.1 (List.infix_trans ha h2)
  exact fun ha => (h a).2.2 (List.infix_trans ha h2)

theorem pts_of_irr (h : irreducible L) : pts L := by
  intro L1 hl
  apply pt_of_irr
  exact irr_infix h hl
-- theorem irr_of_pt (h : pairsTogether L) : irreducible L := by
--   have H : ∀ t L, L.length ≤ t → pairsTogether L → irreducible L := by
--     intro t
--     induction t
--     · intro L len
--       simp at len
--       intro h
--       rw [len]
--       exact irreducible_nil
--     rename_i n ih
--     intro L len pt
--     cases L with
--     | nil =>
--       exact irreducible_nil
--     | cons head tail =>
--       match head with
--       | (none, true) =>
--         simp at len
--         apply irreducible_cons_true
--         apply ih _ len
--         exact List.infix_cons <| ih tail len (irreducible_rest irr) c d h
--       | (none, false) =>
--         match tail with
--         | [] =>
--           apply infix_length_le at h
--           simp [remove_ones] at h
--         | (none, true) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply List.infix_cons
--           exact ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) c d h
--         | (none, false) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply List.infix_cons
--           exact ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) c d h
--         | (some e, true) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply ih ((some e, true) :: tail1)
--           · simp [len]
--           apply irreducible_rest irr
--           exact h
--         | (some e, false) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply ih ((some e, false) :: tail1)
--           · simp [len]
--           apply irreducible_rest irr
--           exact h
--       | (some b, true) =>
--         match tail with
--         | [] =>
--           apply infix_length_le at h
--           simp [remove_ones] at h
--         | (none, true) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply List.infix_cons
--           apply ih tail1
--           · omega
--           apply irreducible_rest (irreducible_rest irr)
--           apply infix_cons_cons_ne at h
--           simp at h
--           exact h
--         | (none, false) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply List.infix_cons
--           apply ih tail1
--           · omega
--           apply irreducible_rest (irreducible_rest irr)
--           apply infix_cons_cons_ne at h
--           simp at h
--           exact h
--         | (some e, true) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply List.infix_cons
--           apply ih tail1
--           · omega
--           apply irreducible_rest (irreducible_rest irr)
--           apply infix_cons_cons_ne at h
--           simp at h
--           apply infix_cons_cons_ne at h
--           simp at h
--           exact h
--         | (some c, false) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply ih ((some c, false) :: tail1)
--           · simp [len]
--           apply irreducible_rest irr
--           apply infix_cons_cons_ne at h
--           simp at h
--           exact h
--       | (some b, false) =>
--         match tail with
--         | [] =>
--           apply infix_length_le at h
--           simp [remove_ones] at h
--         | (none, true) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply List.infix_cons
--           specialize irr b
--           exfalso
--           apply irr.1
--           use [], tail1
--           simp
--         | (none, false) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply List.infix_cons
--           apply ih tail1
--           · omega
--           apply irreducible_rest (irreducible_rest irr)
--           exact funky_helper (irreducible_rest irr) h
--         | (some e, true) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           have H : (c = b ∧ e = d) ∨ (c ≠ b ∨ e ≠ d) := by
--             rcases eq_or_ne c b with h1 | h2
--             · rcases eq_or_ne e d with h3 | h4
--               · left; simp [h1, h3]
--               right; simp [h4]
--             right; simp [h2]
--           rcases H with h1 | h2 | h3
--           · rw [h1.1, h1.2]
--             use [], tail1
--             simp
--           · apply infix_cons_cons_ne at h
--             simp [h2] at h
--             apply infix_cons_cons_ne at h
--             simp at h
--             apply List.infix_cons
--             apply List.infix_cons
--             apply ih tail1 (by omega) (irreducible_rest (irreducible_rest irr))
--             exact h
--           apply infix_cons_cons_ne_double at h
--           simp [h3.symm] at h
--           apply infix_cons_cons_ne at h
--           simp at h
--           apply List.infix_cons
--           apply List.infix_cons
--           apply ih tail1
--           · omega
--           apply irreducible_rest (irreducible_rest irr)
--           exact h
--         | (some e, false) :: tail1 =>
--           simp [remove_ones] at h
--           simp at len
--           apply List.infix_cons
--           apply ih ((some e, false) :: tail1) (by simp [len]) (irreducible_rest irr)
--           apply infix_cons_cons_ne_double at h
--           simp at h
--           exact h
--   exact H L.length L (by simp) h

theorem pt_move_ones : pairsTogether (move_ones_ind L) := pt_of_irr big_attempt

theorem pts_move_ones : pts (move_ones_ind L) := pts_of_irr big_attempt

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

def to_option (L : List (ℕ × Bool)) : List (Option ℕ × Bool) := (List.map (fun x ↦ (some x.1, x.2)) L)

theorem remove_map_helper {a : List (ℕ × Bool)} : remove_ones (to_option a) = a := by
  induction a
  · rfl
  rename_i ih
  simp [to_option, remove_ones]
  exact ih

theorem five_cases (b_ne : b1 ≠ b2) (h : a ++ [b1, b2] ++ c = d ++ [b1, b2] ++ e) :
  (a = d ∧ c = e) ∨ (∃ a1 a2, a = a1 ++ [b1, b2] ++ a2 ∧ d = a1 ∧ e = a2 ++ [b1, b2] ++ c) ∨
  (∃ c1 c2, c = c1 ++ [b1, b2] ++ c2 ∧ d = a ++ [b1, b2] ++ c1 ∧ e = c2) := by
  induction a generalizing b1 b2 c d e
  · simp at h
    simp
    match d with
    | [] =>
      left
      simp at h
      exact ⟨rfl, h⟩
    | d1 :: [] =>
      simp at h
      simp
      apply b_ne
      rw [h.2.1]
    | d1 :: d2 :: dr =>
      simp at h
      simp [h.1]
      constructor
      · rw [← h.1]
        exact h.2.2
      exact h.2.1.symm
  rename_i a1 ar ih
  match d with
  | [] =>
    simp at h
    simp [h.1, h.2]
    use []
    simp
    match ar with
    | [] => simp [b_ne] at h
    | a2 :: arr =>
      simp at h
      use arr
      simp [h.2.1, h.2.2]
  | d1 :: [] =>
    simp at h
    simp [h.1]
    match ar with
    | [] => left; simp at h; exact ⟨rfl, h.2⟩
    | a2 :: a3 :: arr =>
      simp at h
      simp
      use [d1]
      simp [h.1, h.2.1]
      use arr
      simp [h.2.1, h.2.2]
    | a2 :: [] =>
      simp at h
      exfalso
      apply b_ne
      exact h.2.2.1
  | d1 :: d2 :: dr =>
    simp at h
    simp [h.1]
    have H1 : ar ++ b1 :: b2 :: c  = ar ++ [b1, b2] ++ c := by simp
    have H : d2 :: (dr ++ b1 :: b2 :: e) = (d2 :: dr) ++ [b1, b2] ++ e := by simp
    rw [H1, H] at h
    specialize ih b_ne h.2
    rcases ih with h1 | h2 | h3
    · left
      exact h1
    · rcases h2 with ⟨a1', a2', spec⟩
      right; left
      use d1 :: a1'
      use a2'
      simp [spec.1, spec.2]
    rcases h3 with ⟨c1', c2', spec⟩
    right; right
    use c1'
    simp [spec.1, spec.2]


  -- rcases list_splits_somewhere h with h1 | ⟨to_middle, spec⟩ | ⟨to_middle, spec⟩
  -- · left;
  --   simp [h1] at h
  --   simp at h1
  --   aesop
  -- · match to_middle with
  --   | [] =>
  --     left
  --     simp  at h
  --     simp at spec
  --     aesop
  --   | head :: tail =>
  --     right
  --     left
  --     use d
  --     simp [spec.2]
  --     sorry
  -- sorry

theorem giant_list_split {w : List (Option ℕ × Bool)} (h : remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t =
    e ++ [(c1, false), (c2, true)] ++ f) (ptw : pairsTogether w) (ptt : pairsTogether t): (remove_ones w = e ∧ remove_ones t = f) ∨
    (∃ w1 w2, w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = remove_ones w1 ∧
    f = remove_ones w2 ++ [(c1, false), (c2, true)] ++ remove_ones t) ∨
    (∃ t1 t2, t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧
    e = remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t1 ∧ f = remove_ones t2) := by
  rcases (five_cases (by simp) h) with h1 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
  · left; exact h1
  · right; left
    use to_option w1
    use to_option w2
    constructor
    sorry
    sorry
  sorry

theorem giant_list_split' {w : List (Option ℕ × Bool)} (h : remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t =
    e ++ [(c1, false), (c2, true)] ++ f) (ptw : pts w) (ptt : pts t): (remove_ones w = e ∧ remove_ones t = f) ∨
    (∃ w1 w2, w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = remove_ones w1 ∧
    f = remove_ones w2 ++ [(c1, false), (c2, true)] ++ remove_ones t) ∨
    (∃ t1 t2, t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧
    e = remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t1 ∧ f = remove_ones t2) := by
  rcases (five_cases (by simp) h) with h1 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
  · left; exact h1
  · right; left
    use to_option w1
    use to_option w2
    constructor
    sorry
    sorry
  sorry
  -- rcases list_splits_somewhere h with h1 | ⟨to_middle, spec⟩ | ⟨to_middle, spec⟩
  -- · simp at h1
  --   rw [h1] at h
  --   simp at h
  --   left
  --   exact ⟨h1, h⟩
  -- · match to_middle with
  --   | [] =>
  --     simp at spec
  --     left
  --     aesop
  --   | head :: tail =>
  --     right
  --     sorry
  -- sorry

-- theorem pt_chop_left (h : pairsTogether (a ++ b)) : pairsTogether b := fun c d hcd ↦ h L1 (infix_append_left hl) c d hcd


-- theorem rg_of_rev_rel (d1) (h : SemiThue reversing g (e ++ (remove_ones d1) ++ f)) (gr : SemiThue grid_style' a' b') (a'_is : remove_ones a' = g)
--     (b'_is : remove_ones b' = e ++ [(c1, false), (c2, true)] ++ f) (pt_b : pairsTogether b') (rel_holds : grid_style' [(some c1, false), (some c2, true)] d1): ∃ a' b', SemiThue grid_style' a' b' ∧
--     remove_ones a' = g ∧ remove_ones b' = e ++ (remove_ones d1) ++ f ∧ pairsTogether b' := by
--     rcases pt_b c1 c2 (by use e; use f; exact b'_is.symm) with ⟨w, t, hwt⟩
--     use a'
--     rw [← hwt] at b'_is
--     rw [remove_ones_append, remove_ones_append] at b'_is
--     simp only [remove_ones] at b'_is
--     have ptw : pairsTogether w := by sorry
--       -- rw [← hwt] at pt_b
--       -- exact pts_chop_right (pts_chop_right pt_b)
--     have ptt : pairsTogether t := by sorry
--     have splits : (remove_ones w = e ∧ remove_ones t = f) ∨
--         (∃ w1 w2, w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = remove_ones w1 ∧
--         f = remove_ones w2 ++ [(c1, false), (c2, true)] ++ remove_ones t) ∨
--         (∃ t1 t2, t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧
--         e = remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t1 ∧ f = remove_ones t2) :=
--       giant_list_split b'_is ptw ptt
--     rcases splits with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
--     · use move_ones_ind (w ++ d1 ++ t)
--       constructor
--       · apply SemiThue.trans _ _ _ gr
--         rw [← hwt]
--         exact SemiThue.trans _ _ _ (SemiThue.reduction rel_holds) equiv_move_ones
--       exact ⟨a'_is, ⟨by rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, h2.1,
--           h2.2], pt_move_ones⟩⟩
--     · use move_ones_ind (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
--       constructor
--       · apply SemiThue.trans _ _ _ gr
--         rw [← hwt]
--         have H : SemiThue grid_style' (w ++ [(some c1, false), (some c2, true)] ++ t)
--           (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t) := by
--           apply SemiThue_append_right
--           rw [hw.1]
--           apply SemiThue_append_right
--           apply SemiThue_append_right
--           apply SemiThue_append_left
--           apply SemiThue_rel
--           exact rel_holds
--         apply H.trans
--         exact equiv_move_ones
--       constructor
--       · exact a'_is
--       constructor
--       · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, hw.2.1, hw.2.2]
--         simp [remove_ones, remove_ones_append]
--       exact pt_move_ones
--     use move_ones_ind (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
--     constructor
--     · apply SemiThue.trans _ _ _ gr
--       rw [← hwt]
--       have H : SemiThue grid_style' (w ++ [(some c1, false), (some c2, true)] ++ t)
--         (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2) := by
--         rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
--         apply SemiThue_append_left
--         rw [List.append_assoc, List.append_assoc] at ht
--         rw [ht.1]
--         apply SemiThue_append_left
--         apply SemiThue_append_left
--         apply SemiThue_append_right
--         exact SemiThue_rel rel_holds
--       exact H.trans _ _ _ equiv_move_ones
--     constructor
--     · exact a'_is
--     constructor
--     · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, ht.2.1, ht.2.2]
--       simp [remove_ones, remove_ones_append]
--     exact pt_move_ones

-- theorem rev_to_grid (h : SemiThue reversing a b) : ∃ a' b', SemiThue grid_style' a' b' ∧
--   remove_ones a' = a ∧ remove_ones b' = b ∧ pairsTogether b':= by
--   induction one_step_equiv_reg.mp h with
--   | refl a =>
--     use to_option a
--     use to_option a
--     constructor
--     · exact SemiThue.refl _
--     constructor
--     · exact remove_map_helper
--     constructor
--     · exact remove_map_helper
--     intro c d rm
--     rw [remove_map_helper] at rm
--     rcases rm with ⟨w, t, hwt⟩
--     use to_option w
--     use to_option t
--     rw [← hwt]
--     simp [to_option]
--   | one_step h1 h2 ih =>
--     rename_i c d e f g
--     specialize ih (one_step_equiv_reg.mpr h1)
--     rcases ih with ⟨a', b', gr, a'_is, b'_is, pt_b⟩
--     cases h2 with
--     | basic =>
--       exact rg_of_rev_rel ([(none, true), (none, false)]) h gr a'_is b'_is pt_b (grid_style'.basic _)
--     | apart h_dist =>
--       rename_i i j
--       exact rg_of_rev_rel ([(some j, true), (some i, false)]) h gr a'_is b'_is pt_b (grid_style'.apart h_dist)
--     | close h_dist =>
--       rename_i i j
--       exact rg_of_rev_rel ([(some j, true), (some i, true), (some j, false), (some i, false)]) h gr a'_is b'_is pt_b (grid_style'.close h_dist)

theorem pts_chop_right (h : pts (a ++ b)) : pts a := fun L1 hl c d hcd ↦ h L1 (infix_append_right hl) c d hcd

theorem pts_chop_left (h : pts (a ++ b)) : pts b := fun L1 hl c d hcd ↦ h L1 (infix_append_left hl) c d hcd

-- (h : SemiThue reversing g (e ++ (remove_ones d1) ++ f))
theorem rg_of_rev_rel' (d1) (gr : SemiThue grid_style' (to_option a) b')
    (b'_is : remove_ones b' = e ++ [(c1, false), (c2, true)] ++ f) (pt_b : pts b') (rel_holds : grid_style' [(some c1, false), (some c2, true)] d1): ∃ b', SemiThue grid_style' (to_option a) b' ∧
    remove_ones b' = e ++ (remove_ones d1) ++ f ∧ pts b' := by
    rcases pt_b b' (by exact List.infix_refl b') c1 c2 (by use e; use f; exact b'_is.symm) with ⟨w, t, hwt⟩
    rw [← hwt] at b'_is
    rw [remove_ones_append, remove_ones_append] at b'_is
    simp only [remove_ones] at b'_is
    have ptw : pts w := by
      rw [← hwt] at pt_b
      exact pts_chop_right (pts_chop_right pt_b)
    have ptt : pts t := by
      rw [← hwt, List.append_assoc] at pt_b
      exact pts_chop_left (pts_chop_left pt_b)
    have splits : (remove_ones w = e ∧ remove_ones t = f) ∨
        (∃ w1 w2, w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = remove_ones w1 ∧
        f = remove_ones w2 ++ [(c1, false), (c2, true)] ++ remove_ones t) ∨
        (∃ t1 t2, t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧
        e = remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t1 ∧ f = remove_ones t2) :=
      giant_list_split' b'_is ptw ptt
    rcases splits with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
    · use move_ones_ind (w ++ d1 ++ t)
      constructor
      · apply SemiThue.trans _ _ _ gr
        rw [← hwt]
        exact SemiThue.trans _ _ _ (SemiThue.reduction rel_holds) equiv_move_ones
      exact ⟨by rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, h2.1,
          h2.2], pts_move_ones⟩
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
      · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, hw.2.1, hw.2.2]
        simp [remove_ones, remove_ones_append]
      exact pts_move_ones
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
        exact SemiThue_rel rel_holds
      exact H.trans _ _ _ equiv_move_ones
    constructor
    · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, ht.2.1, ht.2.2]
      simp [remove_ones, remove_ones_append]
    exact pts_move_ones

-- (h : SemiThue reversing g (e ++ (remove_ones d1) ++ f))
theorem rg_of_rev_rel (d1) (gr : SemiThue grid_style' (to_option a) b')
    (b'_is : remove_ones b' = e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b') (rel_holds : grid_style' [(some c1, false), (some c2, true)] d1): ∃ b', SemiThue grid_style' (to_option a) b' ∧
    remove_ones b' = e ++ (remove_ones d1) ++ f ∧ irreducible b' := by
    rcases (pts_of_irr pt_b) b' (by exact List.infix_refl b') c1 c2 (by use e; use f; exact b'_is.symm) with ⟨w, t, hwt⟩
    rw [← hwt] at b'_is
    rw [remove_ones_append, remove_ones_append] at b'_is
    simp only [remove_ones] at b'_is
    have ptw : pts w := by
      rw [← hwt] at pt_b
      exact pts_chop_right (pts_chop_right (pts_of_irr pt_b))
    have ptt : pts t := by
      rw [← hwt, List.append_assoc] at pt_b
      exact pts_chop_left (pts_chop_left (pts_of_irr pt_b))
    have splits : (remove_ones w = e ∧ remove_ones t = f) ∨
        (∃ w1 w2, w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = remove_ones w1 ∧
        f = remove_ones w2 ++ [(c1, false), (c2, true)] ++ remove_ones t) ∨
        (∃ t1 t2, t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧
        e = remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t1 ∧ f = remove_ones t2) :=
      giant_list_split' b'_is ptw ptt
    rcases splits with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
    · use move_ones_ind (w ++ d1 ++ t)
      constructor
      · apply SemiThue.trans _ _ _ gr
        rw [← hwt]
        exact SemiThue.trans _ _ _ (SemiThue.reduction rel_holds) equiv_move_ones
      exact ⟨by rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, h2.1,
          h2.2], big_attempt⟩
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
      · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, hw.2.1, hw.2.2]
        simp [remove_ones, remove_ones_append]
      exact big_attempt
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
        exact SemiThue_rel rel_holds
      exact H.trans _ _ _ equiv_move_ones
    constructor
    · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, ht.2.1, ht.2.2]
      simp [remove_ones, remove_ones_append]
    exact big_attempt

theorem pt_to_option : pairsTogether (to_option c) := by
  intro a b hab
  simp [remove_map_helper] at hab
  rcases hab with ⟨w, t, hwt⟩
  use to_option w
  use to_option t
  rw [← hwt]
  simp [to_option]

theorem pts_to_option : pts (to_option a) := by
  have H : irreducible (to_option a) := by
    intro c
    constructor
    · intro h
      induction a
      · simp [to_option] at h
      rename_i ha ta iha
      apply iha
      match ta with
      | [] =>
        simp [to_option] at h
        apply infix_length_le at h
        simp at h
      | t :: taa =>
        simp [to_option] at h
        apply infix_cons_cons_ne_double at h
        simp at h
        exact h
    constructor
    · intro h
      induction a
      · simp [to_option] at h
      rename_i ha ta iha
      apply iha
      simp [to_option] at h
      apply infix_cons_cons_ne at h
      simp at h
      exact h
    intro h
    induction a
    · simp [to_option] at h
    rename_i ha ta iha
    apply iha
    simp [to_option] at h
    apply infix_cons_cons_ne at h
    simp at h
    exact h
  exact pts_of_irr H

theorem infix_cons_ne (h : a :: b <:+: c :: d) (h2 : a ≠ c) : a :: b <:+: d := by
  apply infix_cons_cons_ne at h
  simp [h2] at h
  exact h

theorem irr_to_option : irreducible (to_option a) := by
  induction a with
  | nil => simp [to_option, irreducible_nil]
  | cons head tail ih =>
    simp [to_option]
    intro x
    constructor
    · intro hx
      match tail with
      | [] =>
        apply infix_length_le at hx
        simp at hx
      | t1 :: tr =>
        apply infix_cons_cons_ne_double at hx
        simp only [ne_eq, Prod.mk.injEq, reduceCtorEq, Bool.true_eq, false_and, not_false_eq_true,
          forall_const] at hx
        exact (ih x).1 hx
    constructor
    · intro hx
      apply infix_cons_ne at hx
      simp at hx
      exact (ih x).2.1 hx
    intro hx
    apply infix_cons_ne at hx
    simp at hx
    exact (ih x).2.2 hx


theorem rev_to_grid' (h : SemiThue reversing a b) : ∃ b', SemiThue grid_style' (to_option a) b' ∧
  remove_ones b' = b ∧ pts b':= by
  induction one_step_equiv_reg.mp h with
  | refl a =>
    use to_option a
    constructor
    · exact SemiThue.refl _
    constructor
    · exact remove_map_helper
    exact pts_to_option
  | one_step h1 h2 ih =>
    rename_i c d e f g
    specialize ih (one_step_equiv_reg.mpr h1)
    rcases ih with ⟨b', gr, b'_is, pt_b⟩
    cases h2 with
    | basic =>
      apply rg_of_rev_rel' ([(none, true), (none, false)]) gr  b'_is pt_b (grid_style'.basic _)
    | apart h_dist =>
      rename_i i j
      exact rg_of_rev_rel' ([(some j, true), (some i, false)]) gr b'_is pt_b (grid_style'.apart h_dist)
    | close h_dist =>
      rename_i i j
      exact rg_of_rev_rel' ([(some j, true), (some i, true), (some j, false), (some i, false)]) gr b'_is pt_b (grid_style'.close h_dist)

theorem rev_to_grid (h : SemiThue reversing a b) : ∃ b', SemiThue grid_style' (to_option a) b' ∧
  remove_ones b' = b ∧ irreducible b':= by
  induction one_step_equiv_reg.mp h with
  | refl a =>
    use to_option a
    constructor
    · exact SemiThue.refl _
    constructor
    · exact remove_map_helper
    apply irr_to_option
  | one_step h1 h2 ih =>
    rename_i c d e f g
    specialize ih (one_step_equiv_reg.mpr h1)
    rcases ih with ⟨b', gr, b'_is, pt_b⟩
    cases h2 with
    | basic =>
      apply rg_of_rev_rel ([(none, true), (none, false)]) gr  b'_is pt_b (grid_style'.basic _)
    | apart h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, false)]) gr b'_is pt_b (grid_style'.apart h_dist)
    | close h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, true), (some j, false), (some i, false)]) gr b'_is pt_b (grid_style'.close h_dist)

def is_false (a : List (α × Bool)) := ∀ x ∈ a, x.2 = false

theorem is_false_cons (a : List (α × Bool)) (h : is_false a): is_false ((b, false) :: a) := by
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h2
  · simp [h1]
  exact h _ h2

def is_true (a : List (α × Bool)) := ∀ x ∈ a, x.2 = true

theorem is_true_cons (a : List (α × Bool)) (h : is_true a): is_true ((b, true) :: a) := by
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h2
  · simp [h1]
  exact h _ h2

def in_order (a : List (α × Bool)) := ∃ a1 a2, is_true a1 ∧ is_false a2 ∧ a = a1 ++ a2

theorem in_order_rest (h : in_order (head :: t)) : in_order t := by
  rcases h with ⟨a1, a2, ha⟩
  match a1 with
  | [] => match a2 with
    | [] => simp at ha
    | heada :: taila =>
      use []
      use taila
      constructor
      · exact ha.1
      constructor
      · intro x hx
        apply ha.2.1
        exact List.mem_cons_of_mem heada hx
      simp at ha
      simp [ha.2.2.2]
  | heada :: taila =>
    use taila
    use a2
    constructor
    · intro x hx
      apply ha.1
      exact List.mem_cons_of_mem heada hx
    constructor
    · exact ha.2.1
    simp at ha
    exact ha.2.2.2

theorem in_order_of_true (h : is_true L) : in_order L := by
  use L
  use []
  constructor
  · exact h
  constructor
  · intro x hx
    simp at hx
  simp

theorem in_order_of_false (h : is_false L) : in_order L := by
  use []
  use L
  constructor
  · intro x hx
    simp at hx
  constructor
  · exact h
  simp

theorem in_order_append (h : in_order (a++b)) : in_order a ∧ in_order b := by
  rcases h with ⟨a1, a2, a1_true, a2_false, ha⟩
  rcases list_splits_somewhere ha with h1 | ⟨to_middle, spec⟩ | ⟨to_middle, spec⟩
  · rw [h1] at ha
    simp at ha
    rw [h1, ha]
    constructor
    · exact in_order_of_true a1_true
    exact in_order_of_false a2_false
  · constructor
    · rw [spec.1] at ha
      simp at ha
      rw [spec.1]
      use a1
      use to_middle
      constructor
      · exact a1_true
      constructor
      · intro x hx
        apply a2_false
        rw [spec.2]
        exact List.mem_append_left _ hx
      rfl
    use []
    use b
    constructor
    · intro x hx
      simp at hx
    constructor
    · rw [spec.2] at a2_false
      intro x hx
      apply a2_false
      exact List.mem_append_right to_middle hx
    rfl
  constructor
  · use a
    use []
    constructor
    · intro x hx
      rw [← spec.1] at a1_true
      apply a1_true
      exact List.mem_append_left to_middle hx
    constructor
    · intro x hx
      simp at hx
    simp
  use to_middle
  use a2
  constructor
  · rw [← spec.1] at a1_true
    intro x hx
    apply a1_true
    exact List.mem_append_right _ hx
  constructor
  · exact a2_false
  exact spec.2

@[simp]
theorem is_true_nil : is_true ([] : List (α × Bool)) := by
  intro x hx
  simp at hx

@[simp]
theorem is_false_nil : is_false ([] : List (α × Bool)) := by
  intro x hx
  simp at hx

theorem in_order_nil {α} : in_order ([] : List (α × Bool)) := by
  use []
  use []
  simp

theorem in_order_of_rm_irr (h : in_order (remove_ones L)) (h2 : irreducible L) : in_order L := by
  induction L
  · exact in_order_nil
  rename_i head tail ih
  have h_pts : irreducible tail := irreducible_rest h2
  have h_io : in_order (remove_ones tail) := by
    match head with
    | (none, _) =>
      simp [remove_ones] at h
      exact h
    | (some _, _) =>
      simp [remove_ones] at h
      exact in_order_rest h
  specialize ih h_io h_pts
  rcases ih with ⟨a1, a2, ha⟩
  match head with
  | (none, true) =>
    use (none, true) :: a1
    use a2
    constructor
    · intro x hx
      simp at hx
      rcases hx with h1 | h2
      · simp [h1]
      exact ha.1 _ h2
    constructor
    · exact ha.2.1
    simp [ha.2.2]
  | (none, false) =>
    use []
    use (none, false) :: a2
    constructor
    · intro x hx
      simp at hx
    constructor
    · apply is_false_cons
      exact ha.2.1
    simp [ha.2.2]
    match a1 with
    | [] => rfl
    | head :: tail1 =>
      exfalso
      match head with
      | (_, false) => simp [is_true] at ha
      | (none, true) =>
        simp [remove_ones] at h
        simp [is_true] at ha
        rw [ha.2.2] at h2
        specialize h2 0
        apply h2.2.2
        use []
        use tail1 ++ a2
        simp
      | (some c, true) =>
        simp [remove_ones] at h
        simp [is_true] at ha
        rw [ha.2.2] at h2
        specialize h2 c
        apply h2.2.1
        use []
        use tail1 ++ a2
        simp
  | (some a, true) =>
    simp [remove_ones] at h
    use (some a, true) :: a1
    use a2
    constructor
    · intro x hx
      simp at hx
      rcases hx with h1 | h2
      · simp [h1]
      exact ha.1 _ h2
    constructor
    · exact ha.2.1
    simp [ha.2.2]
  | (some a, false) =>
    simp [remove_ones] at h
    use []
    use (some a, false) :: a2
    constructor
    · intro x hx
      simp at hx
    constructor
    · apply is_false_cons
      exact ha.2.1
    simp [ha.2.2]
    match tail with
    | [] =>
      simp at ha
      exact ha.2.2.1
    | (none, true) :: tail2 =>
      apply (h2 a).1.elim
      use []
      use tail2
      simp
    | (_, false) :: tail2 =>
      match a1 with
      | [] => rfl
      | (_, true) :: rest => simp at ha
      | (_, false) :: rest => simp [is_true] at ha
    | (some c, true) :: tail2 =>
      simp [remove_ones] at h
      change in_order ([(a, false), (c, true)]++_) at h
      apply in_order_append at h
      exfalso
      rcases h.1 with ⟨a3, a4, ha34⟩
      match a3 with
      | [] =>
        have H := ha34.2.2
        simp at H
        rw [← H] at ha34
        simp [is_false] at ha34
      | head :: tail =>
        have H := ha34.2.2
        simp at H
        rw [← H.1] at ha34
        simp [is_true] at ha34

-- theorem in_order_insert_none_false (h : in_order L) : in_order (insert_one (none, false) L) := by
--   induction L
--   · simp; use []; use [(none, false)]; simp [is_true, is_false]
--   rename_i head tail ih
--   match head with
--   | (none, true) =>
--     simp [insert_one]
--     specialize ih (in_order_rest h)
--     rcases ih with ⟨a1, a2, ha⟩
--     use (none, true):: a1
--     use a2
--     constructor
--     · intro x hx
--       simp at hx
--       rcases hx with h1 | h2
--       · simp [h1]
--       exact ha.1 _ h2
--     constructor
--     · exact ha.2.1
--     simp [ha.2.2]
--   | (none, false) =>
--     simp
--     rcases h with ⟨a1, a2, ha⟩
--     match a1 with
--     | [] =>
--       use []
--       use (none, false) :: a2
--       simp [ha]
--       intro x hx
--       simp at hx
--       rcases hx with h1 | h2
--       · simp [h1]
--       apply ha.2.1 _ h2
--     | heada :: taila =>
--       exfalso
--       simp at ha -- ask on zulip about this
--       rw [← ha.2.2.1] at ha
--       simp [is_true] at ha
--   | (some a, true) =>
--     simp [insert_one]
--     specialize ih (in_order_rest h)
--     rcases ih with ⟨a1, a2, ha⟩
--     use (some a, true) :: a1
--     use a2
--     simp [ha]
--     intro x hx
--     simp at hx
--     rcases hx with h1 | h2
--     · simp [h1]
--     apply ha.1 _ h2
--   | (some a, false) =>
--     simp [insert_one]
--     specialize ih (in_order_rest h)
--     rcases h with ⟨a1, a2, ha⟩
--     use []
--     use (none, false) :: a2
--     match a1 with
--     | [] =>
--       simp [ha]
--       intro x hx
--       simp at hx
--       rcases hx with h1 | h2
--       · simp [h1]
--       apply ha.2.1 _ h2
--     | heada :: taila =>
--       exfalso
--       simp at ha -- ask on zulip about this
--       rw [← ha.2.2.1] at ha
--       simp [is_true] at ha

-- theorem in_order_insert (h : in_order (a :: L)) : in_order (insert_one a L) := by
--   match a with
--   | (none, true) =>
--     simp [insert_one]
--     exact h
--   | (none, false) =>
--     exact in_order_insert_none_false (in_order_rest h)
--   | (some a, true) =>
--     match L with
--     | [] =>
--       simp
--       exact h
--     | (none, true) :: tail =>
--       simp [insert_one]
--       exact h
--     | (none, false) :: tail =>
--       simp [insert_one]
--       exact h
--     | (some b, true) :: tail =>
--       simp [insert_one]
--       exact h
--     | (some b, false) :: tail =>
--       simp [insert_one]
--       exact h
--   | (some a, false) =>
--     match L with
--     | [] =>
--       simp
--       exact h
--     | (none, true) :: tail =>
--       simp [insert_one]
--       exfalso
--       change in_order ([(some a, false), (none, true)] ++ tail) at h
--       apply in_order_append at h
--       rcases h.1 with ⟨a1, a2, ha⟩
--       match a1 with
--       | [] =>
--         have H := ha.2.2
--         simp at H
--         rw [← H] at ha
--         simp [is_false] at ha
--       | head :: tail =>
--         have H := ha.2.2
--         simp at H
--         rw [← H.1] at ha
--         simp [is_true] at ha
--     | (none, false) :: tail =>
--       simp [insert_one]
--       exact h
--     | (some b, true) :: tail =>
--       simp [insert_one]
--       exact h
--     | (some b, false) :: tail =>
--       simp [insert_one]
--       exact h


-- theorem in_order_move_ones (h : in_order L) : in_order (move_ones_ind L) := by
--   induction L
--   · simp [h]
--   rename_i head tail ih
--   specialize ih (in_order_rest h)
--   simp [move_ones_ind]
--   have H := in_order_insert h
--   match head with
--   | (none, true) =>
--     simp [insert_one]
--     rcases ih with ⟨a1, a2, ha⟩
--     use (none, true) :: a1
--     use a2
--     simp [ha]
--     apply is_true_cons _ ha.1
--   | (none, false) =>
--     apply in_order_insert_none_false ih
--   | (some a, true) =>
--     sorry
--   | (some a, false) =>
--     match tail with
--     | [] =>
--       simp
--       use []
--       use [(some a, false)]
--       simp [is_true, is_false]
--     | ht :: ttt =>
--       sorry
