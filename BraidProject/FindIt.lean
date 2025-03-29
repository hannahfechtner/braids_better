import BraidProject.StepOne
import BraidProject.Shortlex



def find_it (L : List (Option ℕ × Bool)) :
    Option (List (Option ℕ × Bool) × ((Option ℕ) × (Option ℕ)) × List (Option ℕ × Bool)) :=
  match L with
  | [] => none
  | _ :: [] => none
  | (some a, false) :: (some b, true) :: tail =>
    match find_it tail with
    | none => none
    | some (c, e, f) =>
      some ((some a, false) :: (some b, true) :: c, e, f)
  | (a, false) :: (b, true) :: tail =>
    some ([], (a, b), tail)
  | head :: tail =>
    match find_it tail with
    | none => none
    | some (c, e, f) =>
      some (head :: c, e, f)
-- i need to not return some, some because that's silly

@[simp]
theorem find_it_nil : find_it [] = none := by simp [find_it]

@[simp]
theorem find_it_singleton : find_it [a] = none := by
  unfold find_it; simp

theorem find_it_cons_none (h : find_it (a :: b) = none) : find_it b = none := by
  revert h
  cases b with
  | nil => simp
  | cons head tail =>
    induction tail generalizing a head with
    | nil => simp
    | cons head1 tail1 ih =>
      intro h
      unfold find_it at h
      rcases a with ⟨a1, a2⟩
      rcases head1 with ⟨h3, h4⟩
      rcases head with ⟨h5, h6⟩
      cases a2 with
      | false =>
        cases h6 with
        | false =>
          simp at h
          cases ha : find_it ((h5, false) :: (h3, h4) :: tail1) with
          | none => rfl
          | some a => simp [ha] at h
        | true =>
          cases a1 with
          | none => simp at h
          | some d =>
            cases h5 with
            | none => simp at h
            | some d1 =>
              simp at h
              cases ha : find_it ((h3, h4) :: tail1) with
              | none =>
                simp [h, find_it, ha]
              | some d => simp [ha] at h
      | true =>
        simp at h
        cases ha : find_it ((h5, h6) :: (h3, h4) :: tail1) with
        | none => rfl
        | some a => simp [ha] at h

theorem find_it_cons_true_iff : find_it tail = none ↔ find_it ((none, true) :: tail) = none := by
  constructor
  · intro h
    cases tail with
    | nil => simp [find_it]
    | cons head tail => simp [h, find_it]
  intro h
  exact find_it_cons_none h

@[simp]
theorem find_it_cons_true (h : find_it tail = some ⟨a, b, c⟩) : find_it ((d, true) :: tail) = some ⟨(d, true):: a, b, c⟩ := by
  conv => lhs; unfold find_it
  cases tail with
  | nil => simp at h
  | cons headt tailt => simp [h]

theorem find_it_first_empty (h : find_it a = some ([], d, e)) : ∃ a1 a2, a = (a1, false) :: a2 := by
  induction a with
  | nil => simp [find_it] at h
  | cons head tail ih =>
    rcases head with ⟨h1, t1⟩
    cases t1 with
    | false => use h1, tail
    | true =>
      cases tail with
      | nil => simp [find_it] at h
      | cons head1 tail1 =>
        rcases head1 with ⟨h2, t2⟩
        simp [find_it] at h
        cases hf : find_it ((h2, t2) :: tail1) with
        | none => simp [hf] at h
        | some idk =>
          simp [hf] at h

theorem find_it_true_cons (h : find_it ((a, true)::b) = some (c1 :: c, d, e)) :
    find_it b = (c, d, e) ∧ c1 = (a, true) := by
  induction b with
  | nil =>
    simp [find_it] at h
  | cons hb tb ih =>
    rcases hb with ⟨fb, sb⟩
    cases sb with
    | false =>
      simp [find_it] at h
      cases h1 : find_it ((fb, false) :: tb) with
      | none => simp [h1] at h
      | some val =>
        simp [h1] at h
        constructor
        · rw [← h.2, ← h.1.2]
        exact h.1.1.symm
    | true =>
      simp [find_it] at h
      cases h1 : find_it ((fb, true) :: tb) with
      | none => simp [h1] at h
      | some val =>
        simp [h1] at h
        constructor
        · rw [← h.2, ← h.1.2]
        exact h.1.1.symm

theorem fitc_iff (h : find_it tail1 = some (v1, v2, v3)) :
    find_it ((a, true) :: tail1) = some ((a, true) :: v1, v2, v3) := by
  induction tail1 generalizing v1 with
  | nil => simp [find_it] at h
  | cons head tail ih =>
    induction tail with
    | nil => simp [find_it] at h
    | cons head2 tail2 ih2 =>
      rcases head with ⟨f, s⟩
      rcases head2 with ⟨f2, s2⟩
      cases s with
      | false =>
        cases s2 with
        | true =>
          cases f with
          | some val =>
            cases f2 with
            | none =>
              simp [find_it] at h
              simp [find_it]
              exact h
            | some val =>
              simp [find_it] at h
              simp [find_it]
              rw [h]
          | none =>
            simp [find_it] at h
            simp [find_it]
            exact h
        | false =>
          simp [find_it] at h
          cases h1 : find_it ((f2, false) :: tail2) with
          | none => simp [h1] at h
          | some val =>
            simp [h1] at h
            simp [find_it, h1]
            exact h
      | true =>
        simp [find_it] at h
        cases h1 : find_it ((f2, s2) :: tail2) with
        | none => simp [h1] at h
        | some val =>
          simp [h1] at h
          simp [find_it, h1]
          exact h

theorem find_it_spec {L : List ((Option ℕ × Bool))} (h : find_it L = some (c, d, e)) :
    L = c ++ ([(d.1, false)] ++ [(d.2, true)]) ++ e ∧ ¬ (∃ d1 d2, d.1= some d1 ∧ d.2 = some d2):= by
  induction L generalizing c d e with
  | nil => simp [find_it] at h
  | cons head tail ih =>
  cases tail with
  | nil => simp [find_it] at h
  | cons head1 tail1 =>
    rcases head with ⟨fst1, snd1⟩
    cases snd1 with
    | false =>
      rcases head1 with ⟨fst2, snd2⟩
      cases fst1 with
      | none =>
        cases fst2 with
        | none =>
          cases snd2 with
          | false =>
            simp [find_it] at h
            cases hcases : find_it ((none, false) :: tail1) with
            | none => simp [hcases] at h
            | some thing =>
              rcases thing with ⟨v1, v2, v3⟩
              simp [hcases] at h
              rw [h.2.1, h.2.2] at hcases
              specialize ih hcases
              rw [← h.1, ih.1]
              simp
              intro x hd y hd2
              have H : ∃ d1 d2, d.1 = some d1 ∧ d.2 = some d2 := by
                use x, y
              exact (ih.2 H).elim
          | true =>
            simp only [find_it, Option.some.injEq, Prod.mk.injEq, List.nil_eq] at h
            rw [h.1, h.2.2]
            have H := Prod.mk.inj_iff.mp h.2.1
            rw [← H.1, ← H.2]
            simp
        | some val2 =>
          cases snd2 with
          | false =>
            simp [find_it] at h
            cases hcases : find_it ((some val2, false) :: tail1) with
            | none => simp [hcases] at h
            | some thing =>
              rcases thing with ⟨v1, v2, v3⟩
              simp [hcases] at h
              rw [h.2.1, h.2.2] at hcases
              specialize ih hcases
              rw [← h.1, ih.1]
              simp
              intro x hd y hd2
              have H : ∃ d1 d2, d.1 = some d1 ∧ d.2 = some d2 := by
                use x, y
              exact (ih.2 H).elim
          | true =>
            simp only [find_it, Option.some.injEq, Prod.mk.injEq, List.nil_eq] at h
            rw [h.1, h.2.2]
            have H := Prod.mk.inj_iff.mp h.2.1
            rw [← H.1, ← H.2]
            simp
      | some val3 =>
        cases fst2 with
        | none =>
          cases snd2 with
          | false =>
            simp [find_it] at h
            cases hcases : find_it ((none, false) :: tail1) with
            | none => simp [hcases] at h
            | some thing =>
              rcases thing with ⟨v1, v2, v3⟩
              simp [hcases] at h
              rw [h.2.1, h.2.2] at hcases
              specialize ih hcases
              rw [← h.1, ih.1]
              simp
              intro x hd y hd2
              have H : ∃ d1 d2, d.1 = some d1 ∧ d.2 = some d2 := by
                use x, y
              exact (ih.2 H).elim
          | true =>
            simp only [find_it, Option.some.injEq, Prod.mk.injEq, List.nil_eq] at h
            rw [h.1, h.2.2]
            have H := Prod.mk.inj_iff.mp h.2.1
            rw [← H.1, ← H.2]
            simp
        | some val2 =>
          cases snd2 with
          | false =>
            simp [find_it] at h
            cases hcases : find_it ((some val2, false) :: tail1) with
            | none => simp [hcases] at h
            | some thing =>
              rcases thing with ⟨v1, v2, v3⟩
              simp [hcases] at h
              rw [h.2.1, h.2.2] at hcases
              specialize ih hcases
              rw [← h.1, ih.1]
              simp
              intro x hd y hd2
              have H : ∃ d1 d2, d.1 = some d1 ∧ d.2 = some d2 := by
                use x, y
              exact (ih.2 H).elim
          | true =>
            simp [find_it] at h
            cases h1 : find_it tail1 with
            | none => simp [h1] at h
            | some val =>
              rcases val with ⟨v1, v2, v3⟩
              specialize ih (fitc_iff h1)
              simp only [List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, true_and] at ih
              simp [h1] at h
              rw [ih.1, ← h.1, ← h.2.2, ← h.2.1]
              simp
              intro x hd y hd2
              have H : ∃ d1 d2, v2.1 = some d1 ∧ v2.2 = some d2 := by
                use x, y
              exact (ih.2 H).elim
    | true =>
      cases c with
      | nil =>
        rcases find_it_first_empty h with ⟨a1, a2, ha⟩
        simp at ha
      | cons head3 tail3 =>
        apply find_it_true_cons at h
        specialize ih h.1
        rw [ih.1, ← h.2]
        simp
        intro x hd y hd2
        have H : ∃ d1 d2, d.1 = some d1 ∧ d.2 = some d2 := by
          use x, y
        exact (ih.2 H).elim

theorem find_it_pair {a b : Option ℕ × Bool} (h : find_it [a,b] = some (c, d, e)) :
    d = (none, none) ∨ ∃ a, d = (some a, none) ∨ d = (none, some a) := by
  have H := find_it_spec h
  rcases d with ⟨d1, d2⟩
  cases d1 with
  | none =>
    cases d2 with
    | none => left; rfl
    | some f => right; use f; right; rfl
  | some f =>
    cases d2 with
    | none => right; use f; left; rfl
    | some g => simp at H

-- put in alphabet rel
instance : IsIrrefl (Option ℕ × Bool) lt_a := by
  constructor
  intro a h
  match a with
  | (some a, true) => simp [lt_a] at h
  | (some a, false) => simp [lt_a] at h
  | (none, true) => simp [lt_a] at h
  | (none, false) => simp [lt_a] at h
--local instance hi2 : WellFounded (Shortlex lt_a) := @Shortlex.wf _ _ wf_ar

local instance : WellFoundedRelation (List (Option ℕ × Bool)) where
  rel := Shortlex (lt_a)
  wf := @Shortlex.wf _ _ wf_ar


def move_ones' (a : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
  --let b := find_it a [(none, false), (none, true)]
  --have hb' : b = find_it a [(none, false), (none, true)] := rfl
  match hb': find_it a with
  | none => a
  | some (c, d, e) =>
    -- have hb : Shortlex lt_a (c++ [(none, true), (none, false)] ++e) (c++ [(none, false), (none, true)] ++e) := by
    --   exact
    --     (Shortlex.append_right_iff e).mp
    --       ((Shortlex.append_left_iff c).mp (Shortlex.of_lex rfl (List.Lex.rel (Eq.refl true))))
    -- have len_d := ((@find_it_spec _ _ _ a) (by rw [← hb']))
    match hd : d with
    | (none, none) => move_ones (c ++ [(none, true), (none, false)] ++ e)
    | (none, some i) => move_ones (c ++ [(some i, true), (none, false)] ++ e)
    | (some i, none) => move_ones (c ++ [(none, true), (some i, false)] ++ e)
    | _ => a -- some i, some j
    termination_by a
    decreasing_by
    · --rw [hd] at hb'
      rw [((@find_it_spec _ _ _ a) (by rw [← hb'])).1]
      apply (Shortlex.append_right_iff e).mp
      apply (Shortlex.append_left_iff c).mp
      apply Shortlex.of_lex (by rfl)
      apply List.Lex.rel (by rfl)
    · --rw [hd] at hb'
      rw [((@find_it_spec _ _ _ a) (by rw [← hb'])).1]
      exact (Shortlex.append_right_iff e).mp ((Shortlex.append_left_iff c).mp (Shortlex.of_lex
      (Eq.refl [(none, true), (none, false)].length) (List.Lex.rel (Eq.refl true))))
    · --rw [hd] at hb'
      rw [((@find_it_spec _ _ _ a) (by rw [← hb'])).1]
      apply (Shortlex.append_right_iff e).mp
      apply (Shortlex.append_left_iff c).mp
      apply Shortlex.of_lex (by rfl)
      apply List.Lex.rel
      rfl

-- theorem move_one_spec (h : move_ones_ind L = L1 ++ L2) : ∀ l ∈ L1, ∀ m ∈ L2, l < m := by sorry
-- def move_ones_mwe (a : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
--   --let b := find_it a [(none, false), (none, true)]
--   --have hb' : b = find_it a [(none, false), (none, true)] := rfl
--   match hb': find_it a with
--   | none => a
--   | some (c, d, e) => (move_ones_mwe c) ++ e
--   decreasing_by
--   sorry

-- @[simp]
-- theorem move_ones_cons_nil_true_mwe : move_ones_mwe ((none, true) :: tail) = (none, true) :: move_ones_mwe tail := by
--   unfold move_ones_mwe
--   cases tail with
--   | nil =>
--     have H : find_it [(none, true)] = none := by simp
--     rw [H]
--     simp (config := {zetaDelta := true}) [H]
--     rfl
--   | cons head1 tail =>
--     cases find_it (head1 :: tail) with
--     | none => sorry
--     | some d => sorry

--set_option pp.all true

-- theorem move_ones_no_find_it (h : find_it L = none) : move_ones L = L := by
--   unfold move_ones
--   split
--   · rfl
--   aesop

-- @[simp]
-- theorem move_ones_cons_nil_true : move_ones ((none, true) :: tail) = (none, true) :: move_ones tail := by
--   unfold move_ones
--   split
--   · rename_i h1
--     simp
--     split
--     · rfl
--     exfalso
--     sorry --rw [move_ones_no_find_it (find_it_cons_none h1)]
--   split
--   · rename_i h1
--     apply find_it_spec at h1
--     simp at h1
--     split
--     · exfalso
--       sorry
--     rename_i h2
--     apply find_it_spec at h2
--     simp at h2
--     split
--     · simp at h2
--       rw [h2] at h1
  -- generalize ht : List.length tail = t
  -- induction t with
  -- | zero =>
  --   unfold move_ones;
  --   have H : tail = [] := List.length_eq_zero.mp ht
  --   rw [H]
  --   rfl
  -- | succ n ih =>
  --   conv => lhs; unfold move_ones
  --   split
  --   · rename_i h1
  --     rw [move_ones_no_find_it (find_it_cons_none h1)]
  --   rename_i c d e fis
  --   unfold move_ones
  --   split
  --   · split
  --     · exfalso
  --       sorry
  --     split
  --     · split




      --generalize_proofs p
      --cases find_it (a:: b) with

    -- cases find_it tail with
    -- | none => sorry
    -- | some d => sorry

-- def new_move_ones' (L : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
--   match L with
--   | [] => []
--   | a :: b =>
--     match h : (a, new_move_ones' b) with
--     | ((some a, a1), (some b, b1) :: c) => (some a, a1) :: (some b, b1) :: c
--     | (a, b :: c) => if lt_a a b then a :: b :: c else b:: new_move_ones' (a :: c)
--     | (a, []) => [a]
--   termination_by L
--   decreasing_by
--   · refine Shortlex.of_length_lt ?_
--     simp
--   simp at h
--   rw [h.1]
--   refine Shortlex.cons_iff.mpr ?_
--   refine Shortlex.of_lex ?_ ?_
--   rename_i x _
--   simp at x
--   sorry

-- def new_move_ones (L : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
--   match hl : L with
--   | [] => []
--   | a :: b =>
--     let rest := new_move_ones b
--     match hr : new_move_ones b with
--     | [] => [a]
--     | head :: tail =>
--       match f_is : (a, head) with
--       | ((a1, true), (b1, false)) => (a1, true) :: rest
--       | ((none, true), (none, true)) => (none, true) :: rest
--       | ((some a1, true), (some b1, true)) => (some a1, true) :: rest
--       | ((some a1, true), (none, true)) => (none, true) :: new_move_ones ((some a1, true) :: tail)
--       | ((none, true), (some a1, true)) => (none, true) :: rest
--       | ((none, false), (none, false)) => (none, false) :: rest
--       | ((some a1, false), (some b1, false)) => (some a1, false) :: rest
--       | ((some a1, false), (none, false)) => (some a1, false) :: rest
--       | ((none, false), (some b1, false)) => (some b1, false) :: new_move_ones ((none, false) :: rest)
--       | ((none, false), (none, true)) => (none, true) :: new_move_ones ((none, false)::rest)
--       | ((some a1, false), (none, true)) => (none, true) :: new_move_ones ((some a1, false)::rest)
--       | ((none, false), (some b1, true)) => (some b1, true) :: new_move_ones ((none, false)::rest)
--       | ((some a1, false), (some b1, true)) => (some a1, false) :: new_move_ones rest
--   termination_by L
--   decreasing_by
--   · refine Shortlex.of_length_lt ?_
--     simp
--   all_goals
--   sorry

-- def add_in_ones (a : Option ℕ × Bool) (L : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
--   match L with
--   | [] => [a]
--   | head :: tail =>
--     if lt_a head a then add_in_ones a tail else a :: L

-- theorem move_cons : move_ones (head :: tail) = add_in_ones head (move_ones tail) := by
--   induction tail with
--   | nil =>
--     simp [add_in_ones]
--     exact move_ones_singleton
--   | cons head1 tail1 ih =>
--     sorry
