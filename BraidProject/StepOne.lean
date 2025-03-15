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

def move_ones (a : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
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

def pairsTogether  (L : List (Option ℕ × Bool)) := ∀ a b, [(a, false), (b, true)] <:+: remove_ones L →
    [(some a, false), (some b, true)] <:+: L

theorem pairsTogether_empty : pairsTogether [] := by
  intro c d hcd
  exfalso
  simp at hcd

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

-- theorem foo_helper' (n : ℕ) (iht : ∀ L, L.length ≤ n → pairsTogether L) (h : L1.length ≤ n): pairsTogether (insert_one head L1) := by
--   match head with
--   | (none, true) =>
--     simp [insert_one_none_true]
--     intro a b hab
--     have H : remove_ones ((none, true) :: L1) = remove_ones L1 := rfl
--     rw [H] at hab
--     specialize iht L1 h a b hab
--     exact List.infix_cons iht
--   | (none, false) =>
--     simp [insert_one_none_false]
--     intro a b hab
--     have H : remove_ones (L1 ++ [(none, false)]) = remove_ones L1 := by sorry
--     rw [H] at hab
--     specialize iht L1 h a b hab
--     refine List.infix_concat_iff.mpr ?_
--     right
--     exact iht
--   | (some a, true) =>
--     match L1 with
--     | [] => simp [pairs_together_singleton]
--     | (some a1, snd) :: tail =>
--       simp [insert_one_some_some]
--       specialize iht ((some a1, snd) :: tail) h
--       intro c d hcd
--       have H : remove_ones ((some a, true) :: (some a1, snd) :: tail) = (a, true) :: remove_ones ((some a1, snd) :: tail) := rfl
--       rw [H] at hcd
--       have H2 : [(c, false), (d, true)] <:+: remove_ones ((some a1, snd) :: tail) := infix_cons_cons_ne hcd (by aesop)
--       exact List.infix_cons (iht c d H2)
--     | (none, true) :: tail =>
--       simp [insert_one_to_none_true]
--       simp at h
--       specialize iht (insert_one (some a, true) tail) (by rw [insert_one_length]; exact h; rfl)
--       intro c d hcd
--       have H : remove_ones ((none, true) :: insert_one (some a, true) tail) = remove_ones (insert_one (some a, true) tail) := rfl
--       rw [H] at hcd
--       specialize iht c d hcd
--       exact List.infix_cons iht
--     | (none, false) :: tail =>
--       have H : insert_one (some a, true) ((none, false) :: tail) = (some a, true) :: ((none, false) :: tail) := rfl
--       rw [H]
--       specialize iht ((none, false) :: tail) h
--       intro c d hcd
--       have H2 : remove_ones ((some a, true) :: (none, false) :: tail) = (a, true) :: remove_ones ((none, false) :: tail) := rfl
--       rw [H2] at hcd
--       have H3 : [(c, false), (d, true)] <:+: remove_ones ((none, false) :: tail) := infix_cons_cons_ne hcd (by aesop)
--       specialize iht c d H3
--       exact List.infix_cons iht
--   | (some a, false) =>
--     match L1 with
--     | [] => simp [pairs_together_singleton]
--     | (some a1, snd) :: tail =>
--       simp [insert_one_some_some]
--       specialize iht ((some a1, snd) :: tail) h
--       intro c d hcd
--       have H : remove_ones ((some a, false) :: (some a1, snd) :: tail) = (a, false) :: (a1, snd) :: remove_ones tail := rfl
--       rw [H] at hcd
--       specialize iht c d
--       rcases infix_cons_cons_def hcd with h1 | h2
--       · simp at h1
--         rw [h1.1, h1.2.1, h1.2.2]
--         change _ <:+: [(some a, false), (some a1, true)] ++ tail
--         exact infix_append_right (List.infix_refl [(some a, false), (some a1, true)])
--       have H1 : (a1, snd) :: remove_ones tail = remove_ones ((a1, snd):: tail) := rfl
--       rw [H1] at h2
--       exact List.infix_cons (iht h2)
--     | (none, true) :: tail =>
--       simp [insert_one_to_none_true]
--       simp at h
--       specialize iht (insert_one (some a, false) tail) (by rw [insert_one_length]; exact h; rfl)
--       intro c d hcd
--       have H : remove_ones ((none, true) :: insert_one (some a, false) tail) = remove_ones (insert_one (some a, false) tail) := rfl
--       rw [H] at hcd
--       specialize iht c d hcd
--       exact List.infix_cons iht
--     | (none, false) :: tail =>
--       have H0 : tail = [] := by sorry
--       rw [H0]
--       intro c d hcd
--       have H1 : insert_one (some a, false) [(none, false)] = [(some a, false), (none, false)] := rfl
--       have H2 : remove_ones [(some a, false), (none, false)] = [(a, false)] := rfl
--       rw [H1, H2] at hcd
--       apply infix_length_le at hcd
--       simp at hcd

theorem move_ones_ind_rep : move_ones_ind (move_ones_ind L) = move_ones_ind L := by
  apply move_irreducible
  exact big_attempt

  -- have H : ∀ t L, L.length ≤ t → move_ones_ind (move_ones_ind L) = move_ones_ind L := by
  --   intro t
  --   induction t
  --   · intro L len
  --     simp at len
  --     simp [len]
  --   rename_i n ih0
  --   intro L
  --   induction L with
  --   | nil => simp
  --   | cons head tail =>
  --     intro len2
  --     simp at len2
  --     simp [move_ones_ind]
  --     match head with
  --     | (none, true) =>
  --       simp [insert_one_none_true, move_ones_none_true, insert_one_to_none_true, ih0 tail (by omega)]
  --     | (none, false) =>
  --       match h : move_ones_ind tail with
  --       | [] => simp
  --       | (none, true) :: tail1 =>
  --         simp [insert_one, move_ones_none_true]
  --         have H : ∃ tail3, move_ones_ind tail3 = tail1 := by sorry
  --         rcases H with ⟨tail3, ht3⟩
  --         rw [← ht3]
  --         have ht3_len : ((none, false) :: tail3).length ≤ n := by sorry
  --         exact ih0 ((none, false) :: tail3) ht3_len
  --       | (none, false) :: tail1 =>
  --         simp [move_ones_ind, insert_one]
  --         sorry

  --       | (some c, true) :: tail1 =>
  --         simp [insert_one, move_ones_ind]
  --         have H : ∃ tail3, move_ones_ind tail3 = tail1 := by sorry
  --         rcases H with ⟨tail3, ht3⟩
  --         rw [← ht3]
  --         have ht3_len : ((none, false) :: tail3).length ≤ n := by sorry
  --         have H3 := ih0 ((none, false) :: tail3) ht3_len
  --         change insert_one (some c, true) (move_ones_ind (move_ones_ind ((none, false) :: tail3))) = _
  --         rw [H3]
  --         match h1 : (move_ones_ind ((none, false) :: tail3)) with
  --         | [] =>
  --           simp
  --           change move_ones_ind ((none, false) :: tail3) = []
  --           exact h1
  --         | (none, true) :: tail2 =>
  --           simp [insert_one]
  --           sorry
  --         | _ => sorry

  --       | (some c, false) :: tail1 => sorry


  --     | (some c, true) => sorry
  --     | (some c, false) => sorry
  -- apply H L.length L (by omega)

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

  apply H _ _ _ rfl h h2

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
    intro L len irr
    intro c d h
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

-- theorem pt_sf_nf (h : irreducible ((none, false):: tail)): pairsTogether ((none, false) :: tail) →  pairsTogether ((some b, false) :: (none, false) :: tail) := by
--   intro h1 c d hcd
--   simp [remove_ones] at hcd
--   induction tail
--   · apply infix_length_le at hcd
--     simp at hcd
--   rename_i head tail1 ih
--   match head with
--   | (none, true) =>
--     specialize h 0
--     exfalso
--     apply h.2.2
--     use [], tail1
--     simp
--   | (some a, true) =>
--     specialize h a
--     exfalso
--     apply h.2.1
--     use [], tail1
--     simp
--   | (some a, false) =>
--     simp [remove_ones] at hcd
--     apply infix_cons_cons_ne_double at hcd
--     simp at hcd
--     suffices [(some c, false), (some d, true)] <:+: (some a, false) :: tail1 by
--       exact List.infix_cons (h1 c d hcd)
--     apply pt_less at h1
--     exact h1 c d hcd
--   | (none, false) =>
--     match tail1 with
--     | (none, true) :: tail2 => exfalso; specialize h 0; apply h.2.2; use [(none, false)]; use tail2; simp
--     | (none, false) :: tail2 => sorry
--     | (some b, true) :: tail2 => sorry
--     | (some b, false) :: tail2 => sorry


-- theorem pt_insert (h : pairsTogether L) : pairsTogether (insert_one a L) := by
--   have H : ∀ t a L, L.length = t → pairsTogether L → pairsTogether (insert_one a L) := by
--     intro t
--     induction t
--     · intro a L len
--       simp at len
--       simp [len]
--       intro _
--       exact pairs_together_singleton
--     intro a L len h
--     rename_i n ih
--     match a with
--     | (none, true) =>
--       simp
--       exact pt_true h
--     | (none, false) =>
--       match L with
--       | [] => simp at len
--       | (none, true) :: tail =>
--         simp [insert_one]
--         apply pt_true
--         apply ih
--         · simp at len
--           exact len
--         exact pt_less h
--       | (none, false) :: tail =>
--         simp [insert_one]
--         exact pt_nf_nf h
--       | (some c, true) :: tail1 =>
--         simp [insert_one]
--         apply pt_true
--         apply ih
--         · simp at len
--           exact len
--         exact pt_less h
--       | (some c, false) :: tail1 =>
--         simp [insert_one]
--         exact pt_some_false h
--     | (some b, true) =>
--       match L with
--       | [] => simp at len
--       | (none, true) :: tail =>
--         simp [insert_one]
--         exact pt_true h
--       | (none, false) :: tail =>
--         simp [insert_one]
--         exact pt_true h
--       | (some c, true) :: tail1 =>
--         simp [insert_one]
--         exact pt_true h
--       | (some c, false) :: tail1 =>
--         simp [insert_one]
--         exact pt_true h
--     | (some b, false) =>
--       match L with
--       | [] => simp at len
--       | (none, true) :: tail =>
--         simp [insert_one]
--         apply pt_true
--         apply ih
--         · simp at len
--           exact len
--         exact pt_less h
--       | (none, false) :: tail =>
--         simp [insert_one]
--         sorry -- g
--       | (some c, true) :: tail1 =>
--         simp [insert_one]
--         sorry
--       | (some c, false) :: tail1 =>
--         simp [insert_one]
--         exact pt_some_false h
--   exact H _ _ _ rfl h




-- theorem pt_move : pairsTogether (move_ones_ind L) := by
--   induction L
--   · simp [pairsTogether_empty]
--   rename_i ih
--   exact pt_insert ih
-- theorem foo_helper_ugh (n : ℕ) (iht : ∀ L, L.length ≤ n → pairsTogether (move_ones_ind L)) (h : L1.length ≤ n) :
--     pairsTogether (move_ones_ind (head::L1)) := by
--   unfold move_ones_ind
--   match head with
--   | (none, true) =>
--     simp [insert_one_none_true]
--     intro a b hab
--     have H : remove_ones ((none, true) :: (move_ones_ind L1)) = remove_ones (move_ones_ind L1) := rfl
--     rw [H] at hab
--     specialize iht L1 h a b hab
--     exact List.infix_cons iht
--   | (none, false) =>
--     intro a b hab
--     have H : remove_ones ((move_ones_ind L1) ++ [(none, false)]) = remove_ones (move_ones_ind L1) := by sorry
--     sorry
--     -- rw [H] at hab
--     -- specialize iht L1 h a b hab
--     -- refine List.infix_concat_iff.mpr ?_
--     -- right
    -- exact iht
  -- | (some a, true) =>
  --   match l_is : (move_ones_ind L1) with
  --   | [] => simp [pairs_together_singleton]
  --   | (some a1, snd) :: tail =>
  --     simp [insert_one_some_some]
  --     rw [← move_ones_ind_length, l_is] at h
  --     specialize iht ((some a1, snd) :: tail) h
  --     intro c d hcd
  --     have H : remove_ones ((some a, true) :: (some a1, snd) :: tail) = (a, true) :: remove_ones ((some a1, snd) :: tail) := rfl
  --     rw [H] at hcd
  --     have H2 : [(c, false), (d, true)] <:+: remove_ones ((some a1, snd) :: tail) := infix_cons_cons_ne hcd (by aesop)
  --     have H3 : [(c, false), (d, true)] <:+: remove_ones (move_ones_ind ((some a1, snd) :: tail)) := by
  --       rw [← l_is, move_ones_ind_rep, l_is]
  --       exact H2
  --     specialize (iht c d H3)
  --     rw [← l_is, move_ones_ind_rep, l_is] at iht
  --     exact List.infix_cons iht
  --   | (none, true) :: tail =>
  --     simp [insert_one_to_none_true]
  --     rw [← move_ones_ind_length, l_is] at h
  --     simp at h
  --     specialize iht (insert_one (some a, true) tail) (by rw [insert_one_length]; exact h; rfl)
  --     intro c d hcd
  --     have H : remove_ones ((none, true) :: insert_one (some a, true) tail) = remove_ones (insert_one (some a, true) tail) := rfl
  --     rw [H] at hcd
  --     have h4 : move_ones_ind (insert_one (some a, true) tail) = (insert_one (some a, true) tail) := by sorry
  --     have HCD : [(c, false), (d, true)] <:+: remove_ones (move_ones_ind (insert_one (some a, true) tail)) := by
  --       rw [h4]
  --       exact hcd
  --     specialize iht c d HCD
  --     rw [h4] at iht
  --     exact List.infix_cons iht
  --   | (none, false) :: tail =>
  --     have H : insert_one (some a, true) ((none, false) :: tail) = (some a, true) :: ((none, false) :: tail) := rfl
  --     rw [H]
  --     intro c d hcd
  --     have H2 : remove_ones ((some a, true) :: (none, false) :: tail) = (a, true) :: remove_ones ((none, false) :: tail) := rfl
  --     rw [H2] at hcd
  --     -- from hcd, because remover preserves infixes in this way

  --     sorry

  -- | (some a, false) =>
  --   match l_is : (move_ones_ind L1) with
  --   | [] => simp [pairs_together_singleton]
  --   | (some a1, snd) :: tail =>
  --     simp [insert_one_some_some]
  --     rw [← move_ones_ind_length, l_is] at h
  --     specialize iht ((some a1, snd) :: tail) h
  --     intro c d hcd
  --     have H : remove_ones ((some a, false) :: (some a1, snd) :: tail) = (a, false) :: (a1, snd) :: remove_ones tail := rfl
  --     rw [H] at hcd
  --     specialize iht c d
  --     rcases infix_cons_cons_def hcd with h1 | h2
  --     · simp at h1
  --       rw [h1.1, h1.2.1, h1.2.2]
  --       change _ <:+: [(some a, false), (some a1, true)] ++ tail
  --       exact infix_append_right (List.infix_refl [(some a, false), (some a1, true)])
  --     have H1 : (a1, snd) :: remove_ones tail = remove_ones ((a1, snd):: tail) := rfl
  --     rw [H1] at h2
  --     have H2 : move_ones_ind ((some a1, snd) :: tail)= ((some a1, snd) :: tail) := by
  --       rw [← l_is, move_ones_ind_rep]
  --     rw [← H2] at h2
  --     have h3 := iht h2
  --     rw [H2] at h3
  --     exact List.infix_cons h3
  --   | (none, true) :: tail =>
  --     simp [insert_one_to_none_true]
  --     rw [← move_ones_ind_length, l_is] at h
  --     simp at h
  --     specialize iht (insert_one (some a, false) tail) (by rw [insert_one_length]; exact h; rfl)
  --     intro c d hcd
  --     have H : remove_ones ((none, true) :: insert_one (some a, false) tail) = remove_ones (insert_one (some a, false) tail) := rfl
  --     rw [H] at hcd
  --     specialize iht c d
  --     have H4 : move_ones_ind (insert_one (some a, false) tail)= (insert_one (some a, false) tail) := by sorry -- write tail as move_ones something and then this is move_move
  --     rw [← H4] at hcd
  --     specialize iht hcd
  --     rw [H4] at iht
  --     exact List.infix_cons iht
  --   | (none, false) :: tail =>
  --     intro c d hcd
  --     simp [insert_one_to_none_false]
  --     simp [insert_one_to_none_false] at hcd
  --     exfalso
      --again the issue is with hcd
--       sorry

-- theorem foo_helper : pairsTogether (move_ones_ind L) := by
--   have H : ∀ t, L.length ≤ t → pairsTogether (move_ones_ind L) := by
--     intro t
--     induction t using Nat.strongRecOn generalizing L
--     rename_i n ih
--     intro l_len
--     cases L
--     · simp
--       exact pairsTogether_empty
--     rename_i head tail
--     apply foo_helper_ugh tail.length _ (by rfl)
--     intro L hL
--     simp at l_len
--     exact @ih tail.length (by omega) L hL
--   apply H L.length _
--   rfl

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


theorem equiv_move_ones' : SemiThue grid_style' L (move_ones_ind L) := by
  induction L
  · exact SemiThue.refl []
  rename_i head tail ih
  exact SemiThue.trans _ _ _ (SemiThue_cons ih) (equiv_insert)

#exit
@[simp]
theorem remove_ones_insert_ones : remove_ones (insert_one (none, b) L) = remove_ones L := by
  induction L
  · simp [remove_ones]
  rename_i head tail ih
  match head with
  | (none, true) => simp [insert_one, remove_ones, ih]
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
  | (none, true) => simp [insert_one, remove_ones, ih]
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

-- theorem foo_helper (iht : ∀ L, L.length < n + 1 → pairsTogether (move_ones_ind L)) (h : tail.length ≤ n) : pairsTogether (insert_one head (move_ones_ind tail)) := by
--   apply foo_helper'
-- · intro L l_len
  -- induction tail -- generalizing head
  -- · simp
  --   apply pairs_together_singleton
  -- rename_i h1 t1 ih1
  -- simp at h
  -- specialize ih1 (by omega)
  -- intro a b hab
  -- match head with
  -- | (none, true) =>
  --   rw [insert_one_none_true]
  --   rw [insert_one_none_true] at hab ih1
  --   unfold move_ones_ind at hab
  --   match h1 with
  --   | (none, true) =>
  --     rw [insert_one_none_true] at hab
  --     unfold move_ones_ind
  --     rw [insert_one_none_true]
  --     have H : remove_ones ((none, true) :: (none, true) :: move_ones_ind t1) = remove_ones ((none, true) :: move_ones_ind t1) := rfl
  --     rw [H] at hab
  --     specialize ih1 a b hab
  --     exact List.infix_cons ih1
  --   | (none, false) => sorry
  --   | (some d, true) => sorry
  --   | (some d, false) => sorry

  -- | (none, false) => sorry
  -- | (some c, true) => sorry
  -- | (some c, false) => sorry

theorem Semi_Thue_infix (h : SemiThue r a b) : ∀ c d, SemiThue r (c ++ a ++ d) (c ++ b ++ d) := by sorry

theorem SemiThue_refl : SemiThue r a a := by sorry

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

theorem rev_to_grid (h : SemiThue reversing a b) : ∃ a' b', SemiThue grid_style' a' b' ∧
  remove_ones a' = a ∧ remove_ones b' = b ∧ pairsTogether b':= by
  induction one_step_equiv_reg.mp h with
  | refl a =>
    use (List.map (fun (a, b) => (some a, b))) a
    use (List.map (fun (a, b) => (some a, b))) a
    constructor
    · exact SemiThue.refl ((List.map (fun (a, b) => (some a, b))) a)
    constructor
    · simp [remove_ones]
      sorry -- this is easy
    sorry -- again easy
  | one_step h1 h2 ih =>
    rename_i c d e f g
    specialize ih (one_step_equiv_reg.mpr h1)
    rcases ih with ⟨a', b', gr, a'_is, b'_is, pt_b⟩
    cases h2 with
    | basic =>
      rename_i i
      rcases pt_b i i (by use e; use f; exact b'_is.symm) with ⟨w, t, hwt⟩
      use a'
      rw [← hwt] at b'_is
      rw [remove_ones_append, remove_ones_append] at b'_is
      have splits : (remove_ones w = e ∧ remove_ones t = f) ∨
        (∃ w', remove_ones w = e ++ [(i, false), (i, true)] ++ w' ∧ remove_ones t = f ):= by sorry
      simp only [remove_ones] at b'_is
      rcases splits
      · use move_ones_ind (w ++ [(none, true), (none, false)] ++ t)
        constructor
        · apply SemiThue.trans _ _ _ gr
          have H : SemiThue grid_style' b' (w ++ [(none, true), (none, false)] ++ t) := by
            rw [← hwt]
            apply SemiThue.reduction
            exact grid_style'.basic i
          apply SemiThue.trans _ _ _ H
          exact equiv_move_ones -- basically a sorry
        constructor
        · exact a'_is
        constructor
        · rw [remove_ones_move_ones]
          rw [remove_ones_append, remove_ones_append]
          simp [remove_ones]
          sorry
        exact foo_helper -- basically a sorry
      rename_i h_s
      rcases h_s with ⟨w', hw⟩
      use move_ones_ind (w ++ [(some i, false), (some i, true)] ++ w ++ [(none, true), (none, false)] ++ t)
    | apart h_dist =>
      rename_i i j
      rcases pt_b i j (by use e; use f; exact b'_is.symm) with ⟨w, t, hwt⟩
      use a'
      use move_ones_ind (w ++ [(some j, true), (some i, false)] ++ t)
      constructor
      · apply SemiThue.trans _ _ _ gr
        have H : SemiThue grid_style' b' (w ++ [(some j, true), (some i, false)] ++ t) := by
          rw [← hwt]
          apply SemiThue.reduction
          exact grid_style'.apart h_dist
        apply SemiThue.trans _ _ _ H
        exact equiv_move_ones -- basically a sorry
      constructor
      · exact a'_is
      constructor
      · rw [remove_ones_move_ones]
        rw [← hwt] at b'_is
        rw [remove_ones_append, remove_ones_append] at b'_is
        rw [remove_ones_append, remove_ones_append]
        simp only [remove_ones, List.nil_append] at b'_is
        simp only [remove_ones]
        sorry -- basically a sorry
      exact foo_helper -- basically a sorry
    | close h_dist =>
      rename_i i j
      rcases pt_b i j (by use e; use f; exact b'_is.symm) with ⟨w, t, hwt⟩
      use a'
      use move_ones_ind (w ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ t)
      constructor
      · apply SemiThue.trans _ _ _ gr
        have H : SemiThue grid_style' b' (w ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ t) := by
          rw [← hwt]
          apply SemiThue.reduction
          exact grid_style'.close h_dist
        apply SemiThue.trans _ _ _ H
        exact equiv_move_ones -- basically a sorry
      constructor
      · exact a'_is
      constructor
      · rw [remove_ones_move_ones]
        rw [← hwt] at b'_is
        rw [remove_ones_append, remove_ones_append] at b'_is
        rw [remove_ones_append, remove_ones_append]
        simp only [remove_ones, List.nil_append] at b'_is
        simp only [remove_ones]
        sorry
      exact foo_helper -- basically a sorry


    -- now i kind of want to use b', somehow knowing that i can apply the reversing c d from hd
-- theorem add_ones (h : SemiThue reversing a b) : ∃ d, SemiThue grid_style
--     ((List.map fun (x, y) => (some x, y)) a) d ∧ remove_ones d = b := by
--   apply one_step_equiv_reg.mp at h
--   induction h with
--   | refl a =>
--     use (List.map (fun x ↦ (some x.1, x.2)) a)
--     constructor
--     · exact SemiThue.refl _
--     induction a with
--     | nil =>
--       simp only [List.map_nil, remove_ones]
--     | cons head tail ih =>
--       simp [List.map_cons, Prod.mk.eta, List.cons.injEq, true_and]
--       simp at ih
--       unfold remove_ones
--       rw [ih]
--   | one_step h1 h2 ih =>
--     simp at ih
--     rename_i c e f g i
--     rcases ih with ⟨d2, gd, hd⟩
--     simp
--     apply one_step_equiv_reg.mp at gd
--     sorry
