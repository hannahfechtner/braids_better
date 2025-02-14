import BraidProject.SemiThue
import BraidProject.Shortlex
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
      rw [ha, List.map_eq_nil.mp n_is.symm]
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

theorem reversing_iff_option_other_way : reversing_option a b  → reversing (remove_ones a) (remove_ones b) := by
  intro h
  induction h
  · simp only [remove_ones]
    exact reversing.basic
  · simp only [remove_ones]
    exact reversing.apart (by assumption)
  simp only [remove_ones]
  exact reversing.close (by assumption)

def option_rel : Option ℕ → Option ℕ → Prop := fun a b =>
  match (a, b) with
  | (_, none) => False
  | (none, some _) => True
  | (some i, some j) => i < j

instance bye : WellFoundedRelation (Option ℕ) where
  rel := option_rel
  wf := by
    apply WellFounded.intro
    intro a
    induction a with
    | none =>
      apply Acc.intro
      intro y y_lt
      unfold option_rel at y_lt
      simp only at y_lt
    | some val =>
      induction val with
      | zero =>
        apply Acc.intro
        intro y y_lt
        induction y with
        | none =>
          apply Acc.intro
          intro y y_lt
          unfold option_rel at y_lt
          simp only at y_lt
        | some val =>
          unfold option_rel at y_lt
          simp only at y_lt
          linarith [y_lt]
      | succ n ih =>
        apply Acc.intro
        intro y
        intro y_lt
        rcases ih
        rename_i acc_n
        rcases y
        · apply Acc.intro
          intro y y_lt
          unfold option_rel at y_lt
          simp only at y_lt
        rename_i m
        rcases Nat.lt_or_ge m n with h1 | h2
        · exact acc_n m h1
        rcases LE.le.eq_or_gt h2 with h3 | h4
        · apply Acc.intro
          intro y' y'lt
          rw [h3] at y'lt
          exact acc_n y' y'lt
        unfold option_rel at y_lt
        simp only [lt_self_iff_false] at y_lt
        linarith

def find_it (L : List α) (r : List α) : Option (List α × List α × List α) := sorry

instance hi : WellFounded (Shortlex lt_a) := by
  apply Shortlex.wf
  exact wf_ar
def move_ones (a : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
  match find_it a [(none, false), (none, true)] with
  | none => a
  | some (c, d, e) =>
    have ha : Shortlex lt_a (c++ [(none, true), (none, false)] ++e) a := by sorry
    have hb : Shortlex lt_a (c++ [(none, true), (none, false)] ++e) (c++ [(none, false), (none, true)] ++e) := by sorry
    have hc : Shortlex lt_a [(none, true), (none, false)] [((none : Option ℕ), false), (none, true)]:= by sorry
    have H : (invImage (fun x ↦ Shortlex lt_a) instWellFoundedRelationOfSizeOf).1 (c ++ [(none, true), (none, false)] ++ e) a := by
      simp
      sorry --refine ha
    move_ones (c++ [(none, true), (none, false)] ++e)
    termination_by (Shortlex lt_a)
    decreasing_by exact H --sorry

  --   move_ones (c++ [(true, none), (false, none)] ++e)
  -- | none => sorry
  -- termination_by (List.Lex symbol_lt)
  -- decreasing_by sorry
  -- -- simp





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
