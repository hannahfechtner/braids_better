import Mathlib.Data.Nat.Dist
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lex
import BraidProject.Cancellability

inductive SemiThue (rels : List α → List α → Prop) : List α → List α → Prop
| refl (a : List α) : SemiThue rels a a
| reduction {a b c d : List α} (h : rels a b) : SemiThue rels (c++a++d) (c++b++d)
| trans (a b c : List α) : SemiThue rels a b → SemiThue rels b c → SemiThue rels a c

inductive SemiThue_one_step (rels : List α → List α → Prop) : List α → List α → Prop
| refl (a : List α) : SemiThue_one_step rels a a
| one_step {a b c d e : List α} (h1 : SemiThue_one_step rels e (c++a++d)) (h2 : rels a b) :
    SemiThue_one_step rels e (c++b++d)

private theorem one_step_in_front {a b c d e : List α} (h1 : SemiThue_one_step rels (c++a++d) e)
    (h2 : rels b a) : SemiThue_one_step rels (c++b++d) e := by
  have H : ∀ f, SemiThue_one_step rels f e → f = c ++ a ++ d →
      SemiThue_one_step rels (c ++ b ++ d) e := by
    intro f hf
    induction hf
    · intro f_is
      rw [f_is]
      rw [f_is] at h1
      exact SemiThue_one_step.one_step (SemiThue_one_step.refl _) h2
    rename_i l m n
    intro k_is
    rw [k_is] at l
    exact SemiThue_one_step.one_step (n l k_is) m
  exact H _ h1 rfl

private theorem one_step_trans (h1 : SemiThue_one_step rels a b) (h2 : SemiThue_one_step rels b c) :
    SemiThue_one_step rels a c := by
  induction h1
  · assumption
  rename_i d e f g h i j k
  have H : ∀ l, SemiThue_one_step rels l c → l = (f ++ e ++ g) → SemiThue_one_step rels h c := by
    intro l
    intro hl
    induction hl
    · intro l_is
      rw [l_is]
      exact SemiThue_one_step.one_step i j
    intro l_is
    rename_i m n o p q r s t
    rw [l_is] at r t
    apply k
    exact one_step_in_front h2 j
  exact H _ h2 rfl

theorem one_step_equiv_reg {a b : List α} : SemiThue rels a b ↔ SemiThue_one_step rels a b := by
  constructor
  · intro h
    induction h
    · exact SemiThue_one_step.refl _
    · rename_i c d _ _ h
      exact SemiThue_one_step.one_step (SemiThue_one_step.refl _) h
    rename_i ih1 ih2
    exact one_step_trans ih1 ih2
  intro h
  induction h
  · exact SemiThue.refl _
  rename_i h1 h2
  apply h2.trans
  exact SemiThue.reduction h1


inductive reversing : List (Bool × ℕ) → List (Bool × ℕ) → Prop
| basic {n : ℕ} : reversing [(false, n), (true, n)] []
| apart {i j : ℕ} (h : Nat.dist i j > 1) : reversing [(false, i), (true, j)] [(true, j), (false, i)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : reversing [(false, i), (true, j)]
    [(true, j), (true, i), (false, j), (false, i)]

inductive reversing_option : List (Bool × Option ℕ) → List (Bool × Option ℕ) → Prop
| basic {n : ℕ} : reversing_option [(false, n), (true, n)] []
| apart {i j : ℕ} (h : Nat.dist i j > 1) : reversing_option [(false, i), (true, j)]
    [(true, j), (false, i)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : reversing_option [(false, i), (true, j)]
    [(true, j), (true, i), (false, j), (false, i)]

inductive grid_style : List (Bool × Option ℕ) → List (Bool × Option ℕ) → Prop
| basic {n : ℕ} : grid_style [(false, some n), (true, some n)] [(true, none), (false, none)]
| over {n : ℕ} : grid_style [(false, n), (true, none)] [(true, none), (false, some n)]
| up {n : ℕ} : grid_style [(false, none), (true, some n)] [(true, some n), (false, none)]
| empty : grid_style [(false, none), (true, none)] [(true, none), (false, none)]
| apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style [(false, i), (true, j)] [(true, j), (false, i)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style [(false, i), (true, j)]
    [(true, j), (true, i), (false, j), (false, i)]

-- theorem List.length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
--   ⟨fun _ => let [a, b] := l; ⟨a, b, rfl⟩, fun ⟨_, _, e⟩ => e ▸ rfl⟩

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

theorem prod_some (h : (i.1, some i.2) = (j, some b)) : i = (j, b) := by
  simp at h
  rw [← h.1, ← h.2]

theorem reversing_iff_option : reversing a b ↔ reversing_option (List.map (fun (x, y) =>
    (x, some y)) a) (List.map (fun (x, y) => (x, some y)) b) := by
  constructor
  · intro h
    induction h
    · exact reversing_option.basic
    · exact reversing_option.apart (by assumption)
    exact reversing_option.close (by assumption)
  intro h
  have H : ∀ m n, reversing_option m n → m = List.map (fun x ↦ (x.1, some x.2)) a →
      n = (List.map (fun x ↦ (x.1, some x.2)) b) → reversing a b := by
    intro m n
    intro h
    induction h
    · intro m_is n_is
      rename_i k
      have ha : a = [(false, k), (true, k)] := by
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
          · exact m_is.1.1
          exact m_is.1.2.symm
        simp
        ext
        · exact m_is.2.1
        exact m_is.2.2.symm
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

def remove_ones : List (Bool × Option α) → List (Bool × α) :=
  fun a => match a with
  | [] => []
  | (a, some b) :: c => (a, b) :: remove_ones c
  | (_, none) :: c => remove_ones c

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

instance : WellFoundedRelation (Bool × Option ℕ) := by infer_instance

instance : LT (List (Bool × Option ℕ)) where
  lt := List.Lex (Prod.Lex (fun (a b : Bool) => a < b) option_rel)

instance : IsTrichotomous (Bool × Option ℕ) (Prod.Lex (fun (a b : Bool) => a < b) option_rel) where
  trichotomous := by
    intro a b
    match a with
    | (false, none) =>
      match b with
      | (true, _) =>
        left
        exact Prod.Lex.left none _ rfl
      | (false, none) =>
        right; left
        rfl
      | (false, some j) =>
        left
        exact Prod.Lex.right false trivial
    | (false, some i) =>
      match b with
      | (true, _) =>
        left
        exact Prod.Lex.left (some i) _ rfl
      | (false, none) =>
        right; right
        exact Prod.Lex.right false trivial
      | (false, some j) =>
        have H : i < j ∨ i = j ∨ i > j := by exact trichotomous i j
        rcases H with h1 | h2
        · left
          exact Prod.Lex.right false h1
        rcases h2 with h3 | h4
        · right; left
          rw [h3]
        right; right
        exact Prod.Lex.right false h4
    | (true, none) =>
      match b with
      | (false, _) =>
        right; right; exact Prod.Lex.left _ none rfl
      | (true, none) => right; left; rfl
      | (true, some j) => left; exact Prod.Lex.right true trivial
    | (true, some i) =>
      match b with
      | (false, _) => right; right; exact Prod.Lex.left _ (some i) rfl
      | (true, none) => right; right; exact Prod.Lex.right true trivial
      | (true, some j) =>
      have H : i < j ∨ i = j ∨ i > j := by exact trichotomous i j
      rcases H with h1 | h2
      · left
        exact Prod.Lex.right true h1
      rcases h2 with h3 | h4
      · right; left
        rw [h3]
      right; right
      exact Prod.Lex.right true h4

instance {r : α → α → Prop} [IsTrichotomous α r] : IsTrichotomous (List α) (List.Lex r) where
  trichotomous := by
    intro a
    induction a with
    | nil =>
      intro b
      cases b with
      | nil => right; left; rfl
      | cons head tail => left; exact List.Lex.nil
    | cons head tail ih =>
      intro b
      cases b with
      | nil => right; right; exact List.Lex.nil
      | cons head1 tail1  =>
        have H : r head head1 ∨ head = head1 ∨ r head1 head := trichotomous head head1
        rcases H with h1 | h2
        · left
          exact List.Lex.rel h1
        rcases h2 with h3 | h4
        · rw [h3]
          rcases ih tail1 with h1 | h2
          · left
            exact List.Lex.cons h1
          rcases h2 with h4 | h5
          · rw [h4]
            right; left
            rfl
          right; right
          exact List.Lex.cons h5
        right; right
        exact List.Lex.rel h4

instance : IsTrichotomous (List (Bool × Option ℕ))
    (List.Lex (Prod.Lex (fun (a b : Bool) => a < b) option_rel)) := by infer_instance

instance : WellFoundedRelation (List (Bool × Option ℕ)) where
  rel := List.Lex (Prod.Lex (fun (a b : Bool) => a < b) option_rel)
  wf := by
    apply WellFounded.intro
    intro y
    apply Acc.intro
    intro a h
    cases h with
    | nil =>
      apply Acc.intro
      intro y ylt
      exfalso
      simp only [List.Lex.not_nil_right] at ylt
    | cons h =>
      rename_i c l1 l2
      apply Acc.intro; intro y ylt
      sorry
    | rel h => sorry

-- def find_it (L : List α) (r : List α) : Option (List α × List α × List α) := sorry

-- #check InvImage

-- def move_ones' : Bool × Option ℕ → Bool × Option ℕ  → Prop
--   | (false, none) =>
--     move_ones' (false, none)
--   | _ => fun x => false


-- def move_ones (a : FreeMonoid' (Bool × Option ℕ)) : FreeMonoid' (Bool × Option ℕ) :=
  -- match find_it a [(false, none), (true, none)] with
  -- | some (c, d, e) =>
  --   have : a > (c++ [(true, none), (false, none)] ++e) := by sorry
  --   --have : (c++ [(false, none), (true, none)] ++e) > (c++ [(true, none), (false, none)] ++e) := by sorry
  --   have : [((none : Option ℕ), false), (true, none)] > [(true, none), (false, none)] := by
  --     change List.Lex symbol_lt _ _
  --     apply List.Lex.rel
  --     rfl
  --   have : (c++ [(false, none), (true, none)] ++e) > (c++ [(true, none), (false, none)] ++e) := by
  --     change List.Lex symbol_lt _ _
  --     induction c
  --     · simp
  --       exact List.Lex.rel rfl
  --     rename_i hk tk ihk
  --     simp
  --     refine List.Lex.cons ?cons.h
  --     --simp
  --     simp at ihk
  --     apply ihk
  --     sorry


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
