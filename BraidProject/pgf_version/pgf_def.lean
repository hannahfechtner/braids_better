import BraidProject.Grids_C
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.PartialGrid_bounded

inductive pgf : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → Type
  | skeleton (a b) (ha : a.length > 0) (ha1 : is_false a) (hb : b.length > 0) (hb : is_true b ):
      pgf a b (a ++ b)
  | empty (h : pgf a b c) (hc : c = c1 ++ [(none, false), (none, true)] ++ c2) :
      pgf a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | top_bottom (i : ℕ) (h : pgf a b c) (hc : c = c1 ++ [(none, false), (some i, true)] ++ c2) :
      pgf a b (c1 ++ [(some i, true), (none, false)] ++ c2)
  | sides (i : ℕ) (h : pgf a b c) (hc : c = (c1 ++ [(some i, false), (none, true)] ++ c2)) :
      pgf a b (c1 ++ [(none, true), (some i, false)] ++ c2)
  | top_left (i : ℕ) (h : pgf a b c) (hc : c = (c1 ++ [(some i, false), (some i, true)] ++ c2)) :
      pgf a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | adjacent (i j : ℕ) (hd : Nat.dist i j = 1) (h : pgf a b c)
      (hc : c = (c1 ++ [(some i, false), (some j, true)] ++ c2)) :
      pgf a b (c1 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c2)
  | separated (i k : ℕ) (hd : Nat.dist i k ≥ 2) (h : pgf a b c)
     (hc : c = c1 ++ [(some i, false), (some k, true)] ++ c2) :
      pgf a b (c1 ++ [(some k, true), (some i, false)] ++ c2)

inductive grid_style_real : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| basic (n : ℕ) : grid_style_real [(some n, false), (some n, true)] [(none, true), (none, false)]
| apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style_real [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style_real [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]



-- inductive pgf1 : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
--   List (Option ℕ × Bool) → Type
--   | skeleton (a b) (ha : a.length > 0) (ha1 : is_false a) (hb : b.length > 0) (hb : is_true b ):
--       pgf1 a b (a ++ b)
--   | empty (h : pgf1 a b (c1 ++ [(none, false), (none, true)] ++ c2)) :
--       pgf1 a b (c1 ++ [(none, true), (none, false)] ++ c2)
--   | top_bottom (i : ℕ) (h : pgf1 a b (c1 ++ [(none, false), (some i, true)] ++ c2)) :
--       pgf1 a b (c1 ++ [(some i, true), (none, false)] ++ c2)
--   | sides (i : ℕ) (h : pgf1 a b (c1 ++ [(some i, false), (none, true)] ++ c2)) :
--       pgf1 a b (c1 ++ [(none, true), (some i, false)] ++ c2)
--   | top_left (i : ℕ) (h : pgf1 a b (c1 ++ [(some i, false), (some i, true)] ++ c2)) :
--       pgf1 a b (c1 ++ [(none, true), (none, false)] ++ c2)
--   | adjacent (i j : ℕ) (hd : Nat.dist i j = 1) (h : pgf1 a b (c1 ++ [(some i, false), (some j, true)] ++ c2)) :
--       pgf1 a b (c1 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c2)
--   | separated (i k : ℕ) (hd : Nat.dist i j ≥ 2) (h : pgf1 a b (c1 ++ [(some i, false), (some k, true)] ++ c2)) :
--       pgf1 a b (c1 ++ [(some k, true), (some i, false)] ++ c2)

def pgf.length (h : pgf a b c) : Nat :=
  match h with
  | pgf.skeleton _ _ _ _ _ _ => 0
  | pgf.empty h _ => pgf.length h
  | pgf.top_bottom i h _ => pgf.length h
  | pgf.sides _ h _ => pgf.length h
  | pgf.top_left _ h _ => pgf.length h + 1
  | pgf.adjacent _ _ _ h _ => pgf.length h + 1
  | pgf.separated _ _ _ h _ => pgf.length h + 1

-- def pgf1.length (h : pgf1 a b c) : Nat :=
--   match h with
--   | pgf1.skeleton _ _ _ _ _ _ => 0
--   | pgf1.empty h => pgf1.length h
--   | pgf1.top_bottom i h => pgf1.length h
--   | pgf1.sides _ h => pgf1.length h
--   | pgf1.top_left _ h => pgf1.length h + 1
--   | pgf1.adjacent _ _ _ h => pgf1.length h + 1
--   | pgf1.separated _ _ _ h => pgf1.length h + 1

noncomputable def pgf_left_false (h : pgf a b c) : is_false a := by
  induction h; all_goals assumption

noncomputable def pgf_top_true (h : pgf a b c) : is_true b := by
  induction h; all_goals assumption

noncomputable def add_cell_w_len (h : pgf a b c)
    (hg : grid_style_real i j) (fe : c = k ++ i ++ l) :
    Σ c', (h1 : pgf a b c') × PLift (c' = k ++ j ++ l) ×
    PLift (h.length < h1.length) := by
  cases hg with
  | basic n =>
    use k ++ [(none, true), (none, false)] ++ l
    use pgf.top_left _ h fe
    constructor
    constructor
    simp [pgf.length]
    constructor
    simp [pgf.length]
  | apart hd =>
    rename_i i j
    use k ++ [(some j, true), (some i, false)] ++ l
    use pgf.separated _ _ hd h fe
    constructor
    constructor
    simp [pgf.length]
    constructor
    simp [pgf.length]
  | close hd =>
    rename_i i j
    use k ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ l
    use pgf.adjacent _ _ hd h fe
    constructor
    constructor
    simp [pgf.length]
    constructor
    simp [pgf.length]
-- def get_maximal_true_prefix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
--   match c with
--   | [] => []
--   | (_, false) :: _ => []
--   | (d, true) :: e => [(d, true)] ++ get_maximal_true_prefix e

-- def get_maximal_false_suffix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) := by
--   cases c using List.reverseRecOn with
--   | nil => exact []
--   | append_singleton l a _ =>
--     match a with
--     | (_, true) => exact []
--     | (d, false) => exact get_maximal_false_suffix l ++ [(d, false)]
--   termination_by c.length

-- def remove_maximal_true_prefix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
--   match c with
--   | [] => []
--   | (d, false) :: e => (d, false) :: e
--   | (_, true) :: e => remove_maximal_true_prefix e

-- def remove_maximal_false_suffix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) := by
--   cases c using List.reverseRecOn with
--   | nil => exact []
--   | append_singleton l a _ =>
--     match a with
--     | (d, true) => exact l ++ [(d, true)]
--     | (d, false) => exact remove_maximal_false_suffix l
--   termination_by c.length

-- theorem remove_maximal_false_suffix_nil : remove_maximal_false_suffix [] = [] := by
--   unfold remove_maximal_false_suffix
--   simp

-- theorem remove_maximal_false_suffix_append_false :
--   remove_maximal_false_suffix (a ++ [(b, false)]) = remove_maximal_false_suffix a := by
--   unfold remove_maximal_false_suffix
--   simp
--   exact remove_maximal_false_suffix.eq_def a

-- theorem get_maximal_false_suffix_append_false : get_maximal_false_suffix (a ++ [(b, false)]) =
--   get_maximal_false_suffix a ++ [(b, false)] := by
--   unfold get_maximal_false_suffix
--   simp
--   exact get_maximal_false_suffix.eq_def a


-- def pgf_get_bottom (h : pgf a b c) := get_maximal_true_prefix c

-- def pgf_get_right (h : pgf a b c) := get_maximal_false_suffix c

-- def pgf_get_middle (h : pgf a b c) :=
--   remove_maximal_true_prefix (remove_maximal_false_suffix c)

-- theorem get_prefix_append_remove_prefix : get_maximal_true_prefix a ++ remove_maximal_true_prefix a = a := by
--   induction a with
--   | nil => simp [get_maximal_true_prefix, remove_maximal_true_prefix]
--   | cons d e ih =>
--     match d with
--     | (d1, false) =>
--       simp [get_maximal_true_prefix, remove_maximal_true_prefix, ih]
--     | (d2, true) =>
--       simp [get_maximal_true_prefix, remove_maximal_true_prefix, ih]

-- theorem remove_suffix_append_get_suffix : remove_maximal_false_suffix a ++ get_maximal_false_suffix a = a := by
--   induction a using List.reverseRecOn with
--   | nil => unfold remove_maximal_false_suffix get_maximal_false_suffix; simp
--   | append_singleton l d ih =>
--     match d with
--     | (d1, true) =>
--       unfold remove_maximal_false_suffix get_maximal_false_suffix; simp [ih]
--     | (d2, false) =>
--       rw [remove_maximal_false_suffix_append_false, get_maximal_false_suffix_append_false, ← List.append_assoc, ih]

-- theorem pgf_split_bottom_middle_right (h : pgf a b c) :
--   pgf_get_bottom h ++ pgf_get_middle h ++ pgf_get_right h = c := by
--   unfold pgf_get_bottom pgf_get_middle pgf_get_right
--   sorry

theorem true_false_not_in_spine (h : c1 ++ [(c2, true), (c3, false)] ++ c4 = a ++ b)
    (ha : is_false a) (hb : is_true b) : False := by
  have : c1 ++ [(c2, true), (c3, false)] ++ c4 =
    c1 ++ [(c2, true)] ++ ([(c3, false)] ++ c4) := by simp
  rw [this] at h
  rcases List.append_eq_append_iff.mp h with ⟨m, hm1, hm2⟩ | ⟨m, hm1, hm2⟩
  · rw [hm1] at ha
    specialize ha (c2, true) ⟨by simp⟩
    simp only [Bool.true_eq_false] at ha
    exact ha.1
  rw [hm2] at hb
  specialize hb (c3, false) ⟨by simp⟩
  simp only [Bool.false_eq_true] at hb
  exact hb.1

theorem pgf_length_skeleton (h : pgf a b c) (hc : c = a ++ b) : h.length = 0 := by
  induction h with
  | skeleton a b ha hb =>
    simp [pgf.length]
  | empty h =>
    exact (true_false_not_in_spine hc (pgf_left_false h) (pgf_top_true h)).elim
  | top_bottom i h ih =>
    exact (true_false_not_in_spine hc (pgf_left_false h) (pgf_top_true h)).elim
  | sides i h ih =>
    exact (true_false_not_in_spine hc (pgf_left_false h) (pgf_top_true h)).elim
  | top_left i h ih =>
    exact (true_false_not_in_spine hc (pgf_left_false h) (pgf_top_true h)).elim
  | adjacent i j hd h hc ih =>
    rename_i c5 c6 _
    have : c5 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c6  =
      (c5 ++ [(some j, true)]) ++ [(some i, true), (some j, false)] ++ ((some i, false) :: c6) := by simp
    rw [this] at hc
    exact (true_false_not_in_spine hc (pgf_left_false h) (pgf_top_true h)).elim
  | separated i k h h ih =>
    exact (true_false_not_in_spine hc (pgf_left_false h) (pgf_top_true h)).elim

-- noncomputable def triple_no_overlap'
--  (h : m ++ [(some i, true), (none, false)] ++ n =
--   p ++ [(some j', true), (some i', true), (some j', false), (some i', false)] ++ q) :
--  (Σ m1 m2, PLift (m1 = p ∧ m1 ++ [(some j', true), (some i', true), (some j', false), (some i', false)] ++ m2 = m ∧
--  m2 ++ [(some i, true), (none, false)] ++ n = q)) ⊕
--  (List.Infix' [(none, true), (none, false)] n) := by sorry

-- noncomputable def pgf_extend_side (h : pgf a b c) (d : List (Option ℕ × Bool)) (hd : is_true d):
--   pgf a (b ++ d) (c ++ d) := by
--   induction h with
--   | skeleton a b ha ha1 hb hb1 =>
--     have H := pgf.skeleton a (b ++ d) ha ha1 (by simp [hb]) (is_true_of_true_true hb1 hd)
--     rw [← List.append_assoc] at H
--     use H
--   | empty h ih =>
--     rename_i l m n o
--     rw [List.append_assoc _ o d] at ih
--     have H := pgf.empty ih
--     rw [← List.append_assoc] at H
--     use H
--   | top_bottom i h ih =>
--     rename_i l m n o
--     rw [List.append_assoc _ o d] at ih
--     have H := pgf.top_bottom i ih
--     rw [← List.append_assoc] at H
--     use H
--   | sides i h ih =>
--     rename_i l m n o
--     rw [List.append_assoc _ o d] at ih
--     have H := pgf.sides i ih
--     rw [← List.append_assoc] at H
--     use H
--   | top_left i h ih =>
--     rename_i l m n o p q
--     rw [ih, List.append_assoc _ p d] at q
--     have H := pgf.top_left i q rfl
--     rw [← List.append_assoc] at H
--     use H
--   | adjacent i j hd h ih =>
--     rename_i l m n o
--     rw [List.append_assoc _ o d] at ih
--     have H := pgf.adjacent i j hd ih
--     rw [← List.append_assoc] at H
--     use H
--   | separated i k hd h ih =>
--     rename_i l m n o
--     rw [List.append_assoc _ o d] at ih
--     have H := pgf.separated i k hd ih
--     rw [← List.append_assoc] at H
--     use H

-- noncomputable def pgf_extend_bottom (h : pgf a b c) (d : List (Option ℕ × Bool)) (hd : is_false d):
--   pgf (d ++ a) b (d ++ c) := by
--   induction h with
--   | skeleton a b ha ha1 hb hb1 =>
--     have H := pgf.skeleton (d ++ a) b (by simp [ha]) (is_false_of_false_false hd ha1) hb hb1
--     rw [List.append_assoc d a b] at H
--     use H
--   | empty h ih =>
--     rename_i l m n o
--     rw [← List.append_assoc d, ← List.append_assoc] at ih
--     have H := pgf.empty ih
--     rw [← List.append_assoc, ← List.append_assoc]
--     use H
--   | top_bottom i h ih =>
--     rename_i l m n o
--     rw [← List.append_assoc d, ← List.append_assoc] at ih
--     have H := pgf.top_bottom i ih
--     rw [← List.append_assoc, ← List.append_assoc]
--     use H
--   | sides i h ih =>
--     rename_i l m n o
--     rw [← List.append_assoc d, ← List.append_assoc] at ih
--     have H := pgf.sides i ih
--     rw [← List.append_assoc, ← List.append_assoc]
--     use H
--   | top_left i h ih =>
--     rename_i l m n o p q
--     rw [ih, ← List.append_assoc d, ← List.append_assoc] at q
--     have H := pgf.top_left i q rfl
--     rw [← List.append_assoc, ← List.append_assoc]
--     use H
--   | adjacent i j hd h ih =>
--     rename_i l m n o
--     rw [← List.append_assoc d, ← List.append_assoc] at ih
--     have H := pgf.adjacent i j hd ih
--     rw [← List.append_assoc, ← List.append_assoc]
--     use H
--   | separated i k hd h ih =>
--     rename_i l m n o
--     rw [← List.append_assoc d, ← List.append_assoc] at ih
--     have H := pgf.separated i k hd ih
--     rw [← List.append_assoc, ← List.append_assoc]
--     use H

def rw_length (h : SemiThue grid_style a b) : ℕ :=
  match h with
  | SemiThue.refl a => 0
  | SemiThue.reduction h =>
    match h with
    | grid_style.basic n => 1
    | grid_style.over n => 0
    | grid_style.up n => 0
    | grid_style.empty => 0
    | grid_style.apart h => 1
    | grid_style.close h => 1
  | SemiThue.trans a _ c h1 h2 => rw_length h1 + rw_length h2

def rw_length_one_step (h : SemiThue_one_step  grid_style a b) : ℕ :=
  match h with
  | SemiThue_one_step.refl a => 0
  | SemiThue_one_step.one_step h1 h =>
    match h with
    | grid_style.basic n => rw_length_one_step h1 + 1
    | grid_style.over n => rw_length_one_step h1 + 0
    | grid_style.up n => rw_length_one_step h1 + 0
    | grid_style.empty => rw_length_one_step h1 + 0
    | grid_style.apart h => rw_length_one_step h1 + 1
    | grid_style.close h => rw_length_one_step h1 + 1

private noncomputable def one_step_trans
  (h1 : SemiThue_one_step grid_style a b) (h2 : SemiThue_one_step grid_style b c) :
    (h3 : SemiThue_one_step grid_style a c) ×
    PLift (rw_length_one_step h3 = rw_length_one_step h1 + rw_length_one_step h2) := by
  induction h2
  · use h1
    constructor
    simp [rw_length_one_step]
  rename_i d e f g h i j k
  specialize k h1
  rcases k with ⟨h4, len4⟩
  cases j with
  | basic n =>
    use h4.one_step (grid_style.basic n)
    constructor
    rw [rw_length_one_step, rw_length_one_step, len4.1, add_assoc]
  | over n =>
    use h4.one_step (grid_style.over n)
    constructor
    rw [rw_length_one_step, rw_length_one_step, len4.1, add_assoc]
  | up n =>
    use h4.one_step (grid_style.up n)
    constructor
    rw [rw_length_one_step, rw_length_one_step, len4.1, add_assoc]
  | empty =>
    use h4.one_step (grid_style.empty)
    constructor
    rw [rw_length_one_step, rw_length_one_step, len4.1, add_assoc]
  | apart h =>
    use h4.one_step (grid_style.apart h)
    constructor
    rw [rw_length_one_step, rw_length_one_step, len4.1, add_assoc]
  | close h =>
    use h4.one_step (grid_style.close h)
    constructor
    rw [rw_length_one_step, rw_length_one_step, len4.1, add_assoc]

theorem foo {a b c d : ℕ} (h : a = b) (h1 : c = d) : a + c = b + d :=
  Mathlib.Tactic.Ring.add_congr h h1 rfl

noncomputable def one_step_of_reg_w_len {a b} :
    ((h1 : SemiThue grid_style a b )→ (Σ h2 : SemiThue_one_step grid_style a b,
    PLift (rw_length h1 = rw_length_one_step h2) )) := by
  intro h
  induction h
  · use SemiThue_one_step.refl _
    constructor
    simp [rw_length, rw_length_one_step]
  · rename_i c d e f h
    use SemiThue_one_step.one_step (SemiThue_one_step.refl _) h
    constructor
    cases h
    all_goals rw [rw_length, rw_length_one_step, rw_length_one_step]
  rename_i ih1 ih2
  use (one_step_trans ih1.1 ih2.1).1
  constructor
  rw [rw_length, (one_step_trans ih1.1 ih2.1).2.1]
  exact Mathlib.Tactic.Ring.add_congr ih1.2.1 ih2.2.1 rfl

noncomputable def reg_of_one_step_w_len :
    (h1 : SemiThue_one_step grid_style a b) → (Σ h2 : SemiThue grid_style a b,
    PLift (rw_length h2 = rw_length_one_step h1)) := by
  intro h1
  induction h1
  · use SemiThue.refl _
    constructor
    simp [rw_length, rw_length_one_step]
  rename_i h1 h2
  use h2.1.trans _ _ _ (SemiThue.reduction h1)
  constructor
  rw [rw_length, h2.2.1]
  cases h1
  all_goals rw [rw_length_one_step, rw_length]

noncomputable def pgf_of_st (h : SemiThue grid_style ab c) (hab : ab = a ++ b)
  (ha : is_false a) (hal : a.length > 0) (hb : is_true b) (hbl : b.length > 0) :
  pgf a b c := by
  apply one_step_equiv_reg.1 at h
  induction h with
  | refl d =>
    rw [hab]
    exact pgf.skeleton a b hal ha hbl hb
  | one_step h1 h2 ih =>
    rename_i d e f g l
    specialize ih hab
    rcases h2
    · use pgf.top_left _ ih rfl
    · use pgf.sides _ ih rfl
    · use pgf.top_bottom _ ih rfl
    · use pgf.empty ih rfl
    · use pgf.separated _ _ (by assumption) ih rfl
    use pgf.adjacent _ _ (by assumption) ih rfl

noncomputable def SemiThue_empty_w_len : {h : SemiThue grid_style [(none, false), (none, true)] [(none, true), (none, false)] // rw_length h = 0}:= by
  rw [← List.nil_append [(none, false), (none, true)], ← List.nil_append [(none, true), (none, false)],
    ← List.append_nil ([] ++ [(none, false), (none, true)]), ← List.append_nil ([] ++ [(none, true), (none, false)])]
  use SemiThue.reduction (grid_style.empty)
  simp [rw_length]

noncomputable def SemiThue_top_bottom_w_len (i : ℕ) :
  {h : SemiThue grid_style [(none, false), (some i, true)] [(some i, true), (none, false)] // rw_length h = 0} := by
  rw [← List.nil_append [(none, false), (some i, true)], ← List.nil_append [(some i, true), (none, false)],
    ← List.append_nil ([] ++ [(none, false), (some i, true)]), ← List.append_nil ([] ++ [(some i, true), (none, false)])]
  use SemiThue.reduction (grid_style.up i)
  simp [rw_length]

noncomputable def SemiThue_sides_w_len (i : ℕ) :
  {h : SemiThue grid_style [(some i, false), (none, true)] [(none, true), (some i, false)] // rw_length h = 0} := by
  rw [← List.nil_append [(some i, false), (none, true)], ← List.nil_append [(none, true), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (none, true)]), ← List.append_nil ([] ++ [(none, true), (some i, false)])]
  use SemiThue.reduction (grid_style.over i)
  simp [rw_length]

noncomputable def SemiThue_top_left_w_len (i : ℕ) :
  {h : SemiThue grid_style [(some i, false), (some i, true)] [(none, true), (none, false)] // rw_length h = 1} := by
  rw [← List.nil_append [(none, true), (none, false)], ← List.nil_append [(some i, false), (some i, true)],
    ← List.append_nil ([] ++ [(none, true), (none, false)]), ← List.append_nil ([] ++ [(some i, false), (some i, true)])]
  use SemiThue.reduction (grid_style.basic i)
  simp [rw_length]

noncomputable def SemiThue_adjacent_w_len (i j : ℕ) (hd : Nat.dist i j = 1) :
  {h : SemiThue grid_style [(some i, false), (some j, true)] [(some j, true), (some i, true), (some j, false), (some i, false)] // rw_length h = 1} := by
  rw [← List.nil_append [(some i, false), (some j, true)], ← List.nil_append [(some j, true), (some i, true), (some j, false), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (some j, true)]), ← List.append_nil ([] ++ [(some j, true), (some i, true), (some j, false), (some i, false)])]
  use SemiThue.reduction (grid_style.close hd)
  simp [rw_length]

noncomputable def SemiThue_separated_w_len (i j : ℕ) (hd : Nat.dist i j ≥ 2) :
  {h : SemiThue grid_style [(some i, false), (some j, true)] [(some j, true), (some i, false)] // rw_length h = 1} := by
  rw [← List.nil_append [(some i, false), (some j, true)], ← List.nil_append [(some j, true), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (some j, true)]), ← List.append_nil ([] ++ [(some j, true), (some i, false)])]
  use SemiThue.reduction (grid_style.apart hd)
  simp [rw_length]

noncomputable def SemiThue_cons_w_len (h : SemiThue grid_style a b) :
    {h1 : SemiThue grid_style (c :: a) (c :: b) // rw_length h1 = rw_length h} := by
  induction h with
  | refl a =>
    use SemiThue.refl (c :: a)
    simp [rw_length]
  | reduction h =>
    rename_i e f g i
    rw [← List.cons_append, ← List.cons_append]
    use SemiThue.reduction h
    rfl
  | trans e f g h1 h2 ih1 ih2 =>
    use SemiThue.trans (c :: e) (c :: f) (c :: g) ih1.1 ih2.1
    simp [rw_length, ih1.2, ih2.2]

set_option pp.funBinderTypes true --can add in to make it just for the next one

noncomputable def SemiThue_append_left_w_len (c) (h : SemiThue grid_style a b) :
  {h1 : SemiThue grid_style (c ++ a) (c ++ b) // rw_length h1 = rw_length h} := by
  induction c
  · simp
    use h
  rename_i head tail ih
  have H := @SemiThue_cons_w_len (tail ++ a) (tail ++ b) head ih.1
  use H.1
  rw [H.2, ih.2]

noncomputable def SemiThue_caboose_w_len (h : SemiThue grid_style a b) :
  {h1 : SemiThue grid_style (a ++ [c]) (b ++ [c]) // rw_length h1 = rw_length h }:= by
  induction h with
  | refl a =>
    use SemiThue.refl _
    simp [rw_length]
  | reduction h =>
    rename_i e f g i
    rw [List.append_assoc, List.append_assoc _ i]
    use SemiThue.reduction h
    rfl
  | trans e f g h1 h2 ih1 ih2 =>
    use SemiThue.trans _ _ _ ih1.1 ih2.1
    simp [rw_length, ih1.2, ih2.2]

noncomputable def SemiThue_append_right_w_len (c) (h : SemiThue grid_style a b) :
  {h1 : SemiThue grid_style (a ++ c) (b ++ c) // rw_length h1 = rw_length h} := by
  induction c using List.reverseRecOn
  · rw [List.append_nil, List.append_nil]
    use h
  rename_i front caboose ih
  rw [← List.append_assoc, ← List.append_assoc]
  have H := (@SemiThue_caboose_w_len (a ++ front) (b ++ front) caboose ih.1)
  use H.1
  rw [H.2, ih.2]

noncomputable def pg_to_rev (h : PartialGrid a b c d e) :
  (h1 : SemiThue grid_style (a ++ b) (c ++ d ++ e)) × PLift (h.length = rw_length h1) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty =>
      use SemiThue_empty_w_len.1
      constructor
      simp [PartialGrid.length, SemiThue_empty_w_len.2]
    | top_bottom i =>
      use (SemiThue_top_bottom_w_len i).1
      constructor
      simp [PartialGrid.length, (SemiThue_top_bottom_w_len i).2]
    | sides i =>
      use (SemiThue_sides_w_len i).1
      constructor
      simp [PartialGrid.length, (SemiThue_sides_w_len i).2]
    | top_left i =>
      use (SemiThue_top_left_w_len i).1
      constructor
      simp [PartialGrid.length, (SemiThue_top_left_w_len i).2]
    | adjacent i k h =>
      use (SemiThue_adjacent_w_len i k h).1
      constructor
      simp [PartialGrid.length, (SemiThue_adjacent_w_len i k h).2]
    | separated i j h =>
      use (SemiThue_separated_w_len i j (or_dist_iff.mpr h)).1
      constructor
      simp [PartialGrid.length, (SemiThue_separated_w_len i j (or_dist_iff.mpr h)).2]
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, List.nil_append]
    use SemiThue.refl _
    constructor
    simp [PartialGrid.length, rw_length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i l m n o p q r s
    rw [PartialGrid.length]
    rw [List.append_nil] at g1_ih
    rcases g1_ih with ⟨h3, h3_len⟩
    have h4 := SemiThue_append_right_w_len p h3
    rw [List.append_assoc] at h4
    rcases g2_ih with ⟨h5, h5_len⟩
    have h6 := SemiThue_append_left_w_len n h5
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at h6
    use SemiThue.trans _ _ _ h4.1 h6.1
    constructor
    simp [rw_length, h6.2, h4.2]
    apply foo h3_len.1 h5_len.1
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i l m n o p q r s t
    rw [PartialGrid.length]
    rcases g1_ih with ⟨h3, h3_len⟩
    have h4 := SemiThue_append_right_w_len q h3
    rw [List.append_assoc] at h4
    rcases g2_ih with ⟨h5, h5_len⟩
    have h6 := SemiThue_append_left_w_len (n ++ o) h5
    rw [← List.append_assoc, ← List.append_assoc] at h6
    rw [List.append_assoc o r s, ← List.append_assoc n o (r ++ s)]
    use SemiThue.trans _ _ _ h4.1 h6.1
    constructor
    simp [rw_length, h6.2, h4.2]
    apply foo h3_len.1 h5_len.1
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i l m n o p q r s
    rw [PartialGrid.length]
    rw [List.append_nil] at g1_ih
    rcases g1_ih with ⟨h3, h3_len⟩
    have h4 := SemiThue_append_left_w_len p h3
    rw [← List.append_assoc] at h4
    rcases g2_ih with ⟨h5, h5_len⟩
    have h6 := SemiThue_append_right_w_len o h5
    rw [List.append_assoc, List.append_assoc, List.append_assoc, ← List.append_assoc q] at h6
    use SemiThue.trans _ _ _ h4.1 h6.1
    constructor
    simp [rw_length, h6.2, h4.2]
    apply foo h3_len.1 h5_len.1
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i l m n o p q r s
    rw [PartialGrid.length]
    rcases g1_ih with ⟨h3, h3_len⟩
    have h4 := SemiThue_append_left_w_len p h3
    rcases g2_ih with ⟨h5, h5_len⟩
    have h6 := SemiThue_append_right_w_len (n ++ o) h5
    rw [List.append_assoc, List.append_assoc, List.append_assoc, ← List.append_assoc m n o] at h6
    rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
    use SemiThue.trans _ _ _ h4.1 h6.1
    constructor
    simp [rw_length, h6.2, h4.2]
    apply foo h3_len.1 h5_len.1


noncomputable def pgf_to_rev (h : pgf a b mid) :
  (h1 : SemiThue grid_style (a ++ b) mid) × PLift (h.length = rw_length h1) := by
  induction h with
  | skeleton ha ha1 hb hb =>
    use SemiThue.refl _
    constructor
    simp [rw_length, pgf.length]
  | empty h hc ih =>
    rename_i e f g
    subst hc
    rw [pgf.length]
    use SemiThue.trans _ _ _ ih.1 (SemiThue.reduction (grid_style.empty))
    constructor
    simp [rw_length, ih.2.1, SemiThue_empty_w_len.2]
  | top_bottom i h hc ih =>
    rename_i e f g
    subst hc
    rw [pgf.length]
    use SemiThue.trans _ _ _ ih.1 (SemiThue.reduction (grid_style.up _))
    constructor
    simp [rw_length, ih.2.1, SemiThue_empty_w_len.2]
  | sides i h hc ih =>
    rename_i e f g
    subst hc
    rw [pgf.length]
    use SemiThue.trans _ _ _ ih.1 (SemiThue.reduction (grid_style.over _))
    constructor
    simp [rw_length, ih.2.1, SemiThue_empty_w_len.2]
  | top_left i h hc ih =>
    rename_i e f g
    subst hc
    rw [pgf.length]
    use SemiThue.trans _ _ _ ih.1 (SemiThue.reduction (grid_style.basic _))
    constructor
    simp [rw_length, ih.2.1, SemiThue_empty_w_len.2]
  | adjacent i j hd h hc ih =>
    rename_i e f g
    subst hc
    rw [pgf.length]
    use SemiThue.trans _ _ _ ih.1 (SemiThue.reduction (grid_style.close hd))
    constructor
    simp [rw_length, ih.2.1, SemiThue_empty_w_len.2]
  | separated i k hd h hc ih =>
    rename_i e f g
    subst hc
    rw [pgf.length]
    use SemiThue.trans _ _ _ ih.1 (SemiThue.reduction (grid_style.apart hd))
    constructor
    simp [rw_length, ih.2.1, SemiThue_empty_w_len.2]

noncomputable def pgf_of_st_w_len (h : SemiThue_one_step grid_style ab c) (hab : ab = a ++ b)
  (ha : is_false a) (hal : a.length > 0) (hb : is_true b) (hbl : b.length > 0) :
  (h2 : pgf a b c) × PLift (rw_length_one_step h = pgf.length h2):= by
  induction h with
  | refl d =>
    subst hab
    use pgf.skeleton a b hal ha hbl hb
    constructor
    simp [rw_length_one_step, pgf.length, PartialGrid.length]
  | one_step h1 h2 ih =>
    rename_i d e f g l
    have H1 := reg_of_one_step_w_len h1
    specialize ih hab
    rcases h2
    · rename_i n
      rw [rw_length_one_step]
      use pgf.top_left _ ih.1 rfl
      constructor
      rw [pgf.length, ← ih.2.1]
    · rename_i n
      rw [rw_length_one_step]
      use pgf.sides _ ih.1 rfl
      constructor
      rw [pgf.length, ← ih.2.1]
      rfl
    · rename_i n
      rw [rw_length_one_step]
      use pgf.top_bottom _ ih.1 rfl
      constructor
      rw [pgf.length, ← ih.2.1]
      rfl
    · rw [rw_length_one_step]
      use pgf.empty ih.1 rfl
      constructor
      rw [pgf.length, ← ih.2.1]
      rfl
    · rename_i n
      rw [rw_length_one_step]
      use pgf.separated _ _ n ih.1 rfl
      constructor
      rw [pgf.length, ← ih.2.1]
    rename_i n
    rw [rw_length_one_step]
    use pgf.adjacent _ _ n ih.1 rfl
    constructor
    rw [pgf.length, ← ih.2.1]

noncomputable def pg_of_st_w_len (h : SemiThue_one_step grid_style ab mid) (hab : ab = a ++ b)
  (ha : is_false a) (hal : a.length > 0) (hb : is_true b) (hbl : b.length > 0) :
  Σ c d e, (h2 : PartialGrid a b c d e) ×
  PLift (mid = c ++ d ++ e ∧ rw_length_one_step h = PartialGrid.length h2):= by
  induction h with
  | refl f =>
    use [], a ++ b, []
    use PartialGrid.empty a b hal ha hbl hb
    constructor
    simp [hab, rw_length_one_step, PartialGrid.length]
  | one_step h1 h2 ih =>
    rename_i l m n o p
    specialize ih hab
    have H1 := reg_of_one_step_w_len h1
    sorry
    -- rcases h2
    -- · rename_i q
    --   rw [rw_length_one_step]
    --   use pgf.top_left _ ih.1 rfl
    --   constructor
    --   rw [PartialGrid.length, ← ih.2.1]


-- noncomputable def get_frontier_style_helper (h : PartialGrid a b c d e) :
--   Σ f, Σ (h1 : pgf a b f),
--   PLift (f = c ++ d ++ e ∧ pgf_get_bottom h1 = c ∧ pgf_get_middle h1 = d ∧ pgf_get_right h1 = e ∧
--   h.length = h1.length) := by
--   induction h with
--   | single_gridt h => sorry
--   | empty a b ha ha1 hb hb1 =>
--     use a ++ b, pgf.skeleton a b ha ha1 hb hb1
--     constructor
--     simp_all [pgf_get_bottom, pgf_get_middle, pgf_get_right, pgf.length, PartialGrid.length]
--     sorry
--   | horizontal_append_one g1 g2 g1_ih g2_ih => sorry
--   | horizontal_append h g1 g2 g1_ih g2_ih => sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry

noncomputable def get_frontier_style (h : PartialGrid a b c d e) : Σ (h1 : pgf a b (c ++ d ++ e)),
  PLift ( h.length = h1.length) := by
  have H := pg_to_rev h
  have H2 := one_step_of_reg_w_len H.1
  have H3 := @pgf_of_st_w_len (a ++ b) _ _ _  H2.1 rfl h.left_frontier_is_false
    (PartialGrid.left_length_pos h) h.top_frontier_is_true (PartialGrid.top_length_pos h)
  use H3.1
  constructor
  rw [← H3.2.1, ← H2.2.1, ← H.2.1]

noncomputable def get_frontier_style_converse (h1 : pgf a b mid) :
  Σ c d e, (h : PartialGrid a b c d e) ×
  PLift (mid = c ++ d ++ e ∧ h.length = h1.length) := by
  have H := pgf_to_rev h1
  have H2 := one_step_of_reg_w_len H.1
  have H3 := @pgf_of_st_w_len (a ++ b) _ _ _  H2.1 rfl h.left_frontier_is_false
    (PartialGrid.left_length_pos h) h.top_frontier_is_true (PartialGrid.top_length_pos h)
  use H3.1
  constructor
  rw [← H3.2.1, ← H2.2.1, ← H.2.1]

  -- have H := get_frontier_style_helper h
  -- rcases H with ⟨f, h1, fe, _, _, hl⟩
  -- use f, h1
  -- constructor
  -- aesop

-- theorem same_type_same_length_pg {a b c d e a1 b1 c1 d1 e1}
--   (g1 : PartialGrid a b c d e) (g2 : PartialGrid a1 b1 c1 d1 e1) :
--   a = a1 → b = b1 → c = c1 → d = d1 → e = e1 → g1.length = g2.length := by
--   have H1 := get_frontier_style g1
--   have H2 := get_frontier_style g2
--   rcases H1 with ⟨h1, ⟨h1_len⟩⟩
--   rcases H2 with ⟨h2, ⟨h2_len⟩⟩
--   rw [h1_len, h2_len]
--   intro ha hb hc hd he
--   apply pgf_length_well_defined h1 h2 ha hb
--   aesop

-- noncomputable def reg_of_f (h : pgf a b c) : Σ c1 d1 e1, {h1 : PartialGrid a b c1 d1 e1 //
--   c = c1 ++ d1 ++ e1 ∧ h1.length = pgf.length h} := by
--   induction h with
--   | skeleton a b ha ha1 hb hb1 =>
--     rename_i e f
--     use [], a ++ b, []
--     use PartialGrid.empty a b ha ha1 hb hb1
--     constructor
--     · simp
--     simp [pgf.length, PartialGrid.length]
--   | empty h ih => sorry
--   | top_bottom i h ih =>
--     rename_i e f g j
--     rcases ih with ⟨c2, d2, e2, h2⟩
--     sorry
--   | sides i h ih => sorry
--   | top_left i h ih => sorry
--   | adjacent i j h h ih => sorry
--   | separated i k h h ih => sorry
