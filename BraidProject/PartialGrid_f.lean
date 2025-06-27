import BraidProject.Grids_C
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.PartialGrid_bounded

inductive pgf : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → Type
  | skeleton (a b) (ha : a.length > 0) (ha1 : is_false a) (hb : b.length > 0) (hb : is_true b ):
      pgf a b (a ++ b)
  | empty (h : pgf a b (c1 ++ [(none, false), (none, true)] ++ c2)) :
      pgf a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | top_bottom (i : ℕ) (h : pgf a b (c1 ++ [(none, false), (some i, true)] ++ c2)) :
      pgf a b (c1 ++ [(some i, true), (none, false)] ++ c2)
  | sides (i : ℕ) (h : pgf a b (c1 ++ [(some i, false), (none, true)] ++ c2)) :
      pgf a b (c1 ++ [(none, true), (some i, false)] ++ c2)
  | top_left (i : ℕ) (h : pgf a b c) (hc : c = (c1 ++ [(some i, false), (some i, true)] ++ c2)) :
      pgf a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | adjacent (i j : ℕ) (hd : Nat.dist i j = 1) (h : pgf a b (c1 ++ [(some i, false), (some j, true)] ++ c2)) :
      pgf a b (c1 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c2)
  | separated (i k : ℕ) (hd : Nat.dist i j ≥ 2) (h : pgf a b (c1 ++ [(some i, false), (some k, true)] ++ c2)) :
      pgf a b (c1 ++ [(some k, true), (some i, false)] ++ c2)

def pgf.length (h : pgf a b c) : Nat :=
  match h with
  | pgf.skeleton _ _ _ _ _ _ => 0
  | pgf.empty h => pgf.length h
  | pgf.top_bottom i h => pgf.length h
  | pgf.sides _ h => pgf.length h
  | pgf.top_left _ h _ => pgf.length h + 1
  | pgf.adjacent _ _ _ h => pgf.length h + 1
  | pgf.separated _ _ _ h => pgf.length h + 1

noncomputable def pgf_left_false (h : pgf a b c) : is_false a := by
  induction h; all_goals assumption

noncomputable def pgf_top_true (h : pgf a b c) : is_true b := by
  induction h; all_goals assumption

def get_maximal_true_prefix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
  match c with
  | [] => []
  | (_, false) :: _ => []
  | (d, true) :: e => [(d, true)] ++ get_maximal_true_prefix e

def get_maximal_false_suffix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) := by
  cases c using List.reverseRecOn with
  | nil => exact []
  | append_singleton l a _ =>
    match a with
    | (_, true) => exact []
    | (d, false) => exact get_maximal_false_suffix l ++ [(d, false)]
  termination_by c.length

def remove_maximal_true_prefix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
  match c with
  | [] => []
  | (d, false) :: e => (d, false) :: e
  | (_, true) :: e => remove_maximal_true_prefix e

def remove_maximal_false_suffix (c : List (Option ℕ × Bool)) : List (Option ℕ × Bool) := by
  cases c using List.reverseRecOn with
  | nil => exact []
  | append_singleton l a _ =>
    match a with
    | (d, true) => exact l ++ [(d, true)]
    | (d, false) => exact remove_maximal_false_suffix l
  termination_by c.length

theorem remove_maximal_false_suffix_nil : remove_maximal_false_suffix [] = [] := by
  unfold remove_maximal_false_suffix
  simp

theorem remove_maximal_false_suffix_append_false :
  remove_maximal_false_suffix (a ++ [(b, false)]) = remove_maximal_false_suffix a := by
  unfold remove_maximal_false_suffix
  simp
  exact remove_maximal_false_suffix.eq_def a

theorem get_maximal_false_suffix_append_false : get_maximal_false_suffix (a ++ [(b, false)]) =
  get_maximal_false_suffix a ++ [(b, false)] := by
  unfold get_maximal_false_suffix
  simp
  exact get_maximal_false_suffix.eq_def a


def pgf_get_bottom (h : pgf a b c) := get_maximal_true_prefix c

def pgf_get_right (h : pgf a b c) := get_maximal_false_suffix c

def pgf_get_middle (h : pgf a b c) :=
  remove_maximal_true_prefix (remove_maximal_false_suffix c)

theorem get_prefix_append_remove_prefix : get_maximal_true_prefix a ++ remove_maximal_true_prefix a = a := by
  induction a with
  | nil => simp [get_maximal_true_prefix, remove_maximal_true_prefix]
  | cons d e ih =>
    match d with
    | (d1, false) =>
      simp [get_maximal_true_prefix, remove_maximal_true_prefix, ih]
    | (d2, true) =>
      simp [get_maximal_true_prefix, remove_maximal_true_prefix, ih]

theorem remove_suffix_append_get_suffix : remove_maximal_false_suffix a ++ get_maximal_false_suffix a = a := by
  induction a using List.reverseRecOn with
  | nil => unfold remove_maximal_false_suffix get_maximal_false_suffix; simp
  | append_singleton l d ih =>
    match d with
    | (d1, true) =>
      unfold remove_maximal_false_suffix get_maximal_false_suffix; simp [ih]
    | (d2, false) =>
      rw [remove_maximal_false_suffix_append_false, get_maximal_false_suffix_append_false, ← List.append_assoc, ih]

theorem pgf_split_bottom_middle_right (h : pgf a b c) :
  pgf_get_bottom h ++ pgf_get_middle h ++ pgf_get_right h = c := by
  unfold pgf_get_bottom pgf_get_middle pgf_get_right
  sorry

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

theorem pgf_length_empty (h : pgf a b c) (hc : c = a ++ b) : h.length = 0 := by
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
  | adjacent i j h h ih =>
    rename_i c5 c6 _
    have : c5 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c6  =
      (c5 ++ [(some j, true)]) ++ [(some i, true), (some j, false)] ++ ((some i, false) :: c6) := by simp
    rw [this] at hc
    exact (true_false_not_in_spine hc (pgf_left_false h) (pgf_top_true h)).elim
  | separated i k h h ih =>
    exact (true_false_not_in_spine hc (pgf_left_false h) (pgf_top_true h)).elim

noncomputable def triple_no_overlap''
 (h : m ++ [(some i, true), (none, false)] ++ n = p ++ [(none, true), (none, false)] ++ q) :
 (Σ m1 m2, PLift (m1 = p ∧ m1 ++ [(none, true), (none, false)] ++ m2 = m ∧ m2 ++ [(some i, true), (none, false)] ++ n = q)) ⊕
 (List.Infix' [(none, true), (none, false)] n) := by sorry

noncomputable def pgf_length_top_bottom (h2 : pgf a b c)
    (hc : m ++ [(some i, true), (none, false)] ++ n = c) :
      Σ (h1 : pgf a b (m ++ [(none, false), (some i, true)] ++ n)), PLift (h1.length = h2.length) := by
  induction h2 generalizing m n with
  | skeleton a b ha ha' hb hb' =>
    exact (true_false_not_in_spine hc ha' hb').elim
  | empty h => sorry
  | top_bottom i' h ih =>
    rename_i l o p q
    simp [pgf.length]
    sorry
  | sides i h ih => sorry
  | top_left k h hc' ih =>
    rename_i l o c' p q
    simp [pgf.length]
    rcases triple_no_overlap'' hc with ⟨m1, m2, ⟨hm⟩⟩ | oop
    · have for_ih : m1 ++ [(some k, false), (some k, true)] ++ m2 ++ [(some i, true), (none, false)] ++ n =
        p ++ [(some k, false), (some k, true)] ++ q := by
        rw [hm.1, ← hm.2.2]
        simp
      rw [← hc'] at for_ih
      specialize ih for_ih
      rcases ih with ⟨h2, h2_len⟩
      rw [← h2_len.1]
      have H := @pgf.top_left _ _ _ m1 ((m2 ++ [(none, false), (some i, true)] ++ n)) k h2 (by simp)
      rw [← hm.2.1]
      have : m1 ++ [(none, true), (none, false)] ++ m2 ++ [(none, false), (some i, true)] ++ n =
        m1 ++ [(none, true), (none, false)] ++ (m2 ++ [(none, false), (some i, true)] ++ n) := by simp
      rw [this]
      use @pgf.top_left _ _ _ m1 ((m2 ++ [(none, false), (some i, true)] ++ n)) k h2 (by simp)
      constructor
      rw [pgf.length]
    sorry
  | adjacent i j hd h ih => sorry
  | separated i k hd h ih => sorry


theorem pgf_length_well_defined (h1 : pgf a1 b1 c1) (h2 : pgf a2 b2 c2)
    (ha12 : a1 = a2) (hb12 : b1 = b2) (hc12 : c1 = c2) : h1.length = h2.length := by
  induction h1 generalizing h2 a2 b2 c2 with
  | skeleton a b ha _ hb _ =>
    rw [ha12, hb12] at hc12
    rw [pgf_length_empty h2 hc12.symm, pgf.length]
  | empty h ih => sorry
  | top_bottom i h ih =>
    rename_i k l m n
    rw [pgf.length]
    have H := pgf_length_top_bottom h2 hc12
    rcases H with ⟨h3, ⟨h3_len⟩⟩
    rw [← h3_len]
    exact ih h3 ha12 hb12 rfl
  | sides i h ih => sorry
  | top_left i h ih => sorry
  | adjacent i j hd h ih =>
    rename_i k l m n
    rw [pgf.length]
    sorry
  | separated i k h h ih => sorry

noncomputable def pgf_extend_side (h : pgf a b c) (d : List (Option ℕ × Bool)) (hd : is_true d):
  pgf a (b ++ d) (c ++ d) := by
  induction h with
  | skeleton a b ha ha1 hb hb1 =>
    have H := pgf.skeleton a (b ++ d) ha ha1 (by simp [hb]) (is_true_of_true_true hb1 hd)
    rw [← List.append_assoc] at H
    use H
  | empty h ih =>
    rename_i l m n o
    rw [List.append_assoc _ o d] at ih
    have H := pgf.empty ih
    rw [← List.append_assoc] at H
    use H
  | top_bottom i h ih =>
    rename_i l m n o
    rw [List.append_assoc _ o d] at ih
    have H := pgf.top_bottom i ih
    rw [← List.append_assoc] at H
    use H
  | sides i h ih =>
    rename_i l m n o
    rw [List.append_assoc _ o d] at ih
    have H := pgf.sides i ih
    rw [← List.append_assoc] at H
    use H
  | top_left i h ih =>
    rename_i l m n o p q
    rw [ih, List.append_assoc _ p d] at q
    have H := pgf.top_left i q rfl
    rw [← List.append_assoc] at H
    use H
  | adjacent i j hd h ih =>
    rename_i l m n o
    rw [List.append_assoc _ o d] at ih
    have H := pgf.adjacent i j hd ih
    rw [← List.append_assoc] at H
    use H
  | separated i k hd h ih =>
    rename_i l m n o
    rw [List.append_assoc _ o d] at ih
    have H := pgf.separated i k hd ih
    rw [← List.append_assoc] at H
    use H

noncomputable def pgf_extend_bottom (h : pgf a b c) (d : List (Option ℕ × Bool)) (hd : is_false d):
  pgf (d ++ a) b (d ++ c) := by
  induction h with
  | skeleton a b ha ha1 hb hb1 =>
    have H := pgf.skeleton (d ++ a) b (by simp [ha]) (is_false_of_false_false hd ha1) hb hb1
    rw [List.append_assoc d a b] at H
    use H
  | empty h ih =>
    rename_i l m n o
    rw [← List.append_assoc d, ← List.append_assoc] at ih
    have H := pgf.empty ih
    rw [← List.append_assoc, ← List.append_assoc]
    use H
  | top_bottom i h ih =>
    rename_i l m n o
    rw [← List.append_assoc d, ← List.append_assoc] at ih
    have H := pgf.top_bottom i ih
    rw [← List.append_assoc, ← List.append_assoc]
    use H
  | sides i h ih =>
    rename_i l m n o
    rw [← List.append_assoc d, ← List.append_assoc] at ih
    have H := pgf.sides i ih
    rw [← List.append_assoc, ← List.append_assoc]
    use H
  | top_left i h ih =>
    rename_i l m n o p q
    rw [ih, ← List.append_assoc d, ← List.append_assoc] at q
    have H := pgf.top_left i q rfl
    rw [← List.append_assoc, ← List.append_assoc]
    use H
  | adjacent i j hd h ih =>
    rename_i l m n o
    rw [← List.append_assoc d, ← List.append_assoc] at ih
    have H := pgf.adjacent i j hd ih
    rw [← List.append_assoc, ← List.append_assoc]
    use H
  | separated i k hd h ih =>
    rename_i l m n o
    rw [← List.append_assoc d, ← List.append_assoc] at ih
    have H := pgf.separated i k hd ih
    rw [← List.append_assoc, ← List.append_assoc]
    use H

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
  | SemiThue.trans a b c h1 h2 => rw_length h1 + rw_length h2

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
  exact Mathlib.Tactic.Ring.add_congr (ih1.2.1) (ih2.2.1) rfl

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
    · use pgf.sides _ ih
    · use pgf.top_bottom _ ih
    · use pgf.empty ih
    · use pgf.separated _ _ (by assumption) ih
    use pgf.adjacent _ _ (by assumption) ih

noncomputable def pgf_of_st_w_len (h : SemiThue grid_style ab c) (hab : ab = a ++ b)
  (ha : is_false a) (hal : a.length > 0) (hb : is_true b) (hbl : b.length > 0) :
  (h2 : pgf a b c) × PLift (rw_length h = pgf.length h2):= by
  apply one_step_of_reg_w_len at h
  induction h.1 with
  | refl d =>
    sorry --use pgf.skeleton a b hal ha hbl hb
  | one_step h1 h2 ih =>
    rename_i d e f g l
    have H1 := reg_of_one_step_w_len h1
    specialize ih H1.1 hab ⟨h1, ⟨H1.2.1⟩⟩
    rw [H1.2.1] at ih
    rcases h2
    · rw [h.2.1]
      use pgf.top_left _ ih.1 rfl
      constructor
      rw [pgf.length, ← ih.2.1, H1.2.1]
      sorry

    -- · use pgf.sides _ ih
    -- · use pgf.top_bottom _ ih
    -- · use pgf.empty ih
    -- · use pgf.separated _ _ (by assumption) ih
    -- use pgf.adjacent _ _ (by assumption) ih

noncomputable def get_frontier_style_helper (h : PartialGrid a b c d e) :
  Σ f, Σ (h1 : pgf a b f),
  PLift (f = c ++ d ++ e ∧ pgf_get_bottom h1 = c ∧ pgf_get_middle h1 = d ∧ pgf_get_right h1 = e ∧
  h.length = h1.length) := by
  induction h with
  | single_gridt h => sorry
  | empty a b ha ha1 hb hb1 =>
    use a ++ b, pgf.skeleton a b ha ha1 hb hb1
    constructor
    simp_all [pgf_get_bottom, pgf_get_middle, pgf_get_right, pgf.length, PartialGrid.length]
    sorry
  | horizontal_append_one g1 g2 g1_ih g2_ih => sorry
  | horizontal_append h g1 g2 g1_ih g2_ih => sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

noncomputable def get_frontier_style (h : PartialGrid a b c d e) : Σ f, Σ (h1 : pgf a b f),
  PLift (f = c ++ d ++ e ∧ h.length = h1.length) := by
  have H := get_frontier_style_helper h
  rcases H with ⟨f, h1, fe, _, _, hl⟩
  use f, h1
  constructor
  aesop

theorem same_type_same_length_pg {a b c d e a1 b1 c1 d1 e1}
  (g1 : PartialGrid a b c d e) (g2 : PartialGrid a1 b1 c1 d1 e1) :
  a = a1 → b = b1 → c = c1 → d = d1 → e = e1 → g1.length = g2.length := by
  have H1 := get_frontier_style g1
  have H2 := get_frontier_style g2
  rcases H1 with ⟨f, h1, h1_eq, h1_len⟩
  rcases H2 with ⟨f1, h2, h2_eq, h2_len⟩
  rw [h1_len, h2_len]
  intro ha hb hc hd he
  apply pgf_length_well_defined h1 h2 ha hb
  aesop

noncomputable def reg_of_f (h : pgf a b c) : Σ c1 d1 e1, {h1 : PartialGrid a b c1 d1 e1 //
  c = c1 ++ d1 ++ e1 ∧ h1.length = pgf.length h} := by
  induction h with
  | skeleton a b ha ha1 hb hb1 =>
    rename_i e f
    use [], a ++ b, []
    use PartialGrid.empty a b ha ha1 hb hb1
    constructor
    · simp
    simp [pgf.length, PartialGrid.length]
  | empty h ih => sorry
  | top_bottom i h ih =>
    rename_i e f g j
    rcases ih with ⟨c2, d2, e2, h2⟩
    sorry
  | sides i h ih => sorry
  | top_left i h ih => sorry
  | adjacent i j h h ih => sorry
  | separated i k h h ih => sorry
