import BraidProject.Grids_C
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.SimplerPG.SimplePG_block
import BraidProject.SimplerPG.SimplePG_bounded

inductive pgf : List (ℕ × Bool) → List (ℕ × Bool) →
  List (ℕ × Bool) → Type
  | skeleton (a b) (ha1 : is_false a) (hb : is_true b ):
      pgf a b (a ++ b)
  | top_left (i : ℕ) (h : pgf a b c) (hc : c = (c1 ++ [(i, false), (i, true)] ++ c2)) :
      pgf a b (c1 ++ c2)
  | adjacent (i j : ℕ) (hd : Nat.dist i j = 1) (h : pgf a b c)
      (hc : c = (c1 ++ [(i, false), (j, true)] ++ c2)) :
      pgf a b (c1 ++ [(j, true), (i, true), (j, false), (i, false)] ++ c2)
  | separated (i k : ℕ) (hd : Nat.dist i k ≥ 2) (h : pgf a b c)
     (hc : c = c1 ++ [(i, false), (k, true)] ++ c2) :
      pgf a b (c1 ++ [(k, true), (i, false)] ++ c2)

-- inductive grid_style_real : List (ℕ × Bool) → List (ℕ × Bool) → Type
-- | basic (n : ℕ) : grid_style_real [(n, false), (n, true)] []
-- | apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style_real [(i, false), (j, true)] [(j, true), (i, false)]
-- | close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style_real [(i, false), (j, true)]
--     [(j, true), (i, true), (j, false), (i, false)]

def pgf.length (h : pgf a b c) : Nat :=
  match h with
  | pgf.skeleton _ _ _ _ => 0
  | pgf.top_left _ h _ => pgf.length h + 1
  | pgf.adjacent _ _ _ h _ => pgf.length h + 1
  | pgf.separated _ _ _ h _ => pgf.length h + 1

noncomputable def pgf_left_false (h : pgf a b c) : is_false a := by
  induction h; all_goals assumption

noncomputable def pgf_top_true (h : pgf a b c) : is_true b := by
  induction h; all_goals assumption

inductive reversing : List (α × Bool) → List (α × Bool) → Type
  | basic (a : ℕ) : reversing [(a, false), (a, true)] []
  | close {i j : ℕ} (h : i.dist j = 1) : reversing [(i, false), (j, true)]
      [(j, true), (i, true), (j, false), (i, false)]
  | apart {i j : ℕ} (h : i.dist j >= 2): reversing [(i, false), (j, true)]
      [(j, true), (i, false)]

noncomputable def add_cell_w_len_pgf (h : pgf a b c)
    (hg : reversing i j) (fe : c = k ++ i ++ l) :
    Σ c', (h1 : pgf a b c') × PLift (c' = k ++ j ++ l) ×
    PLift (h.length < h1.length) := by
  cases hg with
  | basic n =>
    use k ++ l
    use pgf.top_left _ h fe
    constructor
    constructor
    simp [pgf.length]
    constructor
    simp [pgf.length]
  | apart hij =>
    rename_i i j
    use k ++ [(j, true), (i, false)] ++ l
    use pgf.separated _ _ hij h fe
    constructor
    constructor
    simp [pgf.length]
    constructor
    simp [pgf.length]
  | close hij =>
    rename_i i j
    use k ++ [(j, true), (i, true), (j, false), (i, false)] ++ l
    use pgf.adjacent _ _ hij h fe
    constructor
    constructor
    simp [pgf.length]
    constructor
    simp [pgf.length]


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

def rw_length (h : SemiThue reversing a b) : ℕ :=
  match h with
  | SemiThue.refl a => 0
  | SemiThue.reduction h =>
    match h with
    | reversing.basic _ => 1
    | reversing.apart _ => 1
    | reversing.close _ => 1
  | SemiThue.trans a _ c h1 h2 => rw_length h1 + rw_length h2

def rw_length_rev (h : SemiThue reversing a b) : ℕ :=
  match h with
  | SemiThue.refl a => 0
  | SemiThue.reduction h => 1
  | SemiThue.trans a _ c h1 h2 => rw_length_rev h1 + rw_length_rev h2

def rw_length_one_step (h : SemiThue_one_step reversing a b) : ℕ :=
  match h with
  | SemiThue_one_step.refl a => 0
  | SemiThue_one_step.one_step h1 h => rw_length_one_step h1 + 1

def rw_length_one_step_rev (h : SemiThue_one_step reversing a b) : ℕ :=
  match h with
  | SemiThue_one_step.refl a => 0
  | SemiThue_one_step.one_step h1 h => rw_length_one_step_rev h1 + 1

noncomputable def one_step_trans
  (h1 : SemiThue_one_step reversing a b) (h2 : SemiThue_one_step reversing b c) :
    (h3 : SemiThue_one_step reversing a c) ×
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
    use h4.one_step (reversing.basic n)
    constructor
    rw [rw_length_one_step, rw_length_one_step, len4.1, add_assoc]
  | apart h' =>
    use h4.one_step (reversing.apart h')
    constructor
    rw [rw_length_one_step, rw_length_one_step, len4.1, add_assoc]
  | close h' =>
    use h4.one_step (reversing.close h')
    constructor
    rw [rw_length_one_step, rw_length_one_step, len4.1, add_assoc]

theorem foo {a b c d : ℕ} (h : a = b) (h1 : c = d) : a + c = b + d :=
  Mathlib.Tactic.Ring.add_congr h h1 rfl

noncomputable def one_step_of_reg_w_len {a b : List (ℕ × Bool)} :
    ((h1 : SemiThue reversing a b )→ (Σ h2 : SemiThue_one_step reversing a b,
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
    (h1 : SemiThue_one_step reversing a b) → (Σ h2 : SemiThue reversing a b,
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

noncomputable def pgf_of_st (h : SemiThue reversing ab c) (hab : ab = a ++ b)
  (ha : is_false a) (hb : is_true b) :
  pgf a b c := by
  apply one_step_equiv_reg.1 at h
  induction h with
  | refl d =>
    rw [hab]
    exact pgf.skeleton a b ha hb
  | one_step h1 h2 ih =>
    rename_i d e f g l
    specialize ih hab
    rcases h2
    · rename_i ij
      rw [List.append_nil]
      use pgf.top_left _ ih rfl
    · use pgf.adjacent _ _ (by assumption) ih rfl
    use pgf.separated _ _ (by assumption) ih rfl

noncomputable def SemiThue_top_left_w_len (i : ℕ) :
  {h : SemiThue reversing [(i, false), (i, true)] [] // rw_length h = 1} := by
  rw [← List.nil_append [(i, false), (i, true)], ← List.append_nil ([] ++ [(i, false), (i, true)])]
  use SemiThue.reduction (reversing.basic _)
  simp [rw_length]

noncomputable def SemiThue_adjacent_w_len (i j : ℕ) (hd : Nat.dist i j = 1) :
  {h : SemiThue reversing [(i, false), (j, true)] [(j, true), (i, true), (j, false), (i, false)] // rw_length h = 1} := by
  rw [← List.nil_append [(i, false), (j, true)], ← List.nil_append [(j, true), (i, true), (j, false), (i, false)],
    ← List.append_nil ([] ++ [(i, false), (j, true)]), ← List.append_nil ([] ++ [(j, true), (i, true), (j, false), (i, false)])]
  use SemiThue.reduction (reversing.close hd)
  simp [rw_length]

noncomputable def SemiThue_separated_w_len (i j : ℕ) (hd : Nat.dist i j ≥ 2) :
  {h : SemiThue reversing [( i, false), ( j, true)] [( j, true), ( i, false)] // rw_length h = 1} := by
  rw [← List.nil_append [( i, false), ( j, true)], ← List.nil_append [( j, true), ( i, false)],
    ← List.append_nil ([] ++ [( i, false), ( j, true)]), ← List.append_nil ([] ++ [( j, true), ( i, false)])]
  use SemiThue.reduction (reversing.apart hd)
  simp [rw_length]

noncomputable def SemiThue_cons_w_len (h : SemiThue reversing a b) :
    {h1 : SemiThue reversing (c :: a) (c :: b) // rw_length h1 = rw_length h} := by
  induction h with
  | refl a =>
    use SemiThue.refl (c :: a)
    simp [rw_length]
  | reduction h =>
    rename_i e f g i
    rw [← List.cons_append, ← List.cons_append]
    use SemiThue.reduction h
    simp only [rw_length, List.cons_append]
    aesop
  | trans e f g h1 h2 ih1 ih2 =>
    use SemiThue.trans (c :: e) (c :: f) (c :: g) ih1.1 ih2.1
    simp [rw_length, ih1.2, ih2.2]

set_option pp.funBinderTypes true --can add in to make it just for the next one

noncomputable def SemiThue_append_left_w_len (c) (h : SemiThue reversing a b) :
  {h1 : SemiThue reversing (c ++ a) (c ++ b) // rw_length h1 = rw_length h} := by
  induction c
  · simp
    use h
  rename_i head tail ih
  have H := @SemiThue_cons_w_len _ (tail ++ a) (tail ++ b) head ih.1
  use H.1
  rw [H.2, ih.2]

noncomputable def SemiThue_caboose_w_len (h : SemiThue reversing a b) :
  {h1 : SemiThue reversing (a ++ [c]) (b ++ [c]) // rw_length h1 = rw_length h }:= by
  induction h with
  | refl a =>
    use SemiThue.refl _
    simp [rw_length]
  | reduction h =>
    rename_i e f g i
    rw [List.append_assoc, List.append_assoc _ i]
    use SemiThue.reduction h
    simp only [rw_length, List.append_assoc]
    aesop
  | trans e f g h1 h2 ih1 ih2 =>
    use SemiThue.trans _ _ _ ih1.1 ih2.1
    simp [rw_length, ih1.2, ih2.2]

noncomputable def SemiThue_append_right_w_len (c) (h : SemiThue reversing a b) :
  {h1 : SemiThue reversing (a ++ c) (b ++ c) // rw_length h1 = rw_length h} := by
  induction c using List.reverseRecOn
  · rw [List.append_nil, List.append_nil]
    use h
  rename_i front caboose ih
  rw [← List.append_assoc, ← List.append_assoc]
  have H := (@SemiThue_caboose_w_len _ (a ++ front) (b ++ front) caboose ih.1)
  use H.1
  rw [H.2, ih.2]

noncomputable def pg_to_rev (h : PartialGrid a b c d e) :
  (h1 : SemiThue reversing (a ++ b) (c ++ d ++ e)) × PLift (h.length = rw_length h1) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty =>
      use SemiThue.refl _
      constructor
      simp [PartialGrid.length, rw_length]
    | top_bottom i =>
      use SemiThue.refl _
      constructor
      simp [PartialGrid.length, rw_length]
    | sides i =>
      use SemiThue.refl _
      constructor
      simp [PartialGrid.length, rw_length]
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

def middle_nil : {h : SemiThue reversing (a ++ [] ++ b) (a ++ b) // rw_length h = 0} := by
  rw [List.append_nil]
  use SemiThue.refl _
  simp [rw_length]

noncomputable def pgf_to_rev (h : pgf a b mid) :
  (h1 : SemiThue reversing (a ++ b) mid) × PLift (h.length = rw_length h1) := by
  induction h with
  | skeleton ha hb =>
    use SemiThue.refl _
    constructor
    simp [rw_length, pgf.length]
  | top_left i h hc ih =>
    rename_i e f g
    subst hc
    rw [pgf.length]
    use (SemiThue.trans _ _ _ ih.1 (SemiThue.reduction (reversing.basic _))).trans _ _ _ (middle_nil).1
    constructor
    simp [rw_length, ih.2.1, middle_nil.2]
  | adjacent i j hd h hc ih =>
    rename_i e f g
    subst hc
    rw [pgf.length]
    use SemiThue.trans _ _ _ ih.1 (SemiThue.reduction (reversing.close hd))
    constructor
    simp [rw_length, ih.2.1]
  | separated i k hd h hc ih =>
    rename_i e f g
    subst hc
    rw [pgf.length]
    use SemiThue.trans _ _ _ ih.1 (SemiThue.reduction (reversing.apart hd))
    constructor
    simp [rw_length, ih.2.1]

noncomputable def pgf_of_st_w_len (h : SemiThue_one_step reversing ab c) (hab : ab = a ++ b)
  (ha : is_false a)  (hb : is_true b) :
  (h2 : pgf a b c) × PLift (rw_length_one_step h = pgf.length h2):= by
  induction h with
  | refl d =>
    subst hab
    use pgf.skeleton a b ha hb
    constructor
    simp [rw_length_one_step, pgf.length, PartialGrid.length]
  | one_step h1 h2 ih =>
    rename_i d e f g l
    have H1 := reg_of_one_step_w_len h1
    specialize ih hab
    rcases h2
    · rename_i n
      rw [rw_length_one_step]
      use pgf.top_left n ih.1 (by simp)
      constructor
      rw [pgf.length, ← ih.2.1]
    · rename_i n
      rw [rw_length_one_step]
      use pgf.adjacent _ _ n ih.1 rfl
      constructor
      rw [pgf.length, ← ih.2.1]
    · rename_i n
      rw [rw_length_one_step]
      use pgf.separated _ _ n ih.1 rfl
      constructor
      rw [pgf.length, ← ih.2.1]

-- noncomputable def pgf_of_st_w_rev_len (h : SemiThue_one_step reversing ab c) (hab : ab = a ++ b)
--   (ha : is_false a) (hal : a.length > 0) (hb : is_true b) (hbl : b.length > 0) :
--   (h2 : pgf a b c) × PLift (rw_length_one_step h = pgf.length h2):= by
--   induction h with
--   | refl d =>
--     subst hab
--     use pgf.skeleton a b hal ha hbl hb
--     constructor
--     simp [rw_length_one_step, pgf.length, PartialGrid.length]
--   | one_step h1 h2 ih =>
--     rename_i d e f g l
--     have H1 := reg_of_one_step_w_len h1
--     specialize ih hab
--     rcases h2
--     · rename_i n
--       rw [rw_length_one_step]
--       use pgf.top_left _ ih.1 rfl
--       constructor
--       rw [pgf.length, ← ih.2.1]
--     · rename_i n
--       rw [rw_length_one_step]
--       use pgf.sides _ ih.1 rfl
--       constructor
--       rw [pgf.length, ← ih.2.1]
--       rfl
--     · rename_i n
--       rw [rw_length_one_step]
--       use pgf.top_bottom _ ih.1 rfl
--       constructor
--       rw [pgf.length, ← ih.2.1]
--       rfl
--     · rw [rw_length_one_step]
--       use pgf.empty ih.1 rfl
--       constructor
--       rw [pgf.length, ← ih.2.1]
--       rfl
--     · rename_i n
--       rw [rw_length_one_step]
--       use pgf.separated _ _ n ih.1 rfl
--       constructor
--       rw [pgf.length, ← ih.2.1]
--     rename_i n
--     rw [rw_length_one_step]
--     use pgf.adjacent _ _ n ih.1 rfl
--     constructor
--     rw [pgf.length, ← ih.2.1]
    -- rcases h2
    -- · rename_i q
    --   rw [rw_length_one_step]
    --   use pgf.top_left _ ih.1 rfl
    --   constructor
    --   rw [PartialGrid.length, ← ih.2.1]



noncomputable def get_frontier_style (h : PartialGrid a b c d e) : Σ (h1 : pgf a b (c ++ d ++ e)),
  PLift ( h.length = h1.length) := by
  have H := pg_to_rev h
  have H2 := one_step_of_reg_w_len H.1
  have H3 := @pgf_of_st_w_len (a ++ b) _ _ _  H2.1 rfl h.left_frontier_is_false
     h.top_frontier_is_true
  use H3.1
  constructor
  rw [← H3.2.1, ← H2.2.1, ← H.2.1]
