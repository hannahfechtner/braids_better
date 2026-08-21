import BraidProject.Grids_C
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.PartialGrid.Bounded
import BraidProject.Relations

namespace Braid

open SignedList

inductive pgf : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → Type
  | skeleton (a b) (ha : a.length > 0) (ha1 : is_false a) (hb : b.length > 0) (hb1 : is_true b ):
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

def pgf.length (h : pgf a b c) : Nat :=
  match h with
  | pgf.skeleton _ _ _ _ _ _ => 0
  | pgf.empty h _ => pgf.length h
  | pgf.top_bottom i h _ => pgf.length h
  | pgf.sides _ h _ => pgf.length h
  | pgf.top_left _ h _ => pgf.length h + 1
  | pgf.adjacent _ _ _ h _ => pgf.length h + 1
  | pgf.separated _ _ _ h _ => pgf.length h + 1

noncomputable def pgf_left_false (h : pgf a b c) : is_false a := by
  induction h; all_goals assumption

noncomputable def pgf_top_true (h : pgf a b c) : is_true b := by
  induction h; all_goals assumption

noncomputable def pgf_remove (h : grid_style x y) (hf : pgf a b (c ++ y++ d)) :
  pgf a b (c ++ x ++ d) := by
  generalize hz : c ++ y ++ d = z at hf
  induction hf generalizing c d with
  | skeleton ha ha1 hb hb1 => sorry
  | empty h_inner hc_inner ih =>
    rename_i c1 c2
    subst hc_inner
    sorry
  | top_bottom i h_inner hc_inner ih =>
    rename_i c1 c2
    subst hc_inner
    sorry
  | sides i h_inner hc_inner ih =>
    rename_i c1 c2
    subst hc_inner
    sorry
  | top_left i h_inner hc_inner ih =>
    rename_i c1 c2
    subst hc_inner
    sorry
  | adjacent i j hd h_inner hc_inner ih =>
    rename_i c1 c2
    subst hc_inner
    sorry
  | separated i k hd h_inner hc_inner ih =>
    rename_i c1 c2
    subst hc_inner
    sorry

def pgf_remove' (h : grid_style x y) (hf : pgf a b (c ++ y++ d)) :
  pgf a b (c ++ x ++ d) := by
  generalize hz : c ++ y ++ d = z
  rw [hz] at hf
  cases hf with
  | skeleton ha ha1 hb hb1 => sorry
  | empty h2 hc =>
    rename_i e f g
    have : (PLift (f = c ∧ d = g)) ⊕
      Σ f₁ f₂, PLift (c = f₁ ∧ d = f₂ ++ [(none, true), (none, false)] ++ g) := by sorry
    rcases this with ⟨hf, hd⟩ | ⟨f₁, f₂, hc, hd⟩
    · have : y = [(none, true), (none, false)] := by
        rw [← hf, hd] at hz
        apply List.append_cancel_right at hz
        exact List.append_cancel_left hz
      rw [hc, hf, ← hd] at h2
      convert h2
      sorry
    

    sorry
  | top_bottom i h hc => sorry
  | sides i h hc => sorry
  | top_left i h hc => sorry
  | adjacent i j hd h hc => sorry
  | separated i k hd h hc => sorry

noncomputable def add_cell_w_len_pgf (h : pgf a b c)
    (hg : grid_style_nontrivial i j) (fe : c = k ++ i ++ l) :
    Σ c', (h1 : pgf a b c') × PLift (c' = k ++ j ++ l) ×
    PLift (h.length < h1.length) := by
  cases hg with
  | basic n =>
    use k ++ [(none, true), (none, false)] ++ l
    use pgf.top_left _ h fe
    constructor
    constructor
    simp
    constructor
    simp [pgf.length]
  | apart hd =>
    rename_i i j
    use k ++ [(some j, true), (some i, false)] ++ l
    use pgf.separated _ _ hd h fe
    constructor
    constructor
    simp
    constructor
    simp [pgf.length]
  | close hd =>
    rename_i i j
    use k ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ l
    use pgf.adjacent _ _ hd h fe
    constructor
    constructor
    simp
    constructor
    simp [pgf.length]

--true_false_not_infix_false_true
-- theorem true_false_not_infix_false_true (h : c1 ++ [(c2, true), (c3, false)] ++ c4 = a ++ b)
--     (ha : is_false a) (hb : is_true b) : False := by
--   have : c1 ++ [(c2, true), (c3, false)] ++ c4 =
--     c1 ++ [(c2, true)] ++ ([(c3, false)] ++ c4) := by simp
--   rw [this] at h
--   rcases List.append_eq_append_iff.mp h with ⟨m, hm1, hm2⟩ | ⟨m, hm1, hm2⟩
--   · rw [hm1] at ha
--     specialize ha (c2, true) (by simp)
--     simp only [Bool.true_eq_false] at ha
--   rw [hm2] at hb
--   specialize hb (c3, false) (by simp)
--   simp only [Bool.false_eq_true] at hb

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

-- GENERALIZE so then this can just go into semithue

def rw_length (h : SemiThue grid_style a b) : ℕ :=
  match h with
  | SemiThue.refl => 0
  | SemiThue.step h =>
    match h with
    | grid_style.basic n => 1
    | grid_style.over n => 0
    | grid_style.up n => 0
    | grid_style.empty => 0
    | grid_style.apart h => 1
    | grid_style.close h => 1
  | SemiThue.trans h1 h2 => rw_length h1 + rw_length h2

def rw_length_rev (h : SemiThue reversing a b) : ℕ :=
  match h with
  | SemiThue.refl => 0
  | SemiThue.step h => 1
  | SemiThue.trans h1 h2 => rw_length_rev h1 + rw_length_rev h2

def rw_length_one_step (h : SemiThueDerivation grid_style a b) : ℕ :=
  match h with
  | SemiThueDerivation.refl => 0
  | SemiThueDerivation.step h1 h =>
    match h with
    | grid_style.basic n => rw_length_one_step h1 + 1
    | grid_style.over n => rw_length_one_step h1 + 0
    | grid_style.up n => rw_length_one_step h1 + 0
    | grid_style.empty => rw_length_one_step h1 + 0
    | grid_style.apart h => rw_length_one_step h1 + 1
    | grid_style.close h => rw_length_one_step h1 + 1

def rw_length_one_step_rev (h : SemiThueDerivation reversing a b) : ℕ :=
  match h with
  | SemiThueDerivation.refl => 0
  | SemiThueDerivation.step h1 h => rw_length_one_step_rev h1 + 1

noncomputable def one_step_trans
  (h1 : SemiThueDerivation grid_style a b) (h2 : SemiThueDerivation grid_style b c) :
    {h3 : SemiThueDerivation grid_style a c //
    rw_length_one_step h3 = rw_length_one_step h1 + rw_length_one_step h2} := by
  induction h2
  · use h1
    simp [rw_length_one_step]
  rename_i d e f g h i j k
  specialize k h1
  rcases k with ⟨h4, len4⟩
  match j with
  | basic n =>
    use h4.step (grid_style.basic n)
    rw [rw_length_one_step, rw_length_one_step, len4, add_assoc]
  | over n =>
    use h4.step (grid_style.over n)
    rw [rw_length_one_step, rw_length_one_step, len4, add_assoc]
  | up n =>
    use h4.step (grid_style.up n)
    rw [rw_length_one_step, rw_length_one_step, len4, add_assoc]
  | empty =>
    use h4.step (grid_style.empty)
    rw [rw_length_one_step, rw_length_one_step, len4, add_assoc]
  | apart h =>
    use h4.step (grid_style.apart h)
    rw [rw_length_one_step, rw_length_one_step, len4, add_assoc]
  | close h =>
    use h4.step (grid_style.close h)
    rw [rw_length_one_step, rw_length_one_step, len4, add_assoc]

noncomputable def one_step_of_reg_w_len {a b} (h1 : SemiThue grid_style a b ) :
    {h2 : SemiThueDerivation grid_style a b // rw_length h1 = rw_length_one_step h2} := by
  induction h1
  · use SemiThueDerivation.refl
    simp [rw_length, rw_length_one_step]
  · rename_i c d e f h
    use SemiThueDerivation.step (SemiThueDerivation.refl) h
    cases h
    all_goals rw [rw_length, rw_length_one_step, rw_length_one_step]
  rename_i ih1 ih2
  use (one_step_trans ih1.1 ih2.1).1
  rw [rw_length, (one_step_trans ih1.1 ih2.1).2]
  aesop

noncomputable def reg_of_one_step_w_len :
    (h1 : SemiThueDerivation grid_style a b) → (Σ h2 : SemiThue grid_style a b,
    PLift (rw_length h2 = rw_length_one_step h1)) := by
  intro h1
  induction h1
  · use SemiThue.refl
    constructor
    simp [rw_length, rw_length_one_step]
  rename_i h1 h2
  use h2.1.trans (SemiThue.step h1)
  constructor
  rw [rw_length, h2.2.1]
  cases h1
  all_goals rw [rw_length_one_step, rw_length]


noncomputable def SemiThue_empty_w_len : {h : SemiThue grid_style [(none, false), (none, true)] [(none, true), (none, false)] // rw_length h = 0}:= by
  rw [← List.nil_append [(none, false), (none, true)], ← List.nil_append [(none, true), (none, false)],
    ← List.append_nil ([] ++ [(none, false), (none, true)]), ← List.append_nil ([] ++ [(none, true), (none, false)])]
  use SemiThue.step (grid_style.empty)
  simp [rw_length]

noncomputable def SemiThue_top_bottom_w_len (i : ℕ) :
  {h : SemiThue grid_style [(none, false), (some i, true)] [(some i, true), (none, false)] // rw_length h = 0} := by
  rw [← List.nil_append [(none, false), (some i, true)], ← List.nil_append [(some i, true), (none, false)],
    ← List.append_nil ([] ++ [(none, false), (some i, true)]), ← List.append_nil ([] ++ [(some i, true), (none, false)])]
  use SemiThue.step (grid_style.up i)
  simp [rw_length]

noncomputable def SemiThue_sides_w_len (i : ℕ) :
  {h : SemiThue grid_style [(some i, false), (none, true)] [(none, true), (some i, false)] // rw_length h = 0} := by
  rw [← List.nil_append [(some i, false), (none, true)], ← List.nil_append [(none, true), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (none, true)]), ← List.append_nil ([] ++ [(none, true), (some i, false)])]
  use SemiThue.step (grid_style.over i)
  simp [rw_length]

noncomputable def SemiThue_top_left_w_len (i : ℕ) :
  {h : SemiThue grid_style [(some i, false), (some i, true)] [(none, true), (none, false)] // rw_length h = 1} := by
  rw [← List.nil_append [(none, true), (none, false)], ← List.nil_append [(some i, false), (some i, true)],
    ← List.append_nil ([] ++ [(none, true), (none, false)]), ← List.append_nil ([] ++ [(some i, false), (some i, true)])]
  use SemiThue.step (grid_style.basic i)
  simp [rw_length]

noncomputable def SemiThue_adjacent_w_len (i j : ℕ) (hd : Nat.dist i j = 1) :
  {h : SemiThue grid_style [(some i, false), (some j, true)] [(some j, true), (some i, true), (some j, false), (some i, false)] // rw_length h = 1} := by
  rw [← List.nil_append [(some i, false), (some j, true)], ← List.nil_append [(some j, true), (some i, true), (some j, false), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (some j, true)]), ← List.append_nil ([] ++ [(some j, true), (some i, true), (some j, false), (some i, false)])]
  use SemiThue.step (grid_style.close hd)
  simp [rw_length]

noncomputable def SemiThue_separated_w_len (i j : ℕ) (hd : Nat.dist i j ≥ 2) :
  {h : SemiThue grid_style [(some i, false), (some j, true)] [(some j, true), (some i, false)] // rw_length h = 1} := by
  rw [← List.nil_append [(some i, false), (some j, true)], ← List.nil_append [(some j, true), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (some j, true)]), ← List.append_nil ([] ++ [(some j, true), (some i, false)])]
  use SemiThue.step (grid_style.apart hd)
  simp [rw_length]

noncomputable def SemiThue_cons_w_len (h : SemiThue grid_style a b) :
    {h1 : SemiThue grid_style (c :: a) (c :: b) // rw_length h1 = rw_length h} := by
  induction h with
  | refl =>
    use SemiThue.refl
    simp [rw_length]
  | step h =>
    rw [← List.cons_append, ← List.cons_append]
    use SemiThue.step h
    rfl
  | trans h1 h2 ih1 ih2 =>
    use SemiThue.trans ih1.1 ih2.1
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
  erw [H.2, ih.2]

noncomputable def SemiThue_caboose_w_len (h : SemiThue grid_style a b) :
  {h1 : SemiThue grid_style (a ++ [c]) (b ++ [c]) // rw_length h1 = rw_length h }:= by
  induction h with
  | refl =>
    use SemiThue.refl
    simp [rw_length]
  | step h =>
    rename_i e f g i
    rw [List.append_assoc, List.append_assoc _ i]
    use SemiThue.step h
    rfl
  | trans h1 h2 ih1 ih2 =>
    use SemiThue.trans ih1.1 ih2.1
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

open Braid

noncomputable def pg_to_rev (h : PartialGrid a b c d e) :
  {h1 : SemiThue grid_style (a ++ b) (c ++ d ++ e) // h.length = rw_length h1} := by
  induction h with
  | single_cell h =>
    cases h with
    | empty =>
      use SemiThue_empty_w_len.1
      simp [PartialGrid.length, SemiThue_empty_w_len.2]
    | top_bottom i =>
      use (SemiThue_top_bottom_w_len i).1
      simp [PartialGrid.length, (SemiThue_top_bottom_w_len i).2]
    | sides i =>
      use (SemiThue_sides_w_len i).1
      simp [PartialGrid.length, (SemiThue_sides_w_len i).2]
    | top_left i =>
      use (SemiThue_top_left_w_len i).1
      simp [PartialGrid.length, (SemiThue_top_left_w_len i).2]
    | adjacent i k h =>
      use (SemiThue_adjacent_w_len i k h).1
      simp [PartialGrid.length, (SemiThue_adjacent_w_len i k h).2]
    | separated i j h =>
      use (SemiThue_separated_w_len i j h).1
      simp [PartialGrid.length, (SemiThue_separated_w_len i j h).2]
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, List.nil_append]
    use SemiThue.refl
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
    use SemiThue.trans h4.1 h6.1
    simp only [rw_length, h4.2, h6.2]
    aesop
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
    use SemiThue.trans h4.1 h6.1
    simp only [rw_length, h6.2, h4.2]
    aesop
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
    use SemiThue.trans h4.1 h6.1
    simp only [rw_length, h6.2, h4.2]
    aesop
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i l m n o p q r s
    rw [PartialGrid.length]
    rcases g1_ih with ⟨h3, h3_len⟩
    have h4 := SemiThue_append_left_w_len p h3
    rcases g2_ih with ⟨h5, h5_len⟩
    have h6 := SemiThue_append_right_w_len (n ++ o) h5
    rw [List.append_assoc, List.append_assoc, List.append_assoc, ← List.append_assoc m n o] at h6
    rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
    use SemiThue.trans h4.1 h6.1
    simp [rw_length, h6.2, h4.2]
    aesop

noncomputable def pgf_to_rev (h : pgf a b mid) :
  {h1 : SemiThue grid_style (a ++ b) mid // h.length = rw_length h1} := by
  induction h with
  | skeleton ha ha1 hb hb =>
    use SemiThue.refl
    simp [rw_length, pgf.length]
  | empty h hc ih =>
    subst hc
    rw [pgf.length]
    use SemiThue.trans ih.1 (SemiThue.step (grid_style.empty))
    simp [rw_length, ih.2]
  | top_bottom i h hc ih =>
    subst hc
    rw [pgf.length]
    use SemiThue.trans ih.1 (SemiThue.step (grid_style.up _))
    simp [rw_length, ih.2]
  | sides i h hc ih =>
    subst hc
    rw [pgf.length]
    use SemiThue.trans ih.1 (SemiThue.step (grid_style.over _))
    simp [rw_length, ih.2]
  | top_left i h hc ih =>
    subst hc
    rw [pgf.length]
    use SemiThue.trans ih.1 (SemiThue.step (grid_style.basic _))
    simp [rw_length, ih.2]
  | adjacent i j hd h hc ih =>
    subst hc
    rw [pgf.length]
    use SemiThue.trans ih.1 (SemiThue.step (grid_style.close hd))
    simp [rw_length, ih.2]
  | separated i k hd h hc ih =>
    subst hc
    rw [pgf.length]
    use SemiThue.trans ih.1 (SemiThue.step (grid_style.apart hd))
    simp [rw_length, ih.2]

noncomputable def pgf_of_st_w_len (h : SemiThueDerivation grid_style ab c) (hab : ab = a ++ b)
  (ha : is_false a) (hal : a.length > 0) (hb : is_true b) (hbl : b.length > 0) :
  {h2 : pgf a b c // rw_length_one_step h = pgf.length h2} := by
  induction h with
  | refl =>
    subst hab
    use pgf.skeleton a b hal ha hbl hb
    simp [rw_length_one_step, pgf.length]
  | step h1 h2 ih =>
    rename_i d e f g l
    have H1 := reg_of_one_step_w_len h1
    specialize ih hab
    rcases h2
    · rw [rw_length_one_step]
      use pgf.top_left _ ih.1 rfl
      rw [pgf.length, ← ih.2]
    · rw [rw_length_one_step]
      use pgf.sides _ ih.1 rfl
      rw [pgf.length, ← ih.2]
      rfl
    · rw [rw_length_one_step]
      use pgf.top_bottom _ ih.1 rfl
      rw [pgf.length, ← ih.2]
      rfl
    · rw [rw_length_one_step]
      use pgf.empty ih.1 rfl
      rw [pgf.length, ← ih.2]
      rfl
    · rename_i n
      rw [rw_length_one_step]
      use pgf.separated _ _ n ih.1 rfl
      rw [pgf.length, ← ih.2]
    rename_i n
    rw [rw_length_one_step]
    use pgf.adjacent _ _ n ih.1 rfl
    rw [pgf.length, ← ih.2]

noncomputable def get_frontier_style (h : PartialGrid a b c d e) :
    {h1 : pgf a b (c ++ d ++ e) // h.length = h1.length} := by
  have H := pg_to_rev h
  have H2 := one_step_of_reg_w_len H.1
  have H3 := @pgf_of_st_w_len (a ++ b) _ _ _  H2.1 rfl h.left_side_is_false
    (PartialGrid.left_side_length_pos h) h.top_side_is_true (PartialGrid.top_length_pos h)
  use H3.1
  aesop
