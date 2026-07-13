import BraidProject.SemiThue_length_general
import BraidProject.PartialGrid.AddCell

namespace Braid

namespace PartialGrid
open SignedList
inductive FrontierStyle : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → Type
  | skeleton (a b) (ha : a.length > 0) (ha1 : is_false a) (hb : b.length > 0) (hb : is_true b ):
      FrontierStyle a b (a ++ b)
  | empty (h : FrontierStyle a b c) (hc : c = c1 ++ [(none, false), (none, true)] ++ c2) :
      FrontierStyle a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | top_bottom (i : ℕ) (h : FrontierStyle a b c) (hc : c = c1 ++ [(none, false), (some i, true)] ++ c2) :
      FrontierStyle a b (c1 ++ [(some i, true), (none, false)] ++ c2)
  | sides (i : ℕ) (h : FrontierStyle a b c) (hc : c = (c1 ++ [(some i, false), (none, true)] ++ c2)) :
      FrontierStyle a b (c1 ++ [(none, true), (some i, false)] ++ c2)
  | top_left (i : ℕ) (h : FrontierStyle a b c) (hc : c = (c1 ++ [(some i, false), (some i, true)] ++ c2)) :
      FrontierStyle a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | adjacent (i j : ℕ) (hd : Nat.dist i j = 1) (h : FrontierStyle a b c)
      (hc : c = (c1 ++ [(some i, false), (some j, true)] ++ c2)) :
      FrontierStyle a b (c1 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c2)
  | separated (i k : ℕ) (hd : Nat.dist i k ≥ 2) (h : FrontierStyle a b c)
     (hc : c = c1 ++ [(some i, false), (some k, true)] ++ c2) :
      FrontierStyle a b (c1 ++ [(some k, true), (some i, false)] ++ c2)

namespace FrontierStyle

def length (h : FrontierStyle a b c) : Nat :=
  match h with
  | FrontierStyle.skeleton _ _ _ _ _ _ => 0
  | FrontierStyle.empty h _ => FrontierStyle.length h
  | FrontierStyle.top_bottom i h _ => FrontierStyle.length h
  | FrontierStyle.sides _ h _ => FrontierStyle.length h
  | FrontierStyle.top_left _ h _ => FrontierStyle.length h + 1
  | FrontierStyle.adjacent _ _ _ h _ => FrontierStyle.length h + 1
  | FrontierStyle.separated _ _ _ h _ => FrontierStyle.length h + 1

noncomputable def is_false_left_side (h : FrontierStyle a b c) : is_false a := by
  induction h; all_goals assumption

noncomputable def is_true_top_side (h : FrontierStyle a b c) : is_true b := by
  induction h; all_goals assumption

-- noncomputable def add_cell (h : FrontierStyle a b c)
--     (hg : grid_style_nontrivial i j) (fe : c = k ++ i ++ l) :
--     Σ c', (h1 : FrontierStyle a b c') × PLift (c' = k ++ j ++ l) ×
--     PLift (h.length < h1.length) := by
--   cases hg with
--   | basic n =>
--     use k ++ [(none, true), (none, false)] ++ l,  FrontierStyle.top_left _ h fe
--     exact ⟨⟨by simp⟩, ⟨by simp [FrontierStyle.length]⟩⟩
--   | apart hd =>
--     rename_i i j
--     use k ++ [(some j, true), (some i, false)] ++ l, FrontierStyle.separated _ _ hd h fe
--     exact ⟨⟨by simp⟩, ⟨by simp [FrontierStyle.length]⟩⟩
--   | close hd =>
--     rename_i i j
--     use k ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ l
--     use FrontierStyle.adjacent _ _ hd h fe
--     exact ⟨⟨by simp⟩, ⟨by simp [FrontierStyle.length]⟩⟩

-- theorem length_skeleton (h : FrontierStyle a b c) (hc : c = a ++ b) : h.length = 0 := by
--   induction h with
--   | skeleton a b ha hb =>
--     simp [FrontierStyle.length]
--   | empty h =>
--     exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
--   | top_bottom i h ih =>
--     exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
--   | sides i h ih =>
--     exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
--   | top_left i h ih =>
--     exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
--   | adjacent i j hd h hc ih =>
--     rename_i c5 c6 _
--     have : c5 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c6  =
--       (c5 ++ [(some j, true)]) ++ [(some i, true), (some j, false)] ++ ((some i, false) :: c6) := by simp
--     rw [this] at hc
--     exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
--   | separated i k h h ih =>
--     exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim

noncomputable def to_SemiThue_grid_style (h : FrontierStyle a b mid) :
  {h1 : SemiThue grid_style (a ++ b) mid // h.length = SemiThue.grid_style.length h1} := by
  induction h with
  | skeleton ha ha1 hb hb =>
    use SemiThue.refl
    simp [SemiThue.grid_style.length, FrontierStyle.length]
  | empty h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThue.trans ih.1 (SemiThue.step _ _ (grid_style.empty))
    simp [SemiThue.grid_style.length, ih.2]
  | top_bottom i h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThue.trans ih.1 (SemiThue.step _ _ (grid_style.up _))
    simp [SemiThue.grid_style.length, ih.2]
  | sides i h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThue.trans ih.1 (SemiThue.step _ _ (grid_style.over _))
    simp [SemiThue.grid_style.length, ih.2]
  | top_left i h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThue.trans ih.1 (SemiThue.step _ _ (grid_style.basic _))
    simp [SemiThue.grid_style.length, ih.2]
  | adjacent i j hd h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThue.trans ih.1 (SemiThue.step _ _ (grid_style.close hd))
    simp [SemiThue.grid_style.length, ih.2]
  | separated i k hd h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThue.trans ih.1 (SemiThue.step _ _ (grid_style.apart hd))
    simp [SemiThue.grid_style.length, ih.2]


noncomputable def of_SemiThueDerivation_grid_style (h : SemiThueDerivation grid_style ab c)
  (hab : ab = a ++ b)
  (ha : is_false a) (hal : a.length > 0) (hb : is_true b) (hbl : b.length > 0) :
  {h2 : FrontierStyle a b c // SemiThueDerivation.grid_style.length h = FrontierStyle.length h2} := by
  induction h with
  | refl =>
    subst hab
    use FrontierStyle.skeleton a b hal ha hbl hb
    simp [SemiThueDerivation.grid_style.length, FrontierStyle.length]
    rfl
  | step h1 h2 ih =>
    rename_i d e f g l
    have H1 := SemiThueDerivation.grid_style.toSemiThue_with_length h1
    specialize ih hab
    rcases h2
    · rw [SemiThueDerivation.grid_style.length]
      use FrontierStyle.top_left _ ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    · rw [SemiThueDerivation.grid_style.length]
      use FrontierStyle.sides _ ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    · rw [SemiThueDerivation.grid_style.length]
      use FrontierStyle.top_bottom _ ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    · rw [SemiThueDerivation.grid_style.length]
      use FrontierStyle.empty ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    · rename_i n
      rw [SemiThueDerivation.grid_style.length]
      use FrontierStyle.separated _ _ n ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    rename_i n
    rw [SemiThueDerivation.grid_style.length]
    use FrontierStyle.adjacent _ _ n ih.1 rfl
    rw [FrontierStyle.length, ← ih.2]
    rfl


end FrontierStyle

noncomputable def to_SemiThue_grid_style (h : PartialGrid a b c d e) :
  {h1 : SemiThue grid_style (a ++ b) (c ++ d ++ e) // h.length = SemiThue.grid_style.length h1} := by
  induction h with
  | single_cell h =>
    cases h with
    | empty =>
      use SemiThue.grid_style.empty_w_length.1
      simp [PartialGrid.length, SemiThue.grid_style.empty_w_length.2]
    | top_bottom i =>
      use (SemiThue.grid_style.top_bottom_w_length i).1
      simp [PartialGrid.length, (SemiThue.grid_style.top_bottom_w_length i).2]
    | sides i =>
      use (SemiThue.grid_style.sides_w_length i).1
      simp [PartialGrid.length, (SemiThue.grid_style.sides_w_length i).2]
    | top_left i =>
      use (SemiThue.grid_style.top_left_w_length i).1
      simp [PartialGrid.length, (SemiThue.grid_style.top_left_w_length i).2]
    | adjacent i k h =>
      use (SemiThue.grid_style.adjacent_w_length i k h).1
      simp [PartialGrid.length, (SemiThue.grid_style.adjacent_w_length i k h).2]
    | separated i j h =>
      use (SemiThue.grid_style.separated_w_length i j h).1
      simp [PartialGrid.length, (SemiThue.grid_style.separated_w_length i j h).2]
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, List.nil_append]
    use SemiThue.refl
    simp [PartialGrid.length, SemiThue.grid_style.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i l m n o p q r s
    rw [PartialGrid.length]
    rw [List.append_nil] at g1_ih
    rcases g1_ih with ⟨h3, h3_len⟩
    have h4 := SemiThue.grid_style.append_right_w_length p h3
    rw [List.append_assoc] at h4
    rcases g2_ih with ⟨h5, h5_len⟩
    have h6 := SemiThue.grid_style.append_left_w_length n h5
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at h6
    use SemiThue.trans h4.1 h6.1
    aesop
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i l m n o p q r s t
    rw [PartialGrid.length]
    rcases g1_ih with ⟨h3, h3_len⟩
    have h4 := SemiThue.grid_style.append_right_w_length q h3
    rw [List.append_assoc] at h4
    rcases g2_ih with ⟨h5, h5_len⟩
    have h6 := SemiThue.grid_style.append_left_w_length (n ++ o) h5
    rw [← List.append_assoc, ← List.append_assoc] at h6
    rw [List.append_assoc o r s, ← List.append_assoc n o (r ++ s)]
    use SemiThue.trans h4.1 h6.1
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i l m n o p q r s
    rw [PartialGrid.length]
    rw [List.append_nil] at g1_ih
    rcases g1_ih with ⟨h3, h3_len⟩
    have h4 := SemiThue.grid_style.append_left_w_length p h3
    rw [← List.append_assoc] at h4
    rcases g2_ih with ⟨h5, h5_len⟩
    have h6 := SemiThue.grid_style.append_right_w_length o h5
    rw [List.append_assoc, List.append_assoc, List.append_assoc, ← List.append_assoc q] at h6
    use SemiThue.trans h4.1 h6.1
    aesop
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i l m n o p q r s
    rw [PartialGrid.length]
    rcases g1_ih with ⟨h3, h3_len⟩
    have h4 := SemiThue.grid_style.append_left_w_length p h3
    rcases g2_ih with ⟨h5, h5_len⟩
    have h6 := SemiThue.grid_style.append_right_w_length (n ++ o) h5
    rw [List.append_assoc, List.append_assoc, List.append_assoc, ← List.append_assoc m n o] at h6
    rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
    use SemiThue.trans h4.1 h6.1
    aesop

noncomputable def to_FrontierStyle (h : PartialGrid a b c d e) :
    {h1 : FrontierStyle a b (c ++ d ++ e) // h.length = h1.length} := by
  have H := to_SemiThue_grid_style h
  have H2 := SemiThue.grid_style.toSemiThueDerivation_with_length H.1
  have H3 := @FrontierStyle.of_SemiThueDerivation_grid_style (a ++ b) _ _ _  H2.1 rfl h.left_side_is_false
    (PartialGrid.left_side_length_pos h) h.top_side_is_true (PartialGrid.top_length_pos h)
  use H3.1
  aesop

noncomputable def of_FrontierStyle (h1 : PartialGrid.FrontierStyle a b mid) :
  Σ c d e, (h : PartialGrid a b c d e) ×
  PLift (mid = c ++ d ++ e ∧ h.length = h1.length) := by
  induction h1 with
  | skeleton ha ha1 hb hb1 =>
    use [], (a ++ b), []
    use PartialGrid.empty a b ha ha1 hb hb1
    constructor
    constructor
    · simp
    simp [PartialGrid.length, PartialGrid.FrontierStyle.length]
  | empty h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := add_any_cell_with_length s (grid_style.empty) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [PartialGrid.FrontierStyle.length, ← t.1.2, ← hl.1]
    rfl
  | top_bottom i h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := add_empty_cell_w_len s (grid_style_trivial.up _) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [PartialGrid.FrontierStyle.length, ← t.1.2, hl.1]
  | sides i h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := add_empty_cell_w_len s (grid_style_trivial.over _) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [PartialGrid.FrontierStyle.length, ← t.1.2, hl.1]
  | top_left i h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := PartialGrid.add_any_cell_with_length s (grid_style.basic _) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [PartialGrid.FrontierStyle.length, ← t.1.2]
    exact hl.1.symm
  | adjacent i j hd h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := PartialGrid.add_any_cell_with_length s (grid_style.close hd) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [PartialGrid.FrontierStyle.length, ← t.1.2]
    exact hl.1.symm
  | separated i k hd h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H1 : p ++ q ++ r = n ++ [(some i, false), (some k, true)] ++ o := by
      rw [← t.1.1, hc]
    have H2 : grid_style_nontrivial [(some i, false), (some k, true)] [(some k, true), (some i, false)] :=
      grid_style_nontrivial.apart hd
    have H := PartialGrid.add_any_cell_with_length s (grid_style.apart hd) H1
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [PartialGrid.FrontierStyle.length, ← t.1.2]
    exact hl.1.symm
