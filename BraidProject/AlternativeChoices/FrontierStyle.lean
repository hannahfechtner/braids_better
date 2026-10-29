import BraidProject.DataCarrying.SemiThue
import BraidProject.PartialGrid.Basic
import BraidProject.Relations
import BraidProject.UnfinishedFrontier
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

open Relations

noncomputable def add_cell (h : FrontierStyle a b c)
    (hg : grid_style_nontrivial i j) (fe : c = k ++ i ++ l) :
    Σ c', (h1 : FrontierStyle a b c') × PLift (c' = k ++ j ++ l) ×
    PLift (h.length < h1.length) := by
  cases hg with
  | basic n =>
    use k ++ [(none, true), (none, false)] ++ l,  FrontierStyle.top_left _ h fe
    exact ⟨⟨by simp⟩, ⟨by simp [FrontierStyle.length]⟩⟩
  | apart hd =>
    rename_i i j
    use k ++ [(some j, true), (some i, false)] ++ l, FrontierStyle.separated _ _ hd h fe
    exact ⟨⟨by simp⟩, ⟨by simp [FrontierStyle.length]⟩⟩
  | close hd =>
    rename_i i j
    use k ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ l
    use FrontierStyle.adjacent _ _ hd h fe
    exact ⟨⟨by simp⟩, ⟨by simp [FrontierStyle.length]⟩⟩

theorem length_skeleton (h : FrontierStyle a b c) (hc : c = a ++ b) : h.length = 0 := by
  induction h with
  | skeleton a b ha hb =>
    simp [FrontierStyle.length]
  | empty h =>
    exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
  | top_bottom i h ih =>
    exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
  | sides i h ih =>
    exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
  | top_left i h ih =>
    exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
  | adjacent i j hd h hc ih =>
    rename_i c5 c6 _
    have : c5 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c6  =
      (c5 ++ [(some j, true)]) ++ [(some i, true), (some j, false)] ++ ((some i, false) :: c6) := by simp
    rw [this] at hc
    exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim
  | separated i k h h ih =>
    exact (true_false_not_infix_false_true hc (is_false_left_side h) (is_true_top_side h)).elim


noncomputable def to_SemiThue_grid_style (h : FrontierStyle a b mid) :
  {h1 : SemiThueData grid_style (a ++ b) mid // h.length = SemiThueData.length grid_style.length h1} := by
  induction h with
  | skeleton ha ha1 hb hb =>
    use SemiThueData.refl
    simp [SemiThueData.length, FrontierStyle.length]
  | empty h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThueData.trans ih.1 (SemiThueData.step _ _ (grid_style.empty))
    simp [SemiThueData.length, ih.2]
  | top_bottom i h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThueData.trans ih.1 (SemiThueData.step _ _ (grid_style.up _))
    simp [SemiThueData.length, ih.2]
  | sides i h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThueData.trans ih.1 (SemiThueData.step _ _ (grid_style.over _))
    simp [SemiThueData.length, ih.2]
  | top_left i h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThueData.trans ih.1 (SemiThueData.step _ _ (grid_style.basic _))
    simp [SemiThueData.length, ih.2]
  | adjacent i j hd h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThueData.trans ih.1 (SemiThueData.step _ _ (grid_style.close hd))
    simp [SemiThueData.length, ih.2]
  | separated i k hd h hc ih =>
    subst hc
    rw [FrontierStyle.length]
    use SemiThueData.trans ih.1 (SemiThueData.step _ _ (grid_style.apart hd))
    simp [SemiThueData.length, ih.2]


noncomputable def of_SemiThueDerivation_grid_style (h : SemiThueDataDerivation grid_style ab c)
  (hab : ab = a ++ b)
  (ha : is_false a) (hal : a.length > 0) (hb : is_true b) (hbl : b.length > 0) :
  {h2 : FrontierStyle a b c // SemiThueDataDerivation.length grid_style.length h = FrontierStyle.length h2} := by
  induction h with
  | refl =>
    subst hab
    use FrontierStyle.skeleton a b hal ha hbl hb
    simp [SemiThueDataDerivation.length, FrontierStyle.length]
  | step h1 h2 ih =>
    rename_i d e f g l
    have H1 := @SemiThueDataDerivation.toSemiThueData_length _ _ grid_style.length _ _ h1
    specialize ih hab
    rcases h2
    · rw [SemiThueDataDerivation.length]
      use FrontierStyle.top_left _ ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    · rw [SemiThueDataDerivation.length]
      use FrontierStyle.sides _ ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    · rw [SemiThueDataDerivation.length]
      use FrontierStyle.top_bottom _ ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    · rw [SemiThueDataDerivation.length]
      use FrontierStyle.empty ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    · rename_i n
      rw [SemiThueDataDerivation.length]
      use FrontierStyle.separated _ _ n ih.1 rfl
      rw [FrontierStyle.length, ← ih.2]
      rfl
    rename_i n
    rw [SemiThueDataDerivation.length]
    use FrontierStyle.adjacent _ _ n ih.1 rfl
    rw [FrontierStyle.length, ← ih.2]
    rfl


end FrontierStyle

open Relations

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
    have H := PartialGrid.add_cell_with_length s (grid_style.empty) (by rw [← t.1.1, hc])
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
    have H := PartialGrid.add_cell_with_length s (grid_style.up _) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [PartialGrid.FrontierStyle.length, ← t.1.2, ←hl.1]
    rfl
  | sides i h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := PartialGrid.add_cell_with_length s (grid_style.over _) (by rw [← t.1.1, hc])
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [PartialGrid.FrontierStyle.length, ← t.1.2, ← hl.1]
    rfl
  | top_left i h hc ih =>
    rename_i m n o
    rcases ih with ⟨p, q, r, s, t⟩
    have H := PartialGrid.add_cell_with_length s (grid_style.basic _) (by rw [← t.1.1, hc])
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
    have H := PartialGrid.add_cell_with_length s (grid_style.close hd) (by rw [← t.1.1, hc])
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
    have H := PartialGrid.add_cell_with_length s (grid_style.apart hd) H1
    rcases H with ⟨nb, nm, nu, h3, fe, sx, px, hl⟩
    use nb, nm, nu, h3
    constructor
    constructor
    · rw [fe.1]
    simp only [PartialGrid.FrontierStyle.length, ← t.1.2]
    exact hl.1.symm


section Ford

variable {α : Type} {rels : List α → List α → Type}
  {rels_length : {a b : List α} → rels a b → ℕ}

def ford {a b a' b' : List α} (ha : a = a') (hb : b = b') (h : SemiThueData rels a b) :
    SemiThueData rels a' b' := by
  subst ha hb
  exact h

@[simp]
theorem length_ford {a b a' b' : List α} (ha : a = a') (hb : b = b')
    (h : SemiThueData rels a b) :
    SemiThueData.length rels_length (ford ha hb h) = SemiThueData.length rels_length h := by
  subst ha hb
  rfl

end Ford

noncomputable def to_SemiThueData_grid_style (h : PartialGrid a b c d e) :
  {h1 : SemiThueData grid_style (a ++ b) (c ++ d ++ e) // h.length = SemiThueData.length grid_style.length h1} := by
  induction h with
  | single_cell h =>
    cases h with
    | empty =>
      use SemiThueData.of_rel (grid_style.empty)
      rfl
    | top_bottom i =>
      use SemiThueData.of_rel (grid_style.up _)
      rfl
    | sides i =>
      use SemiThueData.of_rel (grid_style.over _)
      rfl
    | top_left i =>
      use SemiThueData.of_rel (grid_style.basic _)
      rfl
    | adjacent i k h =>
      use SemiThueData.of_rel (grid_style.close h)
      rfl
    | separated i j h =>
      use SemiThueData.of_rel (grid_style.apart h)
      rfl
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, List.nil_append]
    use SemiThueData.refl
    rfl
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases g1_ih with ⟨h3, h3_len⟩
    rcases g2_ih with ⟨h5, h5_len⟩
    exact ⟨SemiThueData.trans (ford (List.append_assoc _ _ _) (List.append_assoc _ _ _)
      (SemiThueData.append_right h3)) (ford rfl (by simp only [List.append_nil, List.append_assoc]) (SemiThueData.append_left h5)),
      by simp [PartialGrid.length, h3_len, h5_len]⟩
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases g1_ih with ⟨h3, h3_len⟩
    rcases g2_ih with ⟨h5, h5_len⟩
    exact ⟨SemiThueData.trans (ford (List.append_assoc _ _ _) (List.append_assoc _ _ _)
      (SemiThueData.append_right h3))
      (ford rfl (by simp only [List.append_assoc]) (SemiThueData.append_left h5)),
      by simp [PartialGrid.length, h3_len, h5_len]⟩
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases g1_ih with ⟨h3, h3_len⟩
    rcases g2_ih with ⟨h5, h5_len⟩
    exact ⟨SemiThueData.trans (ford (List.append_assoc _ _ _).symm
      (by simp only [List.append_nil, List.append_assoc]) (SemiThueData.append_left h3))
      (ford rfl (List.append_assoc _ _ _) (SemiThueData.append_right h5)),
      by simp [PartialGrid.length, h3_len, h5_len]⟩
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases g1_ih with ⟨h3, h3_len⟩
    rcases g2_ih with ⟨h5, h5_len⟩
    exact ⟨SemiThueData.trans (ford (List.append_assoc _ _ _).symm
      (by simp [List.append_assoc]; rfl) (SemiThueData.append_left h3))
      (ford rfl (by simp [List.append_assoc]) (SemiThueData.append_right h5)),
      by simp [PartialGrid.length, h3_len, h5_len]⟩

noncomputable def to_FrontierStyle (h : PartialGrid a b c d e) :
    {h1 : FrontierStyle a b (c ++ d ++ e) // h.length = h1.length} := by
  have H := to_SemiThueData_grid_style h
  have H2 := @SemiThueData.toSemiThueDataDerivation_length _ _ _ _ grid_style.length H.1
  have H3 := @FrontierStyle.of_SemiThueDerivation_grid_style (a ++ b) _ _ _  (SemiThueData.toSemiThueDataDerivation H.1) rfl h.left_side_is_false
    (PartialGrid.left_side_length_pos h) h.top_side_is_true (PartialGrid.top_length_pos h)
  use H3.1
  aesop
