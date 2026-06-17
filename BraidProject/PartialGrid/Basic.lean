import BraidProject.Grids_C
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.NewListFacts
import BraidProject.Relations
import BraidProject.Additions.InvRev
import BraidProject.SignedList_C

namespace Braid

open List SignedList SignedOptionList

/-- A partial grid generalizes the notion of a grid to include "unfinished" grids. -/
inductive PartialGrid : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
    List (Option ℕ × Bool) → List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
  | single_cell {a b c d} (h : CellData a b c d) :
      PartialGrid (to_vertical_edge a) (to_horizontal_edge b)
        (to_horizontal_edge c) [] (to_vertical_edge d)
  | empty (a b : List (Option ℕ × Bool)) (ha : a.length > 0) (ha1 : is_false a)
        (hb : b.length > 0) (hb : is_true b) :
      PartialGrid a b [] (a ++ b) []
  | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : PartialGrid a b bot [] up)
        (g2 : PartialGrid up b2 bot2 mid2 up2) :
      PartialGrid a (b ++ b2) (bot ++ bot2) mid2 up2
  | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : List (Option ℕ × Bool)}
        (g1 : PartialGrid a b bot mid up)
        (g2 : PartialGrid up b2 bot2 mid2 up2) (h : mid.length > 0) :
      PartialGrid a (b ++ b2) bot (mid ++ bot2 ++ mid2) up2
  | vertical_append_one (g1 : PartialGrid a b bot [] up)
        (g2 : PartialGrid a1 bot bot2 mid2 up2) :
      PartialGrid (a1 ++ a) b bot2 mid2 (up2 ++ up)
  | vertical_append (g1 : PartialGrid a b bot mid up)
        (g2 : PartialGrid a1 bot bot2 mid2 up2) (h : mid.length > 0) :
      PartialGrid (a1 ++ a) b bot2 (mid2 ++ up2 ++ mid) up

namespace PartialGrid

def length (h : PartialGrid a b c d e) :=
  match h with
  | single_cell h =>
    by cases h with
    | empty => exact 0
    | top_bottom i => exact 0
    | sides i => exact 0
    | top_left i => exact 1
    | adjacent i k h => exact 1
    | separated i j h => exact 1
  | empty a b ha ha1 hb hb1 => 0
  | horizontal_append_one g1 g2 => g1.length + g2.length
  | horizontal_append g1 g2 h => g1.length + g2.length
  | vertical_append_one g1 g2 => g1.length + g2.length
  | vertical_append g1 g2 h => g1.length + g2.length

open GridData in
def reflect (h : PartialGrid a b c d e) :
    (h1 : PartialGrid (FreeGroup.invRev b) (FreeGroup.invRev a) (FreeGroup.invRev e) (FreeGroup.invRev d) (FreeGroup.invRev c)) ×
    PLift (h.length = h1.length) := by
  match h with
  | single_cell h =>
    rw [FreeGroup.invRev_to_vertical_edge, FreeGroup.invRev_to_horizontal_edge, FreeGroup.invRev_to_vertical_edge, FreeGroup.invRev_to_horizontal_edge, FreeGroup.invRev_empty]
    cases h with
    | empty =>
      use PartialGrid.single_cell (CellData.empty)
      exact ⟨rfl⟩
    | top_bottom i =>
      use PartialGrid.single_cell (CellData.sides i)
      exact ⟨rfl⟩
    | sides i =>
      use PartialGrid.single_cell (CellData.top_bottom i)
      exact ⟨rfl⟩
    | top_left i =>
      use PartialGrid.single_cell (CellData.top_left i)
      exact ⟨rfl⟩
    | adjacent i k h =>
      use PartialGrid.single_cell (CellData.adjacent k i (by rw [Nat.dist_comm] at h; exact h))
      exact ⟨rfl⟩
    | separated i j h =>
      use PartialGrid.single_cell (CellData.separated j i (by rw [Nat.dist_comm] at h; exact h))
      exact ⟨rfl⟩
  | empty a b ha ha1 hb hb1 =>
    rw [FreeGroup.invRev_append]
    rw [← FreeGroup.invRev_length] at ha
    rw [← FreeGroup.invRev_length] at hb
    use PartialGrid.empty (FreeGroup.invRev b) (FreeGroup.invRev a) hb (FreeGroup.invRev_false hb1) ha (FreeGroup.invRev_true ha1)
    simp [PartialGrid.length]
    exact ⟨trivial⟩
  | horizontal_append_one g1 g2 =>
    rw [FreeGroup.invRev_append, FreeGroup.invRev_append]
    have ⟨h3, len3⟩ := reflect g1
    have ⟨h4, len4⟩ := reflect g2
    use PartialGrid.vertical_append_one h3 h4
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]⟩
  | horizontal_append g1 g2 h_mid =>
    rw [FreeGroup.invRev_append, FreeGroup.invRev_append, FreeGroup.invRev_append, ← List.append_assoc]
    have ⟨h3, len3⟩ := reflect g1
    have ⟨h4, len4⟩ := reflect g2
    rw [← FreeGroup.invRev_length] at h_mid
    use PartialGrid.vertical_append h3 h4 h_mid
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]⟩
  | vertical_append_one g1 g2 =>
    rw [FreeGroup.invRev_append, FreeGroup.invRev_append]
    have ⟨h3, len3⟩ := reflect g1
    have ⟨h4, len4⟩ := reflect g2
    use PartialGrid.horizontal_append_one h3 h4
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]⟩
  | vertical_append g1 g2 h_mid =>
    rw [FreeGroup.invRev_append, FreeGroup.invRev_append, FreeGroup.invRev_append, ← List.append_assoc]
    have ⟨h3, len3⟩ := reflect g1
    have ⟨h4, len4⟩ := reflect g2
    rw [← FreeGroup.invRev_length] at h_mid
    use PartialGrid.horizontal_append h3 h4 h_mid
    exact ⟨by simp [PartialGrid.length, len3.1, len4.1]⟩

/-- a helper function, which gives the conclusion of `reflect` on a partial grid that has all 5
parts of its frame already `FreeGroup.invRev`-images -/
private def reflect_of_invRev_images (a b c d e) (h : PartialGrid a1 b1 c1 d1 e1) :
    a1 = FreeGroup.invRev a → b1 = FreeGroup.invRev b → c1 = FreeGroup.invRev c →
    d1 = FreeGroup.invRev d → e1 = FreeGroup.invRev e →
    (h1 : PartialGrid b a e d c) × PLift (h.length = h1.length) := by
  intro a_eq b_eq c_eq d_eq e_eq
  apply congr_arg FreeGroup.invRev at a_eq
  rw [FreeGroup.invRev_invRev] at a_eq
  apply congr_arg FreeGroup.invRev at b_eq
  rw [FreeGroup.invRev_invRev] at b_eq
  apply congr_arg FreeGroup.invRev at c_eq
  rw [FreeGroup.invRev_invRev] at c_eq
  apply congr_arg FreeGroup.invRev at d_eq
  rw [FreeGroup.invRev_invRev] at d_eq
  apply congr_arg FreeGroup.invRev at e_eq
  rw [FreeGroup.invRev_invRev] at e_eq
  rw [← a_eq, ← b_eq, ← c_eq, ← d_eq, ← e_eq]
  apply reflect h

def right_frontier_is_false (h : PartialGrid a b c d e) : is_false e :=
  match h with
  | single_cell  _ => is_false_to_vertical_edge
  | empty _ _ _ _ _ _ => is_false_nil
  | horizontal_append_one g1 g2 => right_frontier_is_false g2
  | horizontal_append g1 g2 _ => right_frontier_is_false g2
  | vertical_append_one g1 g2 => is_false_append (right_frontier_is_false g2) (right_frontier_is_false g1)
  | vertical_append g1 g2 _ => right_frontier_is_false g1

def top_side_is_true (h : PartialGrid a b c d e) : is_true b :=
  match h with
  | single_cell _ => is_true_to_horizontal_edge
  | empty _ _ _ _ _ hb => hb
  | horizontal_append_one g1 g2 => is_true_append (top_side_is_true g1) (top_side_is_true g2)
  | horizontal_append g1 g2 _ => is_true_append (top_side_is_true g1) (top_side_is_true g2)
  | vertical_append_one g1 _ => top_side_is_true g1
  | vertical_append g1 _ _ => top_side_is_true g1

def left_side_is_false (h : PartialGrid a b c d e) : is_false a :=
  match h with
  | single_cell _ => is_false_to_vertical_edge
  | empty _ _ _ ha1 _ _ => ha1
  | horizontal_append_one g1 _ => left_side_is_false g1
  | horizontal_append g1 _ _ => left_side_is_false g1
  | vertical_append_one g1 g2 => is_false_append (left_side_is_false g2) (left_side_is_false g1)
  | vertical_append g1 g2 _ => is_false_append (left_side_is_false g2) (left_side_is_false g1)

def bottom_frontier_is_true (h : PartialGrid a b c d e) : is_true c :=
  match h with
  | single_cell _ => is_true_to_horizontal_edge
  | empty _ _ _ _ _ _ => is_true_nil
  | horizontal_append_one g1 g2 => is_true_append (bottom_frontier_is_true g1) (bottom_frontier_is_true g2)
  | horizontal_append g1 _ _ => bottom_frontier_is_true g1
  | vertical_append_one _ g2 => bottom_frontier_is_true g2
  | vertical_append _ g2 _ => bottom_frontier_is_true g2

theorem left_side_length_pos (h : PartialGrid a b c d e) : a.length > 0 := by
  induction h with
  | single_cell  => exact to_vertical_edge_length_pos
  | empty => assumption
  | horizontal_append_one => assumption
  | horizontal_append => assumption
  | vertical_append_one =>
    rw [List.length_append]
    omega
  | vertical_append =>
    rw [List.length_append]
    omega

theorem top_length_pos (h : PartialGrid a b c d e) : b.length > 0 := by
  induction h with
  | single_cell => exact to_horizontal_edge_length_pos
  | empty => assumption
  | horizontal_append_one =>
    rw [List.length_append]
    omega
  | horizontal_append =>
    rw [List.length_append]
    omega
  | vertical_append_one => assumption
  | vertical_append => assumption

def extend_left_side_w_length (h : PartialGrid a b c d e) (a₂) (h2 : is_false a₂) (h3 : a₂ ≠ []) :
    (h1 : PartialGrid (a₂ ++ a) b [] (a₂ ++ c ++ d) e) × PLift (h.length = h1.length) := by
  match h with
  | single_cell h =>
    cases a₂ with
    | nil => simp at h3
    | cons head tail =>
      rename_i c d
      rw [List.append_nil]
      use PartialGrid.vertical_append_one (PartialGrid.single_cell h)
        (PartialGrid.empty (head :: tail) (to_horizontal_edge c) (by simp)
        h2 to_horizontal_edge_length_pos is_true_to_horizontal_edge)
      exact ⟨by simp [PartialGrid.length]⟩
  | empty a b ha ha1 hb hb1 =>
    rw [List.append_nil, ← List.append_assoc]
    use PartialGrid.empty (a₂ ++ a) b (by rw [List.length_append]; omega)
      (is_false_append h2 ha1) hb hb1
    exact ⟨by simp [PartialGrid.length]⟩
  | horizontal_append_one g1 g2 =>
    rename_i m n o p q
    rw [← List.append_assoc, ← List.append_nil (a₂ ++ n)]
    have ih1 := extend_left_side_w_length g1 a₂ h2 h3
    use PartialGrid.horizontal_append ih1.1 g2
      (by grind [List.length_pos_iff.mpr h3])
    exact ⟨by simp [PartialGrid.length, ih1.2.down]⟩
  | horizontal_append g1 g2 h_mid =>
    rw [← List.append_assoc, ← List.append_assoc]
    have ih1 := extend_left_side_w_length g1 a₂ h2 h3
    use PartialGrid.horizontal_append ih1.1 g2 (by grind)
    exact ⟨by simp [PartialGrid.length, ih1.2.down]⟩
  | vertical_append_one g1 g2 =>
    rw [← List.append_assoc]
    have ih2 := extend_left_side_w_length g2 a₂ h2 h3
    use PartialGrid.vertical_append_one g1 ih2.1
    exact ⟨by simp [PartialGrid.length, ih2.2.down]⟩
  | vertical_append g1 g2 h_mid =>
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    have ih2 := extend_left_side_w_length g2 a₂ h2 h3
    use PartialGrid.vertical_append g1 ih2.1 h_mid
    exact ⟨by simp [PartialGrid.length, ih2.2.down]⟩

def extend_left_side (h : PartialGrid a b c d e) (a₂) (h2 : is_false a₂) (h3 : a₂ ≠ []) :
    PartialGrid (a₂ ++ a) b [] (a₂ ++ c ++ d) e := (extend_left_side_w_length h a₂ h2 h3).1

 def extend_top_side_w_length  (h : PartialGrid a b c d e) (b2) (h2 : is_true b2) (h3 : b2 ≠ []) :
    (h1 : PartialGrid a (b ++ b2) c (d ++ e ++ b2) []) × PLift  (h.length = h1.length) := by
  rcases reflect h with ⟨h4, ⟨len⟩⟩
  have ⟨h5, ⟨len2⟩⟩ := PartialGrid.extend_left_side_w_length h4 (FreeGroup.invRev b2)
    (FreeGroup.invRev_false h2) (fun h => h3 (FreeGroup.invRev_eq_nil_iff.mp h))
  rcases reflect h5 with ⟨h6, ⟨len3⟩⟩
  rcases reflect_of_invRev_images _ _ _ _ _ h6 rfl rfl rfl rfl rfl with ⟨h7, ⟨len4⟩⟩
  have H7 := @reflect_of_invRev_images _ _ _ _ _ (b ++ b2) a [] (d ++ e ++ b2) c h7
    (FreeGroup.invRev_append).symm rfl FreeGroup.invRev_empty (by simp) rfl
  rcases H7 with ⟨h8, ⟨len5⟩⟩
  use h8
  constructor
  omega

def extend_top_side  (h : PartialGrid a b c d e) (b₂) (h2 : is_true b₂) (h3 : b₂ ≠ []) :
    PartialGrid a (b ++ b₂) c (d ++ e ++ b₂) []  := (extend_top_side_w_length h b₂ h2 h3).1

theorem middle_right_frontier_not_both_nil : PartialGrid a b c d e → d = [] → e = [] → False := by
  intro h
  induction h with
  | single_cell h =>
    intro ha hb
    simp only [to_vertical_edge, map_reverse] at hb
    rename_i c _
    match c with
    | [] => split at hb; simp only [cons_ne_self] at hb; aesop
    | c1 :: c2 => split at hb; simp only [cons_ne_self] at hb; aesop
  | empty a b ha ha1 hb hb1 =>
    intro h1
    apply congr_arg List.length at h1
    simp only [length_append, List.length, Nat.add_eq_zero_iff, length_eq_zero_iff] at h1
    rw [h1.1] at ha
    simp at ha
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    exact g2_ih
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro h1
    apply g2_ih
    simp only [append_assoc, append_eq_nil_iff] at h1
    exact h1.2.2
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro h1 h2
    simp only [append_eq_nil_iff] at h2
    apply g2_ih h1
    exact h2.1
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro h1 h2
    simp only [append_assoc, append_eq_nil_iff] at h1
    apply g1_ih h1.2.2 h2

theorem bottom_middle_frontier_not_both_nil : PartialGrid a b c d e → c = [] → d = [] → False := by
  intro h
  induction h with
  | single_cell h =>
    intro ha hb
    simp only [to_horizontal_edge] at ha
    rename_i c
    match c with
    | [] => split at ha; simp only [cons_ne_self] at ha; aesop
    | c1 :: c2 => split at ha; simp only [cons_ne_self] at ha; aesop
  | empty a b ha ha1 hb hb1 =>
    intro _ h1
    apply congr_arg List.length at h1
    simp only [length_append, List.length, Nat.add_eq_zero_iff, length_eq_zero_iff] at h1
    rw [h1.1] at ha
    simp at ha
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro h1 h2
    simp only [append_eq_nil_iff] at h1
    exact g1_ih h1.1 rfl
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro h1 h2
    simp only [append_assoc, append_eq_nil_iff] at h2
    exact g2_ih h2.2.1 h2.2.2
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    exact g2_ih
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro h1 h2
    simp only [append_assoc, append_eq_nil_iff] at h2
    exact g2_ih h1 h2.1

def middle_spec (d : List (α × Bool)) := PLift (d = []) ⊕ Σ front mid caboose,
  PLift (d = [(front, false)] ++ mid ++ [(caboose, true)])

noncomputable def middle_frontier_spec (h : PartialGrid a b c d e) :
    PLift (d = []) ⊕ Σ front mid caboose,
    PLift (d = [(front, false)] ++ mid ++ [(caboose, true)]) := by
  induction h with
  | single_cell h =>
    left; exact {down := rfl}
  | empty a b ha ha1 hb hb1 =>
    right
    match a with
    | [] => simp at ha
    | (a1, true) :: a2 =>
      specialize ha1 (a1, true) (by simp)
      simp only [Bool.true_eq_false] at ha1
    | (a1, false) :: a2 =>
      use a1
      match hbr : b.reverse with
      | [] =>
        rw [List.reverse_eq_nil_iff.mp hbr] at hb
        simp only [List.length_nil, gt_iff_lt, lt_self_iff_false] at hb
      | (b1, false) :: b2 =>
        apply congr_arg List.reverse at hbr
        rw [List.reverse_reverse] at hbr
        rw [hbr] at hb1
        specialize hb1 (b1, false) (by simp)
        simp only [Bool.false_eq_true] at hb1
      | (b1, true) :: b2 =>
        use (a2 ++ b2.reverse), b1
        constructor
        apply congr_arg List.reverse at hbr
        grind
  | horizontal_append_one g1 g2 g1_ih g2_ih => assumption
  | horizontal_append g1 g2 h1 g1_ih g2_ih =>
    rename_i bot2 _ _
    rcases g1_ih with ⟨ha⟩ | hb
    · rw [ha.1] at h1
      simp at h1
    rcases g2_ih with hc | hd
    · right; rw [hc.1, List.append_nil];
      rcases hc with ⟨f1, c1, h1⟩
      induction bot2 using List.reverseRecOn with
      | nil => rw [List.append_nil]; exact hb
      | append_singleton f2 c2 _ =>
        rcases hb with ⟨f1, m1, c1, h1⟩
        rw [h1.1]
        have H : Σ cb, PLift (c2 = (cb, true)) :=
          is_true_singleton <| (is_true_of_append (bottom_frontier_is_true g2)).2
        rcases H with ⟨cb, cbspec⟩
        rw [cbspec.1]
        use f1, m1 ++ [(c1, true)] ++ f2, cb
        exact {down := by simp}
    rcases hb with ⟨front1, m1, caboose1, h1⟩
    rcases hd with ⟨front2, m2, caboose2, h2⟩
    right
    rw [h1.1, h2.1]
    use front1, m1 ++ [(caboose1, true)] ++ bot2 ++ [(front2, false)] ++ m2, caboose2
    exact {down := by simp}
  | vertical_append_one g1 g2 g1_ih g2_ih => assumption
  | vertical_append g1 g2 h g1_ih g2_ih =>
    right
    rcases g1_ih with h1 | h2
    · rw [h1.1] at h
      simp at h
    rcases g2_ih with h3 | h4
    · rw [h3.1, List.nil_append]
      rcases h2 with ⟨f1, m1, c1, spec⟩
      rename_i up2
      cases up2 with
      | nil =>
        use f1,m1, c1
        constructor
        rw [spec.1]; rfl
      | cons head tail =>
        have H : is_false [head] := by
          exact (is_false_of_append (right_frontier_is_false g2)).1
        rcases is_false_singleton H with ⟨hf, spec2⟩
        use hf, tail ++ [(f1, false)] ++ m1, c1
        constructor
        simp only [spec2.1, spec.1, List.cons_append, List.nil_append, List.append_assoc]
    rcases h2 with ⟨f1, m1, c1, spec1⟩
    rcases h4 with ⟨f2, m2, c2, spec2⟩
    rw [spec1.1, spec2.1]
    rename_i up2
    use f2, m2 ++ [(c2, true)] ++ up2 ++ [(f1, false)] ++ m1, c1
    exact {down := by simp}

def middle_frontier_end_spec (d : List (α × Bool)) := PLift (d = []) ⊕
  Σ mid caboose, PLift (d = mid ++ [(caboose, true)])

def middle_frontier_start_spec (d : List (α × Bool)) := PLift (d = []) ⊕
  Σ front mid, PLift (d = [(front, false)] ++ mid)

def middle_frontier_start_spec_of_append (h : middle_frontier_start_spec (d1 ++ d2)) :
    middle_frontier_start_spec d1 := by
  cases d1 with
  | nil => left; exact {down := rfl}
  | cons head tail =>
    right
    rcases h with h1 | ⟨f, m, spec⟩
    · simp only [List.cons_append, reduceCtorEq] at h1
      apply h1.1.elim
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at spec
    use f, tail
    rw [spec.1.1]
    constructor
    simp

def middle_frontier_start_spec_from_spec (h : middle_spec d) : middle_frontier_start_spec d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use f, m ++ [(c, true)]
  exact spec

def middle_frontier_end_spec_from_spec (h : middle_spec d) : middle_frontier_end_spec d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use [(f, false)] ++ m, c
  exact spec

end PartialGrid

namespace GridData

/- a version of grids which are read in the north-easterly direction, mirroring the conventions for partial grids -/
def PartialGridStyle (a b c d : List (Option ℕ × Bool)) : Type :=
  GridData (toList a.reverse) (toList b) (toList c) (toList d.reverse)

namespace PartialGridStyle
def append_horizontal
    (h1 : GridData.PartialGridStyle a b c d) (h2 : GridData.PartialGridStyle d e f g) :
    GridData.PartialGridStyle a (b ++ e) (c ++ f) g := by
  simp only [GridData.PartialGridStyle, toList_append]
  exact GridData.horizontal h1 h2

def append_vertical
    (h1 : GridData.PartialGridStyle a b c d) (h2 : GridData.PartialGridStyle e c f g) :
    GridData.PartialGridStyle (e ++ a) b f (g ++ d) := by
  simp only [GridData.PartialGridStyle, reverse_append, toList_append]
  exact GridData.vertical h1 h2

noncomputable def of_PartialGrid (h : PartialGrid a b c [] d) :
    GridData.PartialGridStyle a b c d := by
  generalize hm : ([] : List (Option ℕ × Bool)) = m at h
  induction h with
  | single_cell h =>
    unfold GridData.PartialGridStyle
    simp only [toList_to_vertical_edge_rev, toList_to_horizontal_edge]
    exact of_CellData h
  | empty a b =>
    apply congr_arg List.length at hm
    simp only [List.length_nil, List.length_append] at hm
    linarith
  | horizontal_append_one _ _ ih1 ih2 =>
    exact GridData.PartialGridStyle.append_horizontal (ih1 rfl) (ih2 hm)
  | horizontal_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at hm
    have H := GridData.PartialGridStyle.append_horizontal (g1_ih hm.1.symm) (g2_ih hm.2.2.symm)
    rw [hm.2.1, List.append_nil] at H
    exact H
  | vertical_append_one _ _ ih1 ih2 =>
    exact GridData.PartialGridStyle.append_vertical (ih1 rfl) (ih2 hm)
  | vertical_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at hm
    have H := GridData.PartialGridStyle.append_vertical (g1_ih hm.2.2.symm) (g2_ih hm.1.symm)
    rw [hm.2.1, List.nil_append] at H
    exact H

end PartialGridStyle
end GridData
end Braid
