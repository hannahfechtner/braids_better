import BraidProject.PartialGrid.Basic

namespace Braid

/-- Bundle a `PartialGrid` together with its frame labels, so we can put a
homogeneous relation on all partial grids regardless of their frame. -/
structure AnyPartialGrid : Type where
  a : List (Option ℕ × Bool)
  b : List (Option ℕ × Bool)
  c : List (Option ℕ × Bool)
  d : List (Option ℕ × Bool)
  e : List (Option ℕ × Bool)
  grid : PartialGrid a b c d e

namespace PartialGrid

@[reducible] def toAny (h : PartialGrid a b c d e) : AnyPartialGrid :=
  ⟨_, _, _, _, _, h⟩

open SignedList

/-- One-step "sub-grid" relation: `lt_helper h₁ h` holds when `h` is one of the
four append constructors applied with `h₁` filling either the left/top (`g1`)
or right/bottom (`g2`) slot. -/
inductive lt_helper : AnyPartialGrid → AnyPartialGrid → Prop
  | horizontal_append_one_g1 {a b bot up b2 bot2 mid2 up2}
      (h1 : PartialGrid a b bot [] up)
      (h2 : PartialGrid up b2 bot2 mid2 up2) :
      lt_helper (toAny h1) (toAny (horizontal_append_one h1 h2))
  | horizontal_append_one_g2 {a b bot up b2 bot2 mid2 up2}
      (h1 : PartialGrid a b bot [] up)
      (h2 : PartialGrid up b2 bot2 mid2 up2) :
      lt_helper (toAny h2) (toAny (horizontal_append_one h1 h2))
  | horizontal_append_g1 {a b bot mid up b2 bot2 mid2 up2}
      (h1 : PartialGrid a b bot mid up)
      (h2 : PartialGrid up b2 bot2 mid2 up2) (hl : mid.length > 0) :
      lt_helper (toAny h1) (toAny (horizontal_append h1 h2 hl))
  | horizontal_append_g2 {a b bot mid up b2 bot2 mid2 up2}
      (h1 : PartialGrid a b bot mid up)
      (h2 : PartialGrid up b2 bot2 mid2 up2) (hl : mid.length > 0) :
      lt_helper (toAny h2) (toAny (horizontal_append h1 h2 hl))
  | vertical_append_one_g1 {a b bot up a1 bot2 mid2 up2}
      (h1 : PartialGrid a b bot [] up)
      (h2 : PartialGrid a1 bot bot2 mid2 up2) :
      lt_helper (toAny h1) (toAny (vertical_append_one h1 h2))
  | vertical_append_one_g2 {a b bot up a1 bot2 mid2 up2}
      (h1 : PartialGrid a b bot [] up)
      (h2 : PartialGrid a1 bot bot2 mid2 up2) :
      lt_helper (toAny h2) (toAny (vertical_append_one h1 h2))
  | vertical_append_g1 {a b bot mid up a1 bot2 mid2 up2}
      (h1 : PartialGrid a b bot mid up)
      (h2 : PartialGrid a1 bot bot2 mid2 up2) (hl : mid.length > 0) :
      lt_helper (toAny h1) (toAny (vertical_append h1 h2 hl))
  | vertical_append_g2 {a b bot mid up a1 bot2 mid2 up2}
      (h1 : PartialGrid a b bot mid up)
      (h2 : PartialGrid a1 bot bot2 mid2 up2) (hl : mid.length > 0) :
      lt_helper (toAny h2) (toAny (vertical_append h1 h2 hl))
  | extend_left_side {a b c d e a₂} (h : PartialGrid a b c d e)
      (h2 : is_false a₂) (h3 : a₂ ≠ []) :
      lt_helper (toAny h) (toAny (extend_left_side h a₂ h2 h3))
  | extend_top_side {a b c d e b₂} (h : PartialGrid a b c d e)
      (h2 : is_true b₂) (h3 : b₂ ≠ []) :
      lt_helper (toAny h) (toAny (extend_top_side h b₂ h2 h3))

/-- Strict partial order on partial grids: the transitive closure of `lt_helper`.
Irreflexive because each `lt_helper` step strictly decreases structural size. -/
def lt : AnyPartialGrid → AnyPartialGrid → Prop := Relation.TransGen lt_helper

/-- Total number of `single_cell` nodes in a partial grid. Unlike `length` (which
gives `0` for cells whose `CellData` is `empty`, `top_bottom`, or `sides`), this
metric counts every cell, including "empty" ones. Regions built with the `empty`
constructor contribute `0`. Serves as the primary key of the well-founded
metric; ties are broken by `spine_length`. -/
def size (h : PartialGrid a b c d e) : ℕ :=
  match h with
  | single_cell _ => 1
  | empty _ _ _ _ _ _ => 0
  | horizontal_append_one g1 g2 => g1.size + g2.size
  | horizontal_append g1 g2 _ => g1.size + g2.size
  | vertical_append_one g1 g2 => g1.size + g2.size
  | vertical_append g1 g2 _ => g1.size + g2.size

/-- Length of a partial grid's spine_length: `a.length + b.length` (left frame plus top
frame). The secondary (tie-breaking) key in the well-founded metric. -/
def spine_length (_ : PartialGrid a b c d e) : ℕ := a.length + b.length

/-- Lexicographic key on `AnyPartialGrid`: primary is `size`, secondary is
`spine_length`. -/
def metric (h : AnyPartialGrid) : ℕ ×ₗ ℕ := toLex (h.grid.size, h.grid.spine_length)

/-- Strict well-founded order on `AnyPartialGrid` given by `metric` under the
lexicographic ordering. Intended to dominate `lt_helper`, and therefore `lt`. -/
def lt_metric : AnyPartialGrid → AnyPartialGrid → Prop := InvImage (· < ·) metric

/-- `lt_metric` is well-founded: lifted from the well-founded strict order on
`ℕ ×ₗ ℕ` via `metric`. -/
theorem lt_metric_wf : WellFounded lt_metric :=
  InvImage.wf metric wellFounded_lt

/-- If a partial grid has a non-empty bottom frontier or right frontier, then it
must contain at least one `single_cell` node, so its `size` is positive. -/
theorem size_pos_of_c_or_e (h : PartialGrid a b c d e) :
    c ≠ [] ∨ e ≠ [] → 0 < h.size := by
  induction h with
  | single_cell _ => intro _; simp [size]
  | empty _ _ _ _ _ _ =>
    grind
  | horizontal_append_one g1 g2 ih1 ih2 =>
    intro hh
    show 0 < g1.size + g2.size
    rcases hh with hc | he
    · rw [ne_eq, List.append_eq_nil_iff, not_and_or] at hc
      aesop
    aesop
  | horizontal_append g1 g2 _ ih1 ih2 =>
    show _ → 0 < g1.size + g2.size
    aesop
  | vertical_append_one g1 g2 ih1 ih2 =>
    intro hh
    show 0 < g1.size + g2.size
    rcases hh with hc | he
    · aesop
    rw [ne_eq, List.append_eq_nil_iff, not_and_or] at he
    aesop
  | vertical_append g1 g2 _ ih1 ih2 =>
    intro hh
    show 0 < g1.size + g2.size
    aesop

private def extend_left_side_with_size (h : PartialGrid a b c d e) (a₂ : List (Option ℕ × Bool))
    (h2 : is_false a₂) (h3 : a₂ ≠ []) :
    (h1 : PartialGrid (a₂ ++ a) b [] (a₂ ++ c ++ d) e) ×
      PLift (h.length = h1.length ∧ h.size = h1.size) := by
  match h with
  | single_cell hh =>
    cases a₂ with
    | nil => simp at h3
    | cons head tail =>
      rename_i cCell dCell
      rw [List.append_nil]
      refine ⟨PartialGrid.vertical_append_one (PartialGrid.single_cell hh)
        (PartialGrid.empty (head :: tail) (to_horizontal_edge cCell) (by simp)
        h2 to_horizontal_edge_length_pos is_true_to_horizontal_edge), ⟨?_, ?_⟩⟩
      · simp [PartialGrid.length]
      · simp [PartialGrid.size]
  | empty a b ha ha1 hb hb1 =>
    rw [List.append_nil, ← List.append_assoc]
    refine ⟨PartialGrid.empty (a₂ ++ a) b (by rw [List.length_append]; omega)
      (is_false_append h2 ha1) hb hb1, ⟨?_, ?_⟩⟩
    · simp [PartialGrid.length]
    · simp [PartialGrid.size]
  | horizontal_append_one g1 g2 =>
    rename_i m n o p q
    rw [← List.append_assoc, ← List.append_nil (a₂ ++ n)]
    have ih1 := extend_left_side_with_size g1 a₂ h2 h3
    refine ⟨PartialGrid.horizontal_append ih1.1 g2
      (by grind [List.length_pos_iff.mpr h3]), ⟨?_, ?_⟩⟩
    · simp [PartialGrid.length, ih1.2.down.1]
    · simp [PartialGrid.size, ih1.2.down.2]
  | horizontal_append g1 g2 h_mid =>
    rw [← List.append_assoc, ← List.append_assoc]
    have ih1 := extend_left_side_with_size g1 a₂ h2 h3
    refine ⟨PartialGrid.horizontal_append ih1.1 g2 (by grind), ⟨?_, ?_⟩⟩
    · simp [PartialGrid.length, ih1.2.down.1]
    · simp [PartialGrid.size, ih1.2.down.2]
  | vertical_append_one g1 g2 =>
    rw [← List.append_assoc]
    have ih2 := extend_left_side_with_size g2 a₂ h2 h3
    refine ⟨PartialGrid.vertical_append_one g1 ih2.1, ⟨?_, ?_⟩⟩
    · simp [PartialGrid.length, ih2.2.down.1]
    · simp [PartialGrid.size, ih2.2.down.2]
  | vertical_append g1 g2 h_mid =>
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    have ih2 := extend_left_side_with_size g2 a₂ h2 h3
    refine ⟨PartialGrid.vertical_append g1 ih2.1 h_mid, ⟨?_, ?_⟩⟩
    · simp [PartialGrid.length, ih2.2.down.1]
    · simp [PartialGrid.size, ih2.2.down.2]
