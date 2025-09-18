import BraidProject.Grids
import BraidProject.SemiThue
import BraidProject.TrueFalse

inductive cell : List ℕ → List ℕ → List ℕ → List ℕ → Prop
  | empty : (cell [] [] [] [] : Prop)
  | top_bottom (i : ℕ) : cell [] [i] [] [i]
  | sides (i : ℕ) : cell [i] [] [i] []
  | top_left (i : ℕ) : cell [i] [i] [] []
  | adjacent (i k : ℕ) (h : Nat.dist i k = 1) : cell [i] [k] [i, k] [k, i]
  | separated (i j : ℕ) (h : i +2 ≤ j ∨ j+2 <= i) : cell [i] [j] [i] [j]

theorem grid_from_cell (h : cell a b c d) : grid a b c d := by
  induction h with
  | empty => exact grid.empty
  | top_bottom i => exact grid.top_bottom _
  | sides i => exact grid.sides _
  | top_left i => exact grid.top_left _
  | adjacent i k h => exact grid.adjacent _ _ h
  | separated i j h => exact grid.separated _ _ (or_dist_iff.mpr h)

@[simp]
theorem List.map_rev_rev : (List.map f (L.reverse)).reverse = List.map f L := by
  induction L with
  | nil => rfl
  | cons h t ih => simp [List.reverse_cons, ih]

def grid_option (a b c d : List (Option ℕ × Bool)) : Prop := grid (remover a.reverse) (remover b)
  (remover c.reverse) (remover d)

theorem grid_option_append_horiz (h1 : grid_option a b c d) (h2 : grid_option c e f g) : grid_option a (b ++ e) f (d ++ g) := by
  simp [grid_option, remover_split]
  exact grid.horizontal h1 h2

theorem grid_option_append_vert (h1 : grid_option a b c d) (h2 : grid_option e d f g) : grid_option (e ++ a) b (f ++ c) g := by
  simp [grid_option, remover_split]
  exact grid.vertical h1 h2

/-- A partial grid generalizes the notion of a grid to include "unfinished" grids. -/
inductive PartialGrid : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → List (Option ℕ × Bool) → List (Option ℕ × Bool) → Prop
  | single_grid (h : cell a b c d): PartialGrid (to_up a) (to_over b) (to_over d) [] (to_up c)
  | empty (a b : List (Option ℕ × Bool)) (ha : a.length > 0) (ha1 : is_false a)
      (hb : b.length > 0) (hb : is_true b) : PartialGrid a b [] (a ++ b) []
  | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : PartialGrid a b bot [] up)
      (g2 : PartialGrid up b2 bot2 mid2 up2) : PartialGrid a (b ++ b2) (bot ++ bot2) mid2 up2
  | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : List (Option ℕ × Bool)}
      (h : mid.length > 0)
      (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid up b2 bot2 mid2 up2) :
      PartialGrid a (b ++ b2) bot (mid ++ bot2 ++ mid2) up2
  | vertical_append_one (g1 : PartialGrid a b bot [] up) (g2 : PartialGrid a1 bot bot2 mid2 up2) :
      PartialGrid (a1 ++ a) b bot2 mid2 (up2 ++ up)
  | vertical_append (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid a1 bot bot2 mid2 up2) (h : mid.length > 0) :
      PartialGrid (a1 ++ a) b bot2 (mid2 ++ up2 ++ mid) up

theorem grid_of_PartialGrid (h : PartialGrid a b d [] c) : grid_option a b c d := by
  generalize he : ([] : List (Option ℕ × Bool)) = e at h
  induction h with
  | single_grid h =>
    unfold grid_option
    simp only [remover_up_rev, remover_over]
    exact grid_from_cell h
  | empty a b =>
    exfalso
    apply congr_arg List.length at he
    rename_i ha hb
    simp [ha, hb] at he
    linarith
  | horizontal_append_one _ _ ih1 ih2 =>
    specialize ih1 rfl
    specialize ih2 he
    exact grid_option_append_horiz ih1 ih2
  | horizontal_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at he
    specialize g1_ih he.1.symm
    specialize g2_ih he.2.2.symm
    have H := grid_option_append_horiz g1_ih g2_ih
    rw [he.2.1, List.append_nil] at H
    exact H
  | vertical_append_one _ _ ih1 ih2 =>
    specialize ih1 rfl
    specialize ih2 he
    exact grid_option_append_vert ih1 ih2
  | vertical_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at he
    specialize g1_ih he.2.2.symm
    specialize g2_ih he.1.symm
    have H := grid_option_append_vert g1_ih g2_ih
    rw [he.2.1, List.nil_append] at H
    exact H
