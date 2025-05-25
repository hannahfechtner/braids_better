import BraidProject.Grids_S
import BraidProject.SemiThue
import BraidProject.TrueFalse

inductive cell_zero : List ℕ → List ℕ → List ℕ → List ℕ → Prop
  | empty : (cell_zero [] [] [] [] : Prop)
  | top_bottom (i : ℕ) : cell_zero [] [i] [] [i]
  | sides (i : ℕ) : cell_zero [i] [] [i] []

inductive cell_one : List ℕ → List ℕ → List ℕ → List ℕ → Prop
  | top_left (i : ℕ) : cell_one [i] [i] [] []
  | adjacent (i k : ℕ) (h : Nat.dist i k = 1) : cell_one [i] [k] [i, k] [k, i]
  | separated (i j : ℕ) (h : i +2 ≤ j ∨ j+2 <= i) : cell_one [i] [j] [i] [j]

theorem grid_from_cell_zero (h : cell_zero a b c d) : grid_sz a b c d 0 := by
  induction h with
  | empty => exact grid_sz.empty
  | top_bottom i => exact grid_sz.top_bottom _
  | sides i => exact grid_sz.sides _

theorem grid_from_cell_one (h : cell_one a b c d) : grid_sz a b c d 1 := by
  induction h with
  | top_left i => exact grid_sz.top_left _
  | adjacent i k h => exact grid_sz.adjacent _ _ h
  | separated i j h => exact grid_sz.separated _ _ (or_dist_iff.mpr h)

@[simp]
theorem List.map_rev_rev : (List.map f (L.reverse)).reverse = List.map f L := by
  induction L with
  | nil => rfl
  | cons h t ih => simp [List.reverse_cons, ih]

def grid_option (a b c d : List (Option ℕ × Bool)) (n : ℕ): Prop := grid_sz (remover a.reverse) (remover b)
  (remover c.reverse) (remover d) n

theorem grid_option_append_horiz (h1 : grid_option a b c d n1 ) (h2 : grid_option c e f g n2) : grid_option a (b ++ e) f (d ++ g) (n1 + n2) := by
  simp [grid_option, remover_split]
  exact grid_sz.horizontal h1 h2

theorem grid_option_append_vert (h1 : grid_option a b c d n1) (h2 : grid_option e d f g n2) : grid_option (e ++ a) b (f ++ c) g (n1 + n2) := by
  simp [grid_option, remover_split]
  exact grid_sz.vertical h1 h2

/-- A partial grid_sz generalizes the notion of a grid_sz to include "unfinished" grids. -/
inductive PartialGrid : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → List (Option ℕ × Bool) → List (Option ℕ × Bool) → ℕ → Prop
  | single_zero (h : cell_zero a b c d): PartialGrid (to_up a) (to_over b) (to_over d) [] (to_up c) 0
  | single_one (h : cell_one a b c d): PartialGrid (to_up a) (to_over b) (to_over d) [] (to_up c) 1
  | empty (a b : List (Option ℕ × Bool)) (ha : a.length > 0) (ha1 : is_false a)
      (hb : b.length > 0) (hb : is_true b) : PartialGrid a b [] (a ++ b) [] 0
  | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : PartialGrid a b bot [] up n1)
      (g2 : PartialGrid up b2 bot2 mid2 up2 n2) : PartialGrid a (b ++ b2) (bot ++ bot2) mid2 up2 (n1 + n2)
  | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : List (Option ℕ × Bool)}
      (h : mid.length > 0)
      (g1 : PartialGrid a b bot mid up n1) (g2 : PartialGrid up b2 bot2 mid2 up2 n2) :
      PartialGrid a (b ++ b2) bot (mid ++ bot2 ++ mid2) up2 (n1 + n2)
  | vertical_append_one (g1 : PartialGrid a b bot [] up n1) (g2 : PartialGrid a1 bot bot2 mid2 up2 n2) :
      PartialGrid (a1 ++ a) b bot2 mid2 (up2 ++ up) (n1 + n2)
  | vertical_append (g1 : PartialGrid a b bot mid up n1) (g2 : PartialGrid a1 bot bot2 mid2 up2 n2) (h : mid.length > 0) :
      PartialGrid (a1 ++ a) b bot2 (mid2 ++ up2 ++ mid) up (n1 + n2)

theorem grid_of_PartialGrid (h : PartialGrid a b d [] c n) : grid_option a b c d n := by
  generalize he : ([] : List (Option ℕ × Bool)) = e at h
  induction h with
  | single_zero h =>
    unfold grid_option
    simp only [remover_up_rev, remover_over]
    exact grid_from_cell_zero h
  | single_one h =>
    unfold grid_option
    simp only [remover_up_rev, remover_over]
    exact grid_from_cell_one h
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
