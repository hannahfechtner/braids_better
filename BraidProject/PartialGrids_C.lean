import BraidProject.Grids_C
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.NewListFacts
import BraidProject.Relations

-- @[simp]
-- theorem List.map_rev_rev : (List.map f (L.reverse)).reverse = List.map f L := by simp only [map_reverse,
--   reverse_reverse]
def gridt_option (a b c d : List (Option ℕ × Bool)) : Type := gridt (remover a.reverse) (remover b)
  (remover c.reverse) (remover d)

def gridt_option_append_horiz (h1 : gridt_option a b c d) (h2 : gridt_option c e f g) : gridt_option a (b ++ e) f (d ++ g) := by
  simp [gridt_option, remover_append]
  exact gridt.horizontal h1 h2

def gridt_option_append_vert (h1 : gridt_option a b c d) (h2 : gridt_option e d f g) : gridt_option (e ++ a) b (f ++ c) g := by
  simp [gridt_option, remover_append]
  exact gridt.vertical h1 h2

def gs_of_real (h : grid_style_real a b) : grid_style a b := by
  match h with
  | grid_style_real.basic n => exact grid_style.basic n
  | grid_style_real.apart hdist => exact grid_style.apart hdist
  | grid_style_real.close hdist => exact grid_style.close hdist

noncomputable def grid_style_real_split (h : grid_style_real i j) :
    Σ a b, PLift (i = [(some a, false), (some b, true)]) := by
  induction h with
  | basic =>
    rename_i n
    use n, n
    exact {down := rfl}
  | apart h =>
    rename_i i j
    use i, j
    exact {down := rfl}
  | close h =>
    rename_i i j
    use i, j
    exact {down := rfl}


noncomputable def empty_fill_split (h : empty_fill i j) :
    Σ a b, PLift (i = [(a, false), (b, true)]) := by
  induction h with
  | empty =>
    use none, none
    exact {down := rfl}
  | over i =>
    use some i, none
    exact {down := rfl}
  | up i =>
    use none, some i
    exact {down := rfl}

/-- A partial gridt generalizes the notion of a gridt to include "unfinished" gridts. -/
inductive PartialGrid : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
  | single_gridt (h : cell a b c d): PartialGrid (to_up a) (to_over b) (to_over d) [] (to_up c)
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

namespace PartialGrid

def length (h : PartialGrid a b c d e) :=
  match h with
  | single_gridt h =>
    by cases h with
    | empty => exact 0
    | top_bottom i => exact 0
    | sides i => exact 0
    | top_left i => exact 1
    | adjacent i k h =>exact 1
    | separated i j h => exact 1
  | empty a b ha ha1 hb hb1 => 0
  | horizontal_append_one g1 g2 => g1.length + g2.length
  | horizontal_append h g1 g2 => g1.length + g2.length
  | vertical_append_one g1 g2 => g1.length + g2.length
  | vertical_append g1 g2 h => g1.length + g2.length

noncomputable def right_frontier_is_false (h : PartialGrid a b c d e) : is_false e := by
  induction h with
  | single_gridt  => exact is_false_up
  | empty => exact is_false_nil
  | horizontal_append_one => assumption
  | horizontal_append => assumption
  | vertical_append_one _ _ g1_ih g2_ih =>
    exact is_false_of_false_false g2_ih g1_ih
  | vertical_append => assumption

noncomputable def  top_frontier_is_true (h : PartialGrid a b c d e) : is_true b := by
  induction h with
  | single_gridt => exact is_true_over
  | empty  => assumption
  | horizontal_append_one _ _ g1_ih g2_ih => exact is_true_of_true_true g1_ih g2_ih
  | horizontal_append _ _ _ g1_ih g2_ih => exact is_true_of_true_true g1_ih g2_ih
  | vertical_append_one => assumption
  | vertical_append => assumption

noncomputable def left_frontier_is_false (h : PartialGrid a b c d e) : is_false a := by
  induction h with
    | single_gridt => exact is_false_up
    | empty => assumption
    | horizontal_append_one => assumption
    | horizontal_append => assumption
    | vertical_append_one _ _ g1_ih g2_ih =>
      exact is_false_of_false_false g2_ih g1_ih
    | vertical_append _ _ _ ih1 ih2 => exact is_false_of_false_false ih2 ih1

noncomputable def bottom_frontier_is_true (h : PartialGrid a b c d e) : is_true c := by
  induction h with
    | single_gridt => exact is_true_over
    | empty => exact is_true_nil
    | horizontal_append_one => exact is_true_of_true_true (by assumption) (by assumption)
    | horizontal_append => assumption
    | vertical_append_one => assumption
    | vertical_append => assumption

theorem left_length_pos (h : PartialGrid a b c d e) : a.length > 0 := by
  induction h with
  | single_gridt  => exact to_up_len_pos
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
  | single_gridt => exact to_over_len_pos
  | empty => assumption
  | horizontal_append_one =>
    rw [List.length_append]
    omega
  | horizontal_append =>
    rw [List.length_append]
    omega
  | vertical_append_one => assumption
  | vertical_append => assumption

theorem mid_length_neq_one (h : PartialGrid a b c d e) : d.length ≠ 1 := by
  intro hd
  induction h with
  | single_gridt => simp at hd
  | empty => rw [List.length_append] at hd; omega
  | horizontal_append_one _ _ _ g2_ih => exact g2_ih hd
  | horizontal_append _ _ _ g1_ih =>
    rw [List.append_assoc, List.length_append] at hd
    exact g1_ih (by omega)
  | vertical_append_one _ _ _ g2_ih => exact g2_ih hd
  | vertical_append _ _ _ g1_ih =>
    rw [List.length_append] at hd
    exact g1_ih (by omega)

open PartialGrid

noncomputable def extend_bottom (h : PartialGrid a b c d e) (a2) (h2 : is_false a2) (h3 : a2 ≠ []) :
    PartialGrid (a2 ++ a) b [] (a2 ++ c ++ d) e := by
  induction h with
  | single_gridt h =>
    cases a2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i d
      have H := PartialGrid.vertical_append_one (PartialGrid.single_gridt h)
        (PartialGrid.empty (head :: tail) (to_over d) (by simp) h2 to_over_len_pos is_true_over)
      rw [List.nil_append] at H
      rw [List.append_nil]
      exact H
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, ← List.append_assoc]
    apply PartialGrid.empty (a2 ++ a) b _ (is_false_of_false_false h2 ha1) (by assumption) hb
    rw [List.length_append]
    omega
  | horizontal_append_one g1 g2 ih1 ih2 =>
    have H := PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos_iff.mpr h3)) ih1 g2
    rw [List.append_nil] at H
    rw [← List.append_assoc]
    exact H
  | horizontal_append h g1 g2 ih1 ih2 =>
    have H := PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos_iff.mpr h3)) ih1 g2
    rw [← List.append_assoc, ← List.append_assoc]
    exact H
  | vertical_append_one g1 g2 ih1 ih2 =>
    have H := PartialGrid.vertical_append_one g1 ih2
    rw [← List.append_assoc]
    exact H
  | vertical_append g1 g2 h ih1 ih2 =>
    have H := PartialGrid.vertical_append g1 ih2 h
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    exact H

noncomputable def extend_side (h : PartialGrid a b c d e) (b2) (h2 : is_true b2) (h3 : b2 ≠ []) :
    PartialGrid a (b ++ b2) c (d ++ e ++ b2) [] := by
  induction h with
  | single_gridt h =>
    cases b2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i c _
      have H := PartialGrid.horizontal_append_one (PartialGrid.single_gridt h)
          (PartialGrid.empty (to_up c) (head :: tail) to_up_len_pos is_false_up (by simp) h2)
      rw [List.append_nil] at H
      rw [List.nil_append]
      exact H
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, List.append_assoc]
    apply PartialGrid.empty a (b ++ b2) ha ha1 _ (is_true_of_true_true hb h2)
    rw [List.length_append]
    omega
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    have H := PartialGrid.horizontal_append_one g1 g2_ih
    rw [← List.append_assoc] at H
    exact H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    have H := PartialGrid.horizontal_append h g1 g2_ih
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at H
    exact H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    have H := PartialGrid.vertical_append g1_ih g2 (by simp; exact Or.inr (List.length_pos_iff.mpr h3))
    rw [← List.append_assoc, ← List.append_assoc, List.append_nil] at H
    rw [← List.append_assoc]
    exact H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    have H := PartialGrid.vertical_append g1_ih g2 (by simp; exact Or.inr (Or.inr (List.length_pos_iff.mpr h3)))
    rw [← List.append_assoc, ← List.append_assoc] at H
    exact H

def middle_spec (d : List (α × Bool)) := PLift (d = []) ⊕ Σ front mid caboose, PLift (d = [(front, false)] ++ mid ++ [(caboose, true)])

def middle_end (d : List (α × Bool)) := PLift (d = []) ⊕ Σ mid caboose, PLift (d = mid ++ [(caboose, true)])

def middle_start (d : List (α × Bool)) := PLift (d = []) ⊕ Σ front mid, PLift (d = [(front, false)] ++ mid)

def middle_start_append (h : middle_start (d1 ++ d2)) : middle_start d1 := by
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

def middle_start_from_spec (h : middle_spec d) : middle_start d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use f, m ++ [(c, true)]
  exact spec

def middle_end_from_spec (h : middle_spec d) : middle_end d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use [(f, false)] ++ m, c
  exact spec

noncomputable def middle_frontier_nil_or_caps (h : PartialGrid a b c d e) : middle_spec d := by
  induction h with
  | single_gridt h =>
    left; exact {down := rfl}
  | empty a b ha ha1 hb hb =>
    right
    generalize hn : a ++ b = n
    induction n using List.reverseRecOn with
    | nil =>
      simp_all
    | append_singleton fn cn _ =>
      cases fn with
      | nil =>
        apply congr_arg List.length at hn
        simp only [List.length_append, List.nil_append, List.length_cons, List.length_nil,
          zero_add] at hn
        omega
      | cons hf td =>
        have H : Σ cb, PLift (cn = (cb, true)) := by
          apply is_true_singleton
          rename_i length_b _
          induction b using List.reverseRecOn with
          | nil => simp at length_b
          | append_singleton front caboose _ =>
            rw [← List.append_assoc] at hn
            apply List.append_singleton_eq_append_singleton at hn
            rw [← hn.2]
            exact (is_true_append hb).2
        have H2 : Σ bb, PLift (hf = (bb, false)) := by
          apply is_false_singleton
          induction a with
          | nil => simp at ha
          | cons front caboose _ =>
            simp only [List.cons_append, List.cons.injEq] at hn
            rw [← hn.1]
            exact (is_false_append ha1).1
        rcases H with ⟨cb, ⟨hcb⟩⟩
        rw [hcb]
        rcases H2 with ⟨hbb, ⟨hhbb⟩⟩
        rw [hhbb]
        use hbb, td, cb
        constructor
        simp
  | horizontal_append_one g1 g2 g1_ih g2_ih => assumption
  | horizontal_append h1 g1 g2 g1_ih g2_ih =>
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
        have H : Σ cb, PLift (c2 = (cb, true)) := is_true_singleton <| (is_true_append (bottom_frontier_is_true g2)).2
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
          exact (is_false_append (right_frontier_is_false g2)).1
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

end PartialGrid

noncomputable def gridt_of_PartialGrid (h : PartialGrid a b d [] c) : gridt_option a b c d := by
  generalize he : ([] : List (Option ℕ × Bool)) = e at h
  induction h with
  | single_gridt h =>
    unfold gridt_option
    simp only [remover_up_rev, remover_over]
    exact gridt_from_cell h
  | empty a b =>
    apply congr_arg List.length at he
    rename_i ha hb
    simp [ha] at he
    linarith
  | horizontal_append_one _ _ ih1 ih2 =>
    exact gridt_option_append_horiz (ih1 rfl) (ih2 he)
  | horizontal_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at he
    have H := gridt_option_append_horiz (g1_ih he.1.symm) (g2_ih he.2.2.symm)
    rw [he.2.1, List.append_nil] at H
    exact H
  | vertical_append_one _ _ ih1 ih2 =>
    exact gridt_option_append_vert (ih1 rfl) (ih2 he)
  | vertical_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at he
    have H := gridt_option_append_vert (g1_ih he.2.2.symm) (g2_ih he.1.symm)
    rw [he.2.1, List.nil_append] at H
    exact H
