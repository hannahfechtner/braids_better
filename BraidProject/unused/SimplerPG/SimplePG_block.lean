import BraidProject.Grids_C
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.NewListFacts

@[simp]
theorem List.map_rev_rev : (List.map f (L.reverse)).reverse = List.map f L := by simp only [map_reverse,
  reverse_reverse]

def remove_bool (L : List (α × Bool)) : List α := List.map (fun x => x.1) L

def gridt_option (a b c d : List (ℕ × Bool)) : Type := gridt (remove_bool a.reverse) (remove_bool b)
  (remove_bool c.reverse) (remove_bool d)

theorem remove_bool_append {L1 L2 : List (α × Bool)} : remove_bool (L1 ++ L2) = remove_bool L1 ++ remove_bool L2 := by simp [remove_bool]

def gridt_option_append_horiz (h1 : gridt_option a b c d) (h2 : gridt_option c e f g) : gridt_option a (b ++ e) f (d ++ g) := by
  simp [gridt_option, remove_bool_append]
  exact gridt.horizontal h1 h2

def gridt_option_append_vert {a b c d e f g} (h1 : gridt_option a b c d) (h2 : gridt_option e d f g) : gridt_option (e ++ a) b (f ++ c) g := by
  simp [gridt_option, remove_bool_append]
  exact gridt.vertical h1 h2

def to_up_plain (a : List α) : List (α × Bool) := List.map (fun x => (x, false)) a.reverse

def to_over_plain {α : Type} (a : List α) : List (α × Bool) := List.map (fun x => (x, true)) a

theorem to_over_plain_length : (to_over_plain a).length = a.length := by
  simp [to_over_plain]

theorem to_up_plain_length : (to_up_plain a).length = a.length := by
  simp [to_up_plain]

theorem to_over_plain_nil : to_over_plain ([] : List α) = [] := rfl
theorem to_up_plain_nil : to_up_plain ([] : List α) = [] := rfl

def to_over_plain_is_true : is_true (to_over_plain a) := by
  induction a with
  | nil =>
    exact is_true_nil
  | cons head tail ih =>
    simp [to_over_plain]
    apply is_true_cons
    exact ih

def to_up_plain_is_false : is_false (to_up_plain a) := by
  induction a with
  | nil =>
    exact is_false_nil
  | cons head tail ih =>
    simp [to_up_plain]
    apply is_false_of_false_false
    unfold to_up_plain at ih
    simp only [List.map_reverse] at ih
    exact ih
    intro a ha
    simp at ha
    constructor
    rw [ha.1]
    
theorem remove_bool_to_up_plain : remove_bool (to_up_plain a).reverse = a := by
  simp only [remove_bool, to_up_plain, List.map_reverse, List.reverse_reverse, List.map_map]
  induction a with
  | nil => simp
  | cons head tail ih => simp [ih]

theorem remove_bool_to_over_plain : remove_bool (to_over_plain b) = b := by
  simp only [remove_bool, to_over_plain, List.map_map]
  induction b with
  | nil => simp
  | cons head tail ih => simp [ih]

/-- A partial gridt generalizes the notion of a gridt to include "unfinished" gridts. -/
inductive PartialGrid : List (ℕ × Bool) → List (ℕ × Bool) →
  List (ℕ × Bool) → List (ℕ × Bool) → List (ℕ × Bool) → Type
  | single_gridt (h : cell a b c d): PartialGrid (to_up_plain a) (to_over_plain b) (to_over_plain d) [] (to_up_plain c)
  | empty (a b : List (ℕ × Bool)) (ha : a.length > 0) (ha1 : is_false a)
      (hb : b.length > 0) (hb : is_true b) : PartialGrid a b [] (a ++ b) []
  | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : PartialGrid a b bot [] up)
      (g2 : PartialGrid up b2 bot2 mid2 up2) : PartialGrid a (b ++ b2) (bot ++ bot2) mid2 up2
  | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : List (ℕ × Bool)}
      (h : mid.length > 0)
      (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid up b2 bot2 mid2 up2) :
      PartialGrid a (b ++ b2) bot (mid ++ bot2 ++ mid2) up2
  | vertical_append_one (g1 : PartialGrid a b bot [] up) (g2 : PartialGrid a1 bot bot2 mid2 up2) :
      PartialGrid (a1 ++ a) b bot2 mid2 (up2 ++ up)
  | vertical_append (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid a1 bot bot2 mid2 up2) (h : mid.length > 0) :
      PartialGrid (a1 ++ a) b bot2 (mid2 ++ up2 ++ mid) up

def PartialGrid.length (h : PartialGrid a b c d e) :=
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

noncomputable def gridt_of_PartialGrid (h : PartialGrid a b d [] c) : gridt_option a b c d := by
  generalize he : ([] : List (ℕ × Bool)) = e at h
  induction h with
  | single_gridt h =>
    unfold gridt_option
    simp only [remove_bool_to_up_plain, remove_bool_to_over_plain]
    exact gridt_from_cell h
  | empty a b =>
    exfalso
    apply congr_arg List.length at he
    rename_i ha hb
    simp [ha] at he
    linarith
  | horizontal_append_one _ _ ih1 ih2 =>
    specialize ih1 rfl
    specialize ih2 he
    exact gridt_option_append_horiz ih1 ih2
  | horizontal_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at he
    specialize g1_ih he.1.symm
    specialize g2_ih he.2.2.symm
    have H := gridt_option_append_horiz g1_ih g2_ih
    rw [he.2.1, List.append_nil] at H
    exact H
  | vertical_append_one _ _ ih1 ih2 =>
    specialize ih1 rfl
    specialize ih2 he
    exact gridt_option_append_vert ih1 ih2
  | vertical_append _ _ _ g1_ih g2_ih =>
    simp only [List.append_assoc, List.nil_eq_append_iff, List.append_eq_nil_iff] at he
    specialize g1_ih he.2.2.symm
    specialize g2_ih he.1.symm
    have H := gridt_option_append_vert g1_ih g2_ih
    rw [he.2.1, List.nil_append] at H
    exact H

namespace PartialGrid

noncomputable def right_frontier_is_false (h : PartialGrid a b c d e) : is_false e := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp only [to_up_plain, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.map_cons, List.map_nil]
    any_goals exact is_false_nil
    · intro a ha
      constructor
      simp at ha
      rw [ha.1]
    · intro a ha
      constructor
      simp at ha
      rcases ha.1
      · aesop
      aesop
    intro a ha
    constructor
    simp at ha
    rw [ha.1]
  | empty => exact is_false_nil
  | horizontal_append_one => assumption
  | horizontal_append => assumption
  | vertical_append_one _ _ g1_ih g2_ih =>
    exact is_false_of_false_false g2_ih g1_ih
  | vertical_append => assumption


noncomputable def  top_frontier_is_true (h : PartialGrid a b c d e) : is_true b := by
  induction h with
  | single_gridt h =>
      cases h
      all_goals simp only [to_over_plain, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.map_cons, List.map_nil]
      any_goals exact is_true_nil
      any_goals
        intro a ha
        constructor
        simp at ha
        rw [ha.1]
  | empty  => assumption
  | horizontal_append_one _ _ g1_ih g2_ih => exact is_true_of_true_true g1_ih g2_ih
  | horizontal_append _ _ _ g1_ih g2_ih => exact is_true_of_true_true g1_ih g2_ih
  | vertical_append_one => assumption
  | vertical_append => assumption

noncomputable def left_frontier_is_false (h : PartialGrid a b c d e) : is_false a := by
  induction h with
    | single_gridt h =>
      cases h
      all_goals simp only [to_up_plain, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.map_cons, List.map_nil]
      any_goals exact is_false_nil
      all_goals
        intro a ha
        constructor
        simp at ha
        rw [ha.1]
    | empty => assumption
    | horizontal_append_one => assumption
    | horizontal_append => assumption
    | vertical_append_one _ _ g1_ih g2_ih =>
      exact is_false_of_false_false g2_ih g1_ih
    | vertical_append _ _ _ ih1 ih2 => exact is_false_of_false_false ih2 ih1

noncomputable def bottom_frontier_is_true (h : PartialGrid a b c d e) : is_true c := by
  induction h with
    | single_gridt h =>
      cases h
      all_goals simp only [to_over_plain, List.nil_append,
        List.cons_append, List.map_cons, List.map_nil]
      any_goals exact is_true_nil
      any_goals
        intro a ha
        constructor
        simp at ha
        rw [ha.1]
      intro a ha
      constructor
      simp at ha
      rcases ha.1
      · aesop
      aesop
    | empty => exact is_true_nil
    | horizontal_append_one => exact is_true_of_true_true (by assumption) (by assumption)
    | horizontal_append => assumption
    | vertical_append_one => assumption
    | vertical_append => assumption


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
