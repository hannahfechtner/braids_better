import BraidProject.Grids
import BraidProject.StepOne
import BraidProject.SemiThue

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

def to_up (a : List ℕ) : List (Option ℕ × Bool) :=
  match a with
  | [] => [(none, false)]
  | _ => List.map (fun x => (some x, false)) a.reverse

def to_over (a : List ℕ) : List (Option ℕ × Bool) :=
  match a with
  | [] => [(none, true)]
  | _ => List.map (fun x => (some x, true)) a

def remover : (a : List (Option ℕ × Bool)) → List ℕ
  | [] => []
  | (some a, _) :: c => a :: remover c
  | (none, _) :: c => remover c

@[simp]
theorem to_up_nil : to_up [] = [(none, false)] := rfl

@[simp]
theorem to_up_singleton (a : ℕ) : to_up [a] = [(some a, false)] := rfl

@[simp]
theorem to_up_pair (a : ℕ) : to_up [a, b] = [(some b, false), (some a, false)] := rfl

@[simp]
theorem to_up_cons_cons : to_up (a :: b :: c) = to_up (b :: c) ++ [(some a, false)] := by
  simp [to_up]

theorem to_up_len_pos : (to_up a).length > 0 := by
  induction a
  · simp
  rename_i h t ht
  simp
  cases t
  · simp
  simp

@[simp]
theorem to_over_nil : to_over [] = [(none, true)] := rfl

@[simp]
theorem to_over_singleton (a : ℕ) : to_over [a] = [(some a, true)] := rfl

@[simp]
theorem to_over_pair (a : ℕ) : to_over [a, b] = [(some a, true), (some b, true)] := rfl

@[simp]
theorem to_over_cons_cons : to_over (a :: b :: c) = (some a, true) :: to_over (b :: c):= by
  simp [to_over]

theorem to_over_len_pos : (to_over a).length > 0 := by
  induction a
  · simp
  rename_i h t ht
  simp
  cases t
  · simp
  simp

theorem to_over_eq_cons (c) : ∃ a b, to_over c = (a, true) :: b := by
  induction c
  · use none, []
    rfl
  rename_i h t ht
  cases t
  · use some h, []
    rfl
  simp

theorem to_over_options (c) : (∃ a, to_over c = [(a, true)]) ∨ ∃ a b, to_over c = (some a, true) :: (to_over b) := by
  induction c
  · simp
  rename_i h t ht
  cases t
  · simp
  simp

theorem remover_mul : remover ((some a, bo) :: b) = a :: remover b := rfl

theorem remover_none : remover ((none, bo) :: b) = remover b := rfl

theorem remover_split : ∀ b, remover (a ++ b) = remover a ++ remover b := by
  induction a
  · exact fun _ => rfl
  intro b
  rename_i h t ht
  rcases h with a | b
  · change remover (_ :: _) = remover (_ :: _) ++ _
    rw [remover_none, remover_none]
    exact ht _
  change remover (_ :: _) = remover (_ :: _) ++ _
  rw [remover_mul, remover_mul]
  rename_i bb _
  simp only [List.append_eq, List.cons_append, List.cons.injEq, true_and]
  exact ht _

@[simp]
theorem remover_up : remover (to_up a) = a.reverse := by
  induction a
  · rfl
  rename_i a b hb
  unfold to_up
  simp only [List.reverse_cons, List.map_append, List.map_reverse, List.map_cons, List.map_nil]
  rw [remover_split]
  cases b with
  | nil =>
    simp [remover, List.nil_append]
  | cons head tail =>
    simp [remover]
    simp [remover, to_up] at hb
    rw [hb]
    simp

@[simp]
theorem List.map_rev_rev : (List.map f (L.reverse)).reverse = List.map f L := by induction L with
  | nil => rfl
  | cons h t ih => simp [List.reverse_cons, ih]
@[simp]
theorem remover_up_rev : remover (to_up a).reverse = a := by
  unfold remover
  unfold to_up
  induction a
  · simp [remover]
  rename_i tail ih
  cases tail
  · simp [remover]
  simp
  simp at ih
  rename_i head tailly
  rw [remover_mul]
  simp
  exact ih

@[simp]
theorem remover_over : remover (to_over a) = a := by
  induction a
  · rfl
  rename_i a b hb
  unfold to_over
  simp
  rw [remover_mul]
  simp only [List.cons.injEq, true_and]
  cases b with
  | nil =>
    simp [remover]
  | cons head tail =>
    exact hb

def grid_option (a b c d : List (Option ℕ × Bool)) : Prop := grid (remover a.reverse) (remover b)
  (remover c.reverse) (remover d)

theorem grid_option_append_horiz (h1 : grid_option a b c d) (h2 : grid_option c e f g) : grid_option a (b ++ e) f (d ++ g) := by
  simp [grid_option, remover_split]
  exact grid.horizontal h1 h2

theorem grid_option_append_vert (h1 : grid_option a b c d) (h2 : grid_option e d f g) : grid_option (e ++ a) b (f ++ c) g := by
  simp [grid_option, remover_split]
  exact grid.vertical h1 h2

def is_false (a : List (Option ℕ × Bool)) := ∀ x ∈ a, x.2 = false

@[simp]
theorem is_false_nil : is_false [] := by simp [is_false]


theorem is_false_up : is_false (to_up a) := by
  unfold to_up
  cases a with
  | nil =>
    simp [is_false]
  | cons head tail =>
    simp [is_false]

theorem is_false_append (h : is_false (a ++ b)) : is_false a ∧ is_false b := by
  constructor
  · exact fun x hx => h x (List.mem_append_left b hx)
  exact fun x hx => h x (List.mem_append_right a hx)
def is_true (a : List (Option ℕ × Bool)) := ∀ x ∈ a, x.2 = true

theorem is_false_of_false_false (h1 : is_false a) (h2 : is_false b) : is_false (a ++ b) := by
  intro x h
  simp at h
  cases h with
  | inl h => exact h1 x h
  | inr h => exact h2 x h

theorem is_true_over : is_true (to_over a) := by
  unfold to_over
  cases a with
  | nil =>
    simp [is_true]
  | cons head tail =>
    simp [is_true]

@[simp]
theorem is_true_nil : is_true [] := by simp [is_true]

theorem is_true_append (h : is_true (a ++ b)) : is_true a ∧ is_true b := by
  constructor
  · exact fun x hx => h x (List.mem_append_left b hx)
  exact fun x hx => h x (List.mem_append_right a hx)

theorem is_true_of_true_true (h1 : is_true a) (h2 : is_true b) : is_true (a ++ b) := by
  intro x h
  simp at h
  cases h with
  | inl h => exact h1 x h
  | inr h => exact h2 x h

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

theorem grid_style_split (h : grid_style' i j) : ∃ a b, i = [(a, false), (b, true)] := by
  induction h with
  | basic =>
    rename_i n
    use n, n
  | over =>
    rename_i n
    use n, none
  | up =>
    rename_i n
    use none, n
  | empty =>
    use none, none
  | apart h =>
    rename_i i j
    use i, j
  | close h =>
    rename_i i j
    use i, j

theorem List.append_eq_len_two (h1 : a.length > 0) (h2 : b.length > 0) (h3 : a ++ b = [c, d]) : a = [c] ∧ b = [d] := by
    have H : ¬ a.length > 1 := by
      intro h
      apply congr_arg List.length at h3
      simp at h3
      omega
    exact append_inj h3 (Nat.le_antisymm h1 (Nat.le_of_not_lt H)).symm

namespace PartialGrid
theorem right_frontier_is_false (h : PartialGrid a b c d e) : is_false e := by
  induction h with
  | single_grid  => exact is_false_up
  | empty => simp
  | horizontal_append_one => assumption
  | horizontal_append => assumption
  | vertical_append_one _ _ g1_ih g2_ih =>
    exact is_false_of_false_false g2_ih g1_ih
  | vertical_append => assumption

theorem top_frontier_is_true (h : PartialGrid a b c d e) : is_true b := by
  induction h with
  | single_grid => exact is_true_over
  | empty  => assumption
  | horizontal_append_one _ _ g1_ih g2_ih => exact is_true_of_true_true g1_ih g2_ih
  | horizontal_append _ _ _ g1_ih g2_ih => exact is_true_of_true_true g1_ih g2_ih
  | vertical_append_one => assumption
  | vertical_append => assumption

theorem left_frontier_is_false (h : PartialGrid a b c d e) : is_false a := by
  induction h with
    | single_grid => exact is_false_up
    | empty => assumption
    | horizontal_append_one => assumption
    | horizontal_append => assumption
    | vertical_append_one _ _ g1_ih g2_ih =>
      exact is_false_of_false_false g2_ih g1_ih
    | vertical_append _ _ _ ih1 ih2 => exact is_false_of_false_false ih2 ih1

theorem bottom_frontier_is_true (h : PartialGrid a b c d e) : is_true c := by
  induction h with
    | single_grid => exact is_true_over
    | empty => simp
    | horizontal_append_one => exact is_true_of_true_true (by assumption) (by assumption)
    | horizontal_append => assumption
    | vertical_append_one => assumption
    | vertical_append => assumption

theorem left_length_pos (h : PartialGrid a b c d e) : a.length > 0 := by
  induction h with
  | single_grid  => exact to_up_len_pos
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
  | single_grid => exact to_over_len_pos
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
  | single_grid => simp at hd
  | empty => rw [List.length_append] at hd; omega
  | horizontal_append_one _ _ _ g2_ih => exact g2_ih hd
  | horizontal_append _ _ _ g1_ih =>
    rw [List.append_assoc, List.length_append] at hd
    exact g1_ih (by omega)
  | vertical_append_one _ _ _ g2_ih => exact g2_ih hd
  | vertical_append _ _ _ g1_ih =>
    rw [List.length_append] at hd
    exact g1_ih (by omega)

-- theorem equiv_paths (h : PartialGrid a b c d e) : SemiThue_one_step grid_style' (a ++ b) (c ++ d ++ e) := by
--   induction h with
--   | single_grid h =>
--     cases h with
--     | empty =>
--       simp
--       apply one_step_equiv_reg.mp
--       sorry
--     | top_bottom i => sorry
--     | sides i => sorry
--     | top_left i => sorry
--     | adjacent i k h => sorry
--     | separated i j h => sorry
--   | empty a b ha ha1 hb hb =>
--     simp
--     exact SemiThue_one_step.refl _
--   | horizontal_append_one g1 g2 g1_ih g2_ih =>
--     simp at g1_ih
--     simp at g2_ih
--     sorry
--   | horizontal_append h g1 g2 g1_ih g2_ih => sorry
--   | vertical_append_one g1 g2 g1_ih g2_ih => sorry
--   | vertical_append g1 g2 h g1_ih g2_ih => sorry

end PartialGrid

theorem over_up_neq_false_true (h : to_over d ++ to_up c = k ++ [(a1, false), (b1, true)] ++ l) : False := by
  induction k generalizing d with
  | nil =>
    rw [List.nil_append] at h
    have H : List.get? (to_over d ++ to_up c) 0 = List.get? ([(a1, false), (b1, true)] ++ l) 0 := by
      rw [h]
    rcases to_over_eq_cons d with ⟨w, w2, hw⟩
    rw [hw] at H
    simp at H
  | cons head tail ih =>
    rcases to_over_options d with h1 | h2
    · rcases h1 with ⟨a3, h3⟩
      rw [h3] at h
      simp at h
      have H : is_false (tail ++ (a1, false) :: (b1, true) :: l) := by
        rw [← h.2]
        exact is_false_up
      have b1_in : (b1, true) ∈ tail ++ (a1, false) :: (b1, true) :: l  := by
        simp
      have H2 := H (b1, true) b1_in
      simp at H2
    rcases h2 with ⟨a3, b3, h3⟩
    rw [h3] at h
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.cons.injEq] at h
    simp only [List.append_assoc, List.cons_append, List.singleton_append, imp_false] at ih
    exact ih h.2

theorem List.append_singleton_eq_append_singleton (h : a ++ [b] = c ++ [d]) : a = c ∧ b = d := by
  induction a generalizing c with
  | nil =>
    have h2 := congr_arg List.length h
    simp at h2
    rw [h2] at h
    simp at h
    exact ⟨h2.symm, h⟩
  | cons head tail ih =>
    cases c with
    | nil =>
      exfalso
      have h2 := congr_arg List.length h
      simp at h2
    | cons head2 tail2 =>
      simp at h
      specialize ih h.2
      rw [h.1, ih.1]
      exact ⟨rfl, ih.2⟩

theorem List.length_geq_one_eq_cons_cons (b) (h : a ++ b = c :: d :: e) (h2 : a.length > 1) : ∃ f, a = c :: d :: f := by
  induction e using List.reverseRecOn generalizing b with
  | nil =>
    use []
    have H : a.length = 2 := by
      apply congr_arg List.length at h
      simp only [length_append, length_cons, length_singleton, Nat.succ_eq_add_one,
        Nat.reduceAdd, List.length_nil] at h
      omega
    exact append_inj_left h H
  | append_singleton front caboose ih =>
    induction b using List.reverseRecOn with
    | nil =>
      use front ++ [caboose]
      rw [List.append_nil] at h
      exact h
    | append_singleton head tail =>
      apply ih head
      rw [← List.append_assoc] at h
      change (a++head) ++ [tail] = (c :: d :: front) ++ [caboose] at h
      exact (List.append_singleton_eq_append_singleton h).1

theorem over_up_splits_at_i (h1 : is_false a) (h2 : is_true b) (h3 : a.length > 0)
      (h5 : a ++ b = k ++ ([(a3, false), (b3, true)] ++ l)) : ∃ a1 a2 b1 b2, a = a1 ++ a2 ∧ b = b1 ++ b2 ∧
      [(a3, false), (b3, true)] = a2 ++ b1 ∧ a1 = k ∧ b2 = l := by
  induction k generalizing a with
  | nil =>
    use [], [(a3, false)], [(b3, true)], l
    simp at h5
    simp
    have H : a.length = 1 := by
      have H : ¬ a.length > 1 := by
        intro h
        rcases List.length_geq_one_eq_cons_cons _ h5 h with ⟨f, hf⟩
        rw [hf] at h1
        simp [is_false] at h1
      omega
    exact List.append_inj h5 H
  | cons head tail ih =>
    cases a with
    | nil => simp at h3
    | cons heada taila =>
      simp at h5
      cases taila with
      | nil =>
        use [], [heada]
        simp
        rw [List.nil_append] at h5
        rw [h5.2] at h2
        specialize h2 (a3, false)
        have H : (a3, false).2 = true := by
          apply h2
          apply List.mem_append_right tail
          exact List.mem_cons_self (a3, false) ((b3, true) :: l)
        exact (Bool.eq_not_self (a3, false).2).mp H
      | cons headaa tailaa =>
        have H1 : is_false (headaa :: tailaa) := fun x hx => h1 _ <| List.mem_cons_of_mem heada hx
        specialize ih H1 (by simp) h5.2
        rcases ih with ⟨a1', a2', b1', b2', f1, f2, f3, f4, f5⟩
        use heada :: a1', a2', b1', b2'
        exact ⟨by rw [f1]; rfl, ⟨f2, ⟨f3, ⟨by rw [f4, h5.1], f5⟩⟩⟩⟩

def option_to_cell (a : Option ℕ) : List ℕ :=
  match a with
  | none => []
  | some b => [b]

theorem over_oc : to_over (option_to_cell b1) = [(b1, true)] := by
  cases b1 with
  | none => rfl
  | some val => rfl

theorem up_oc : to_up (option_to_cell a1) = [(a1, false)] := by
  cases a1 with
  | none => rfl
  | some val => rfl

theorem grid_rel_means (h : grid_style' i j) : ∃ a b c d, i = [(a, false), (b, true)] ∧
    cell (option_to_cell a) (option_to_cell b) c d ∧ j = to_over d ++ to_up c := by
  cases h with
  | basic n =>
    use some n, some n, [], []
    exact ⟨rfl, ⟨cell.top_left n, rfl⟩⟩
  | over n =>
    use some n, none, [n], []
    exact ⟨rfl, ⟨cell.sides n, rfl⟩⟩
  | up n =>
    use none, some n, [], [n]
    exact ⟨rfl, ⟨cell.top_bottom n, rfl⟩⟩
  | empty =>
    use none, none, [], []
    exact ⟨rfl, ⟨cell.empty, rfl⟩⟩
  | apart h =>
    rename_i i j
    use some i, some j, [i], [j]
    exact ⟨rfl, ⟨cell.separated i j (or_dist_iff.mp h), rfl⟩⟩
  | close h =>
    rename_i i j
    use some i, some j, [i, j], [j, i]
    exact ⟨rfl, ⟨cell.adjacent i j h, rfl⟩⟩

theorem skeleton_one_one (h : grid_style' i j) (ha : a.length > 0) (hb : b.length > 0)
    (i_is : i = [(a3, false), (b3, true)]) (ab : [(a3, false), (b3, true)] = a ++ b) :
    ∃ bot mid up, PartialGrid a b bot mid up ∧ bot ++ mid ++ up = j := by
  rcases grid_rel_means h with ⟨a1, b1, c1, d1, i_is', h_cell, j_is⟩
  use to_over d1, [], to_up c1
  have ab_is := List.append_eq_len_two ha hb ab.symm
  rw [ab_is.1, ab_is.2]
  change _ = [(a3, false)] ++ [(b3, true)] at i_is
  rw [i_is'] at i_is
  have happ := List.append_eq_len_two (by simp) (by simp) i_is.symm
  rw [happ.1, happ.2]
  constructor
  · rw [← over_oc, ← up_oc]
    exact PartialGrid.single_grid h_cell
  rw [List.append_nil]
  exact j_is.symm

theorem grid_style'_includes_true (h : grid_style' i j) : (∀ (a : Option ℕ), (a, true) ∉ i) → False := by
  rcases grid_rel_means h with ⟨a1, b1, c1, d1, i_is, _⟩
  intro h
  specialize h b1
  rw [i_is] at h
  simp at h

theorem bool_change_second (h : a.length > 0) (h1 : is_false a) (h3 : a ++ b = [(a1, false), (b1, true)]) :
    a = [(a1, false)]  := by
  have H : a.length = 1 := by
    have h2 : ¬ a.length > 2 := by
        intro h
        apply congr_arg List.length at h3
        simp at h3
        omega
    have H : ¬ a.length = 2 := by
      intro h
      have H : b = [] := by
        apply congr_arg List.length at h3
        simp only [List.length_append, List.length_cons, List.length_singleton, Nat.succ_eq_add_one,
          Nat.reduceAdd] at h3
        rw [h] at h3
        exact List.length_eq_zero.mp (Nat.add_eq_left.mp h3)
      rw [H, List.append_nil] at h3
      rw [h3] at h1
      simp only [is_false, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq,
        Bool.true_eq_false, and_false, List.not_mem_nil, false_implies, implies_true, and_true,
        and_false] at h1
    omega
  change a ++ b = [(a1, false)] ++ [(b1, true)] at h3
  exact (List.append_inj_left h3.symm H.symm).symm

theorem bool_change_first (h : b.length > 0) (h1 : is_true b) (h3 : a ++ b = [(a1, false), (b1, true)]) :
    b = [(b1, true)]  := by
  have H : b.length = 1 := by
    have h2 : ¬ b.length > 2 := by
        intro h
        apply congr_arg List.length at h3
        simp at h3
        omega
    have H : ¬ b.length = 2 := by
      intro h
      have H : a = [] := by
        apply congr_arg List.length at h3
        simp only [List.length_append, List.length_cons, List.length_singleton, Nat.succ_eq_add_one,
          Nat.reduceAdd] at h3
        rw [h] at h3
        simp only [List.length_nil, zero_add, Nat.reduceAdd, add_left_eq_self,
          List.length_eq_zero] at h3
        exact h3
      rw [H, List.nil_append] at h3
      rw [h3] at h1
      simp [is_true] at h1
    omega
  change a ++ b = [(a1, false)] ++ [(b1, true)] at h3
  exact (List.append_inj_right' h3.symm H.symm).symm

theorem skeleton_one_cons (h2 : grid_style' i j) (fe : a ++ b = ([(a3, false), (b3, true)] ++ head :: tail))
    (b_is : b = b1 ++ head :: tail) (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b)
    (ab_is : [(a3, false), (b3, true)] = a ++ b1) (i_is : i = [(a3, false), (b3, true)]):
    ∃ bot mid up, PartialGrid a b bot mid up ∧ bot ++ mid ++ up = [] ++ j ++ head :: tail := by
  have ht_true : is_true (head :: tail) := by
    rw [b_is] at hb
    exact (is_true_append hb).2
  rcases grid_rel_means h2 with ⟨a2, b2, c2, d2, i_is', h_cell, j_is⟩
  use to_over d2, to_up c2 ++ head :: tail, []
  constructor
  · have H2 := PartialGrid.empty (to_up c2) (head :: tail) (by simp [to_up_len_pos]) is_false_up (by simp) ht_true
    have H3 := PartialGrid.horizontal_append_one (PartialGrid.single_grid h_cell) H2
    simp only [up_oc, over_oc, List.singleton_append, List.append_nil] at H3
    have helper := i_is.symm.trans i_is'
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at helper
    have ha : a = [(a2, false)] := by
      rw [← helper.1]
      exact bool_change_second ha1 ha ab_is.symm
    have hb : b = (b2, true) :: head :: tail := by
      rw [← helper.2]
      rw [ha] at fe
      simp only [List.singleton_append, List.cons_append, List.cons.injEq, Prod.mk.injEq,
        and_true] at fe
      exact fe.2
    rw [ha, hb]
    exact H3
  rw [j_is]
  simp

theorem skeleton_cons_one (h2 : grid_style' i j) (a_is : a = head :: tail ++ a2)
    (ha : is_false a) (hb : is_true b) (ab_is : [(a3, false), (b3, true)] = a2 ++ b1)
    (i_is : i = [(a3, false), (b3, true)]) (b_is : b = b1) (hb1 : b.length > 0) :
    ∃ bot mid up, PartialGrid a b bot mid up ∧ bot ++ mid ++ up = head :: tail ++ j ++ [] := by
  rcases grid_rel_means h2 with ⟨a5, b2, c2, d2, i_is', h_cell, j_is⟩
  have ht_false : is_false (head :: tail) := by
    rw [a_is] at ha
    exact (is_false_append ha).1
  have H2 := PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos]) ht_false (by simp [to_over_len_pos]) is_true_over
  have H3 := PartialGrid.vertical_append_one (PartialGrid.single_grid h_cell) H2
  use [], head::tail ++ to_over d2, to_up c2
  constructor
  · rw [a_is]
    have H := i_is.symm.trans i_is'
    simp at H
    rw [List.nil_append, up_oc, over_oc, ← H.1, ← H.2] at H3
    have H2 : b = [(b3, true)] := by
      rw [b_is]
      rw [b_is] at hb1
      rw [b_is] at hb
      exact bool_change_first hb1 hb ab_is.symm
    have H1 : a2 = [(a3, false)] := by
      rw [← b_is, ← H2] at ab_is
      change [(a3, false)] ++ b = _ ++ b at ab_is
      exact (List.append_cancel_right ab_is).symm
    rw [H1, H2]
    exact H3
  rw [j_is]
  simp

theorem bool_split (ha : is_false a2) (hb : is_true b1) (h : [(a3, false), (b3, true)] = a2 ++ b1) :
    a2 = [(a3, false)] ∧ b1 = [(b3, true)] := by
  have H : a2.length = 1 := by
    have H1 : ¬ a2.length = 0 := by
      intro h1
      simp at h1
      rw [h1, List.nil_append] at h
      rw [← h] at hb
      simp [is_true] at hb
    have H2 : ¬ a2.length = 2 := by
      intro h1
      have h2 := congr_arg List.length h
      simp only [List.length_cons, List.length_singleton, Nat.succ_eq_add_one, Nat.reduceAdd,
        List.length_append] at h2
      rw [h1] at h2
      simp at h2
      rw [h2, List.append_nil] at h
      rw [← h] at ha
      simp [is_false] at ha
    have H3 : ¬ a2.length > 2 := by
      intro h1
      apply congr_arg List.length at h
      simp only [List.length_cons, List.length_singleton, Nat.succ_eq_add_one, Nat.reduceAdd,
        List.length_append, List.length_nil, zero_add, Nat.reduceAdd] at h
      omega
    omega
  exact List.append_inj h.symm H

theorem skeleton_cons_cons (gs : grid_style' i j) (ha : is_false (head :: tail)) (hb : is_true (headb :: tailb))
    (i_is : i = [(a3, false), (b3, true)]) :
    ∃ bot mid up, PartialGrid (head :: tail ++ [(a3, false)]) ([(b3, true)] ++ headb :: tailb) bot mid up ∧
    bot ++ mid ++ up = head :: tail ++ j ++ headb :: tailb := by
  rcases grid_rel_means gs with ⟨a5, b2, c2, d2, i_is', h_cell, j_is⟩
  use [], head :: tail ++ to_over d2 ++ to_up c2 ++ headb :: tailb, []
  constructor
  · have H2 := PartialGrid.empty (head :: tail) (to_over d2) (by simp) ha (by simp [to_over_len_pos]) is_true_over
    have H3 := PartialGrid.vertical_append_one (PartialGrid.single_grid h_cell) H2
    have H4 := PartialGrid.empty (to_up c2) (headb :: tailb) to_up_len_pos is_false_up (by simp) hb
    have H5 := PartialGrid.horizontal_append (by simp) H3 H4
    rw [List.append_nil] at H5
    have hi := i_is.symm.trans i_is'
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hi
    rw [← hi.1, up_oc, ← hi.2, over_oc] at H5
    simp only [List.cons_append, List.singleton_append, List.append_assoc]
    simp only [List.cons_append, List.singleton_append, List.append_assoc] at H5
    exact H5
  simp [j_is]

theorem big_split (hup2 : is_false up2)
    (h : bot3 ++ mid3 ++ (up3 ++ up2) = k ++ [(a1, false), (b1, true)] ++ l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ bot3 ++ mid3 ++ up3 = k ++ [(a1, false), (b1, true)] ++ l₁ ∧
    l₂ = up2 := by
  induction l using List.reverseRecOn generalizing up2 with
  | nil =>
    use [], []
    have H : up2 = [] := by
      induction up2 using List.reverseRecOn with
      | nil => rfl
      | append_singleton l e _ =>
        have h3 := congr_arg List.getLast? h
        rw [← List.append_assoc, ← List.append_assoc, List.getLast?_concat, List.append_nil,
          List.getLast?_append_cons, List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at h3
        rw [h3] at hup2
        specialize hup2 (b1, true) (List.mem_append_right l (List.mem_singleton.mpr rfl))
        simp at hup2
    rw [H] at h
    constructor
    · rfl
    constructor
    · simp at h
      simp
      exact h
    exact H.symm
  | append_singleton front caboose ih =>
    induction up2 using List.reverseRecOn with
    | nil =>
      simp at h
      use front ++ [caboose], []
      constructor
      · simp
      simp [h]
    | append_singleton up2front up2back _ =>
      specialize @ih up2front (is_false_append hup2).1
      rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at h
      have h1 := List.append_inj_left' h rfl
      rw [h1] at h
      simp at h1
      simp at ih
      specialize ih h1
      rcases ih with ⟨l₁, hl1, hl2⟩
      use l₁, up2front ++ [caboose]
      constructor
      · rw [hl1]
        exact List.append_assoc l₁ up2front [caboose]
      constructor
      · simp [hl2]
      simp
      simp at h
      exact h.symm

theorem big_split_first (hbot2 : is_true bot2) (h : bot2 ++ bot3 ++ mid3 ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
    : ∃ k₁ k₂, k = k₁ ++ k₂ ∧ bot3 ++ mid3 ++ up3 = k₂ ++ [(a1, false), (b1, true)] ++ l
    ∧ k₁ = bot2  := by
  induction k generalizing bot2 with
  | nil =>
    use [], []
    constructor
    · rfl
    have H : bot2 = [] := by
      induction bot2 with
      | nil => rfl
      | cons head tail _ =>
        simp at h
        rw [h.1] at hbot2
        simp [is_true]  at hbot2
    rw [H, List.nil_append] at h
    constructor
    · simp [h]
    exact H.symm
  | cons head tail ih =>
    cases bot2 with
    | nil =>
      use [], head:: tail
      rw [List.nil_append] at h
      exact ⟨rfl, ⟨h, rfl⟩⟩
    | cons headb tailb =>
      change is_true ([headb] ++ tailb) at hbot2
      simp at h
      simp at ih
      specialize @ih tailb (is_true_append hbot2).2 h.2
      rcases ih with ⟨k₁, k₂, k_is, front, back⟩
      use head :: k₁, k₂
      constructor
      · rw [k_is]
        rfl
      constructor
      · simp [front]
      rw [back, h.1]
