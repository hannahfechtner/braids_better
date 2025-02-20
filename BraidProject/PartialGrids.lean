import BraidProject.Grids
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
