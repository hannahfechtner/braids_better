import BraidProject.Grids
import BraidProject.Reversing
import BraidProject.SemiThue

inductive cell : FreeMonoid' ℕ → FreeMonoid' ℕ → FreeMonoid' ℕ → FreeMonoid' ℕ → Prop
  | empty : (cell 1 1 1 1 : Prop)
  | top_bottom (i : ℕ) : cell 1 (FreeMonoid'.of i) 1 (FreeMonoid'.of i)
  | sides (i : ℕ) : cell (FreeMonoid'.of i) 1 (FreeMonoid'.of i) 1
  | top_left (i : ℕ) : cell (FreeMonoid'.of i) (FreeMonoid'.of i) 1 1
  | adjacent (i k : ℕ) (h : Nat.dist i k = 1) : cell (FreeMonoid'.of i) (FreeMonoid'.of k)
      (FreeMonoid'.of i * FreeMonoid'.of k) (FreeMonoid'.of k * FreeMonoid'.of i)
  | separated (i j : ℕ) (h : i +2 ≤ j ∨ j+2 <= i) : cell (FreeMonoid'.of i) (FreeMonoid'.of j)
      (FreeMonoid'.of i) (FreeMonoid'.of j)

theorem grid_from_cell (h : cell a b c d) : grid a b c d := by
  induction h with
  | empty => exact grid.empty
  | top_bottom i => exact grid.top_bottom _
  | sides i => exact grid.sides _
  | top_left i => exact grid.top_left _
  | adjacent i k h => exact grid.adjacent _ _ h
  | separated i j h => exact grid.separated _ _ h

def to_up (a : FreeMonoid' ℕ) : FreeMonoid' (Option ℕ × Bool) := FreeMonoid'.map
  (fun x => (some x, false)) a

def to_over (a : FreeMonoid' ℕ) : FreeMonoid' (Option ℕ × Bool) := FreeMonoid'.map
  (fun x => (some x, true)) a

def remover : (a : FreeMonoid' (Option ℕ × Bool)) → FreeMonoid' ℕ
  | 1 => 1
  | (some a, _) :: c => a :: remover c
  | (none, _) :: c => remover c

theorem remover_mul : remover ((some a, bo) :: b) = .of a * remover b := rfl

theorem remover_none : remover ((none, bo) :: b) = remover b := rfl

theorem remover_split : ∀ b, remover (a * b) = remover a * remover b := by
  induction a using FreeMonoid'.inductionOn'
  · exact fun _ => rfl
  intro b
  rename_i h t ht
  rcases h with a | b
  · change remover (_ :: _) = remover (_ :: _) * _
    rw [remover_none, remover_none]
    exact ht _
  change remover (_ :: _) = remover (_ :: _) * _
  rw [remover_mul, remover_mul]
  rename_i bb _
  simp
  rw [mul_assoc, mul_right_inj]
  exact ht _

@[simp]
theorem up_length : (to_up a).length = a.length := by
  unfold to_up
  induction a using FreeMonoid'.inductionOn'
  · simp only [FreeMonoid'.length_one, map_one, FreeMonoid'.eq_one_of_length_eq_zero]
  simp only [map_mul, FreeMonoid'.map_of, FreeMonoid'.length_mul, FreeMonoid'.length_of,
    add_right_inj]
  assumption

@[simp]
theorem over_length : (to_over a).length = a.length := by
  unfold to_over
  induction a using FreeMonoid'.inductionOn'
  · simp only [FreeMonoid'.length_one, map_one, FreeMonoid'.eq_one_of_length_eq_zero]
  simp only [map_mul, FreeMonoid'.map_of, FreeMonoid'.length_mul, FreeMonoid'.length_of,
    add_right_inj]
  assumption

@[simp]
theorem remover_up : remover (to_up a) = a := by
  induction a using FreeMonoid'.inductionOn'
  · rfl
  rename_i a b hb
  unfold to_up
  simp only [map_mul, FreeMonoid'.map_of]
  change remover (_ :: _) = _
  rw [remover_mul]
  simp only [List.append_eq, List.nil_append, mul_right_inj]
  change remover (to_up _) = _
  rw [hb]

@[simp]
theorem remover_over : remover (to_over a) = a := by
  induction a using FreeMonoid'.inductionOn'
  · rfl
  rename_i a b hb
  unfold to_over
  simp only [map_mul, FreeMonoid'.map_of]
  change remover (_ :: _) = _
  rw [remover_mul]
  simp only [List.append_eq, List.nil_append, mul_right_inj]
  change remover (to_over _) = _
  rw [hb]

def grid_option (a b c d : FreeMonoid' (Option ℕ × Bool)) : Prop := grid (remover a) (remover b)
  (remover c) (remover d)

theorem grid_option_append_horiz (h1 : grid_option a b c d) (h2 : grid_option c e f g) : grid_option a (b * e) f (d * g) := by
  simp [grid_option, remover_split]
  exact grid.horizontal h1 h2

/-- A partial grid generalizes the notion of a grid to include "unfinished" grids. -/
inductive PartialGrid : FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) →
  FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → Prop
  | single_grid {a b c d : FreeMonoid' ℕ} (h : grid a b c d):
      PartialGrid (to_up a) (to_over b) (to_over d) 1 (to_up c)
  | empty (a b : FreeMonoid' ℕ) (ha : a.length > 0) (hb : b.length > 0):
      PartialGrid (to_up a) (to_over b) 1 ((to_up a) * (to_over b)) 1
  | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : grid_option a b up bot)
      (g2 : PartialGrid up b2 bot2 mid2 up2) : PartialGrid a (b*b2) (bot * bot2) mid2 up2
  | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : FreeMonoid' (Option ℕ × Bool)}
      (h : mid.length > 0)
      (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid up b2 bot2 mid2 up2) :
      PartialGrid a (b*b2) bot (mid * bot2 * mid2) up2

theorem grid_of_PartialGrid (h : PartialGrid a b d 1 c) : grid_option a b c d := by
  generalize he : (1 : FreeMonoid' (Option ℕ × Bool)) = e at h
  induction h with
  | single_grid h =>
    unfold grid_option
    simp only [remover_up, remover_over]
    exact h
  | empty a b =>
    exfalso
    apply congr_arg FreeMonoid'.length at he
    rename_i ha hb
    simp [ha, hb] at he
    linarith
  | horizontal_append_one g1 _ ih =>
    specialize ih he
    exact grid_option_append_horiz g1 ih
  | horizontal_append _ _ _ g1_ih g2_ih =>
    rename_i j k l m n o p q r _ _ _
    have h4 := FreeMonoid.prod_eq_one he.symm
    have h5 := FreeMonoid.prod_eq_one h4.1
    have h1 : m = 1 := h5.1
    have h2 : p = 1 := h5.2
    have h3 : q = 1 := h4.2
    specialize g1_ih h1.symm
    specialize g2_ih h3.symm
    have H := grid_option_append_horiz g1_ih g2_ih
    rw [h2, mul_one] at H
    exact H

theorem middle_starts_up (h : PartialGrid a b d mid c) : mid = 1 ∨ ∃ first, mid.get? 0 = some (first, false) := by
  induction h with
  | single_grid _ =>
    left
    rfl
  | empty a b ha _ =>
    right
    induction a using FreeMonoid'.inductionOn'
    · exfalso
      simp only [FreeMonoid'.length_one, gt_iff_lt, lt_self_iff_false] at ha
    rename_i _ h ta _
    use h
    rfl
  | horizontal_append_one _ _ ih =>
    rcases ih with h1 | h2
    · left
      exact h1
    right
    exact h2
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    right
    rcases g1_ih with h1 | h2
    · exfalso
      apply congr_arg FreeMonoid'.length at h1
      simp only [FreeMonoid'.length_one] at h1
      rw [h1] at g1
      exact Nat.not_succ_le_zero 0 g1
    rcases h2 with ⟨firstie, hf⟩
    use firstie
    rw [← hf]
    rename_i mid _ _ _ _ _
    induction mid using FreeMonoid'.inductionOn'
    · change List.get? [] _ = _ at hf
      simp only [List.get?_nil] at hf
    rw [mul_assoc, mul_assoc]
    change List.get? ( _ :: _) _ = List.get? ( _ :: _) _
    rw [List.get?_cons_zero, List.get?_cons_zero]

#exit
theorem rev'_to_grid'' {a b c d : FreeMonoid' ℕ} (h : SemiThue_one_step reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c))) : PartialGrid (to_up a) (to_over b) (to_over d) 1 (to_up c) := by
  have H : ∀ e f, SemiThue_one_step reversing_rels' e f → ∀ a b c d, e = (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
      FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b) → f = (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
      FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c)) → PartialGrid (to_up a) (to_over b) (to_over d) 1 (to_up c) := by
    intro e f hef
    induction hef with
    | refl a =>
      intro a b c d a1 a2
      have H := a1.symm.trans a2
      have H1 : a = 1 ∧ c = 1 ∧ b = d ∨ b = 1 ∧ d = 1 ∧ a = c := by sorry
      rcases H1 with one | two
      · rw [one.1, one.2.1, one.2.2]
        apply PartialGrid.single_grid
        exact grid_top_bottom_word d
      rw [two.1, two.2.1, two.2.2]
      apply PartialGrid.single_grid (grid_sides_word c)
    | one_step h1 h2 ih =>
      intro a1 b1 c1 d1 he h2
      sorry
  apply H
  sorry

#exit
with
    | refl g =>
      intro a b c d a1 a2
      have H := a1.symm.trans a2
      have H1 : a = 1 ∧ c = 1 ∧ b = d ∨ b = 1 ∧ d = 1 ∧ a = c := by sorry
      rcases H1 with one | two
      · rw [one.1, one.2.1, one.2.2]
        apply PartialGrid.single_grid
        exact grid_top_bottom_word d
      rw [two.1, two.2.1, two.2.2]
      apply PartialGrid.single_grid (grid_sides_word c)
    | reg h =>
      rename_i g i
      intro a b c d g_is i_is
      cases h with
      | inverse s =>
        have H : d = 1 ∧ c = 1 ∧ a = b := by
          constructor
          · have H := (FreeMonoid.prod_eq_one i_is.symm).1
            exact FreeMonoid.lift_bool_one H
          constructor
          · have H := (FreeMonoid.prod_eq_one i_is.symm).2
            have H2 : c.reverse = 1 := FreeMonoid.lift_bool_one H
            have H3 := congr_arg FreeMonoid'.reverse H2
            simp only [FreeMonoid'.reverse_reverse, FreeMonoid'.length_one,
              FreeMonoid'.reverse_length, FreeMonoid'.eq_one_of_length_eq_zero] at H3
            exact H3
          sorry
        rw [H.1, H.2.1, H.2.2]
        exact PartialGrid.single_grid <| grid_top_left_word b
      | adjacent i j h =>
        have H : a = FreeMonoid.of i ∧ b = FreeMonoid.of j ∧ d = [j, i] ∧ c = [i, j] := by sorry
        rw [H.1, H.2.1, H.2.2.1, H.2.2.2]
        exact PartialGrid.single_grid <| grid.adjacent _ _ h
      | separated i j h =>
        have H : a = FreeMonoid.of i ∧ b = FreeMonoid.of j ∧ d = FreeMonoid.of j ∧ c = FreeMonoid.of i := by sorry
        rw [H.1, H.2.1, H.2.2.1, H.2.2.2]
        apply PartialGrid.single_grid
        apply grid.separated
        exact or_dist_iff.mp h
    | left g h =>
      rename_i i j k
      induction k using FreeMonoid'.inductionOn'
      · intro a b c d h1 h2
        rw [one_mul] at h1
        rw [one_mul] at h2
        exact h _ _ _ _ h1 h2
      rename_i kh kt ihk
      intro a1 b1 c1 d1 h1 h2
      rcases a1
      · rcases b1
        · sorry
        sorry
      sorry
    | right _ _ => sorry
    | trans h1 h2 h1_ih h2_ih =>
      rename_i i j k
      intro a1 b1 c1 d1
      intro i_is k_is
      --specialize h1_ih a1 b1 _ _ i_is
      sorry
  exact H _ _ h _ _ _ _ rfl rfl
