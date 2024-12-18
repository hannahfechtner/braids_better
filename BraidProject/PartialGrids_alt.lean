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

def to_up' (a : List ℕ) : FreeMonoid' (Option ℕ × Bool) :=
 match a with
 | [] => FreeMonoid'.of (none, false)
 | _ => FreeMonoid'.map (fun x => (some x, false)) a.reverse

def to_over' (a : List ℕ) : FreeMonoid' (Option ℕ × Bool) :=
  match a with
  | [] => FreeMonoid'.of (none, true)
  | _ => FreeMonoid'.map (fun x => (some x, true)) a

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

@[simp]
theorem remover_up' : remover (to_up' a) = a.reverse := by
  induction a using FreeMonoid'.inductionOn'
  · rfl
  exact remover_up

theorem FreeMonoid'.map_mul : FreeMonoid.map f (a * b) = FreeMonoid.map f a * FreeMonoid.map f b := List.map_append f a b

theorem to_up'_triple {a b : ℕ} : to_up' (a::(b::c)) =  to_up' (b :: c) * to_up' [a] := by
  unfold to_up'
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.reverse_nil,
    List.nil_append]
  change FreeMonoid'.map _ (_ * _) = FreeMonoid'.map _ (_ * _) * _
  rw [map_mul, map_mul, mul_assoc, mul_right_inj]
  rfl


theorem remover_up'_rev : remover (to_up' i).reverse = i := by
  induction i with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil => rfl
    | cons h1 t1  =>
      rw [to_up'_triple, FreeMonoid'.reverse_mul, remover_split, ih]
      unfold to_up'
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rfl

-- theorem remover_up'_rev' : remover (to_up' a).reverse = a := by
--   induction a using FreeMonoid'.inductionOn'
--   · rfl
--   rename_i head tail ih
--   induction tail using FreeMonoid'.inductionOn'
--   · rfl
--   sorry

@[simp]
theorem remover_over' : remover (to_over' a) = a := by
  induction a using FreeMonoid'.inductionOn'
  · rfl
  exact remover_over

theorem grid_option_append_horiz (h1 : grid_option a b c d) (h2 : grid_option c e f g) : grid_option a (b * e) f (d * g) := by
  simp [grid_option, remover_split]
  exact grid.horizontal h1 h2

theorem grid_option_append_vert (h1 : grid_option a b c d) (h2 : grid_option e d f g) : grid_option (a * e) b (c * f) g := by
  simp [grid_option, remover_split]
  exact grid.vertical h1 h2

-- inductive PartialGrid : FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) →
--   FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → Prop
--   | single_grid {a b c d : FreeMonoid' ℕ} (h : grid a b c d):
--       PartialGrid (to_up a) (to_over b) (to_over d) 1 (to_up c)
--   | empty_both :
--       PartialGrid (FreeMonoid'.of (none, false)) (FreeMonoid.of (none, true)) 1
--         ((FreeMonoid'.of (none, false)) * (FreeMonoid'.of (none, true))) 1
--   | empty_side (a : FreeMonoid' ℕ) (h : a.length > 0) :
--       PartialGrid (to_up a) (FreeMonoid.of (none, true)) 1
--         ((to_up a) * (FreeMonoid'.of (none, true))) 1
--   | empty (a b : FreeMonoid' ℕ) (h : a.length >0 ∧ b.length > 0):
--       PartialGrid (to_up a) (to_over b) 1 ((to_up a) * (to_over b)) 1
--   | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : grid_option a b up bot)
--       (g2 : PartialGrid up b2 bot2 mid2 up2) : PartialGrid a (b*b2) (bot * bot2) mid2 up2
--   | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : FreeMonoid' (Option ℕ × Bool)}
--       (h : mid.length > 0)
--       (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid up b2 bot2 mid2 up2) :
--       PartialGrid a (b*b2) bot (mid * bot2 * mid2) up2

/-- A partial grid generalizes the notion of a grid to include "unfinished" grids. -/
inductive PartialGrid' : FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) →
  FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → Prop
  | single_grid {a b c d : FreeMonoid' ℕ} (h : grid a b c d):
      PartialGrid' (to_up' a) (to_over' b) (to_over' d) 1 (to_up' c)
  | empty (a b : FreeMonoid' ℕ):
      PartialGrid' (to_up' a) (to_over' b) 1 ((to_up' a) * (to_over' b)) 1
  | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : grid a b up bot)
      (g2 : PartialGrid' (to_up' up) b2 bot2 mid2 up2) : PartialGrid' (to_up' a) ((to_over' b)*b2) (to_over' bot * bot2) mid2 up2
  | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : FreeMonoid' (Option ℕ × Bool)}
      (h : mid.length > 0)
      (g1 : PartialGrid' a b bot mid up) (g2 : PartialGrid' up b2 bot2 mid2 up2) :
      PartialGrid' a (b*b2) bot (mid * bot2 * mid2) up2
  | vertical_append_one {a b bot up b2 bot2 mid2 up2} (g1 : grid a b up bot)
        (g2 : PartialGrid' b2 (to_over' bot) bot2 mid2 up2) :
      PartialGrid' (b2 * to_up' a) (to_over' b) bot2 mid2 (up2 * to_up' up)
  | vertical_append {a b bot mid up b2 bot2 mid2 up2 : FreeMonoid' (Option ℕ × Bool)}
      (h : mid.length > 0)
      (g1 : PartialGrid' a b bot mid up) (g2 : PartialGrid' a2 bot bot2 mid2 up2) :
      PartialGrid' (a2*a) b bot2 (mid2 *up2 * mid) up

-- theorem grid_of_PartialGrid (h : PartialGrid a b d 1 c) : grid_option a b c d := by
--   generalize he : (1 : FreeMonoid' (Option ℕ × Bool)) = e at h
--   induction h with
--   | single_grid h =>
--     unfold grid_option
--     simp only [remover_up, remover_over]
--     exact h
--   | empty_both =>
--     unfold grid_option
--     simp only [remover]
--     exact grid.empty
--   | empty_side a _ =>
--     exfalso
--     have H3 := congr_arg FreeMonoid'.length (FreeMonoid.prod_eq_one he.symm).2
--     simp at H3
--   | empty a b =>
--     rw [(FreeMonoid.prod_eq_one he.symm).1, (FreeMonoid.prod_eq_one he.symm).2]
--     exact grid.empty
--   | horizontal_append_one g1 _ ih =>
--     specialize ih he
--     exact grid_option_append_horiz g1 ih
--   | horizontal_append _ _ _ g1_ih g2_ih =>
--     rename_i j k l m n o p q r _ _ _
--     have h4 := FreeMonoid.prod_eq_one he.symm
--     have h5 := FreeMonoid.prod_eq_one h4.1
--     have h1 : m = 1 := h5.1
--     have h2 : p = 1 := h5.2
--     have h3 : q = 1 := h4.2
--     specialize g1_ih h1.symm
--     specialize g2_ih h3.symm
--     have H := grid_option_append_horiz g1_ih g2_ih
--     rw [h2, mul_one] at H
--     exact H

theorem grid_of_PartialGrid' (h : PartialGrid' a b d 1 c) : grid_option a.reverse b c.reverse d := by
  generalize he : (1 : FreeMonoid' (Option ℕ × Bool)) = e at h
  induction h with
  | single_grid h =>
    unfold grid_option
    simp only [remover_up'_rev, remover_over']
    exact h
  | empty a b =>
    rw [(FreeMonoid.prod_eq_one he.symm).1, (FreeMonoid.prod_eq_one he.symm).2]
    exact grid.empty
  | horizontal_append_one g1 _ ih =>
    specialize ih he
    unfold grid_option
    rw [remover_split, remover_split]
    rw [remover_up'_rev, remover_over', remover_over']
    apply grid.horizontal g1
    unfold grid_option at ih
    rw [remover_up'_rev] at ih
    exact ih
  | horizontal_append _ _ _ g1_ih g2_ih =>
    have h4 := FreeMonoid.prod_eq_one he.symm
    have h5 := FreeMonoid.prod_eq_one h4.1
    have H := grid_option_append_horiz (g1_ih h5.1.symm) (g2_ih h4.2.symm)
    rw [h5.2, mul_one] at H
    exact H
  | vertical_append_one g1 _ ih =>
    specialize ih he
    unfold grid_option
    simp only [FreeMonoid'.reverse_mul, remover_over', remover_split, remover_up'_rev]
    apply grid.vertical g1
    unfold grid_option at ih
    rw [remover_over'] at ih
    exact ih
  | vertical_append _ _ _ g1_ih g2_ih =>
    have h4 := FreeMonoid.prod_eq_one he.symm
    have h5 := FreeMonoid.prod_eq_one h4.1
    rename_i e f g i j k l m n o p q r
    have H := grid_option_append_vert (g1_ih h4.2.symm) (g2_ih h5.1.symm)
    rw [h5.2] at H
    simp only [FreeMonoid'.length_one, FreeMonoid'.reverse_length,
      FreeMonoid'.eq_one_of_length_eq_zero, mul_one] at H
    simp only [FreeMonoid'.reverse_mul]
    exact H

-- theorem middle_starts_up (h : PartialGrid a b d mid c) : mid = 1 ∨ ∃ first, mid.get? 0 = some (first, false) := by
--   induction h with
--   | single_grid _ =>
--     left
--     rfl
--   | empty_both =>
--     right
--     use none
--     rfl
--   | empty_side a ha =>
--     induction a using FreeMonoid'.inductionOn'
--     · left
--       exfalso
--       simp only [FreeMonoid'.length_one, gt_iff_lt, lt_self_iff_false] at ha
--     right
--     rename_i b _ _
--     use b
--     rfl
--   | empty a b h =>
--     right
--     induction a using FreeMonoid'.inductionOn'
--     · exfalso
--       simp only [FreeMonoid'.length_one, gt_iff_lt, lt_self_iff_false] at h
--       exact h.1
--     rename_i _ h1 ta _
--     use h1
--     rfl
--   | horizontal_append_one _ _ ih =>
--     rcases ih with h1 | h2
--     · left
--       exact h1
--     right
--     exact h2
--   | horizontal_append g1 g2 h g1_ih g2_ih =>
--     right
--     rcases g1_ih with h1 | h2
--     · exfalso
--       apply congr_arg FreeMonoid'.length at h1
--       simp only [FreeMonoid'.length_one] at h1
--       rw [h1] at g1
--       exact Nat.not_succ_le_zero 0 g1
--     rcases h2 with ⟨firstie, hf⟩
--     use firstie
--     rw [← hf]
--     rename_i mid _ _ _ _ _
--     induction mid using FreeMonoid'.inductionOn'
--     · change List.get? [] _ = _ at hf
--       simp only [List.get?_nil] at hf
--     rw [mul_assoc, mul_assoc]
--     change List.get? ( _ :: _) _ = List.get? ( _ :: _) _
--     rw [List.get?_cons_zero, List.get?_cons_zero]


theorem middle_starts_up' (h : PartialGrid' a b d mid c) : mid = 1 ∨ ∃ first, mid.get? 0 = some (first, false) := by
  induction h with
  | single_grid _ =>
    left
    rfl
  | empty a b =>
    right
    induction a using FreeMonoid'.inductionOn'
    · use none
      rfl
    rename_i _ h1 ta _
    use h1
    unfold to_up'
    rename_i ih
    rcases ih with ⟨firstie, hf⟩

    
    sorry
    --rfl
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
  | vertical_append_one _ _ ih =>
    rcases ih with h1 | h2
    · left
      exact h1
    right
    exact h2
  | vertical_append g1 g2 h g1_ih g2_ih =>
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
    rw [mul_assoc]
    sorry --change List.get? ( _ :: _) _ = List.get? ( _ :: _) _
    --rw [List.get?_cons_zero, List.get?_cons_zero]

theorem false_not_in_to_over' (h : (x, false) ∈ to_over' b) : False := by
  unfold to_over' at h
  induction b
  · simp only [FreeMonoid'.mem_of, Prod.mk.injEq, Bool.false_eq_true, and_false] at h
  simp only [FreeMonoid'.mem_map, Prod.mk.injEq, Bool.true_eq_false, and_false, exists_const] at h

theorem true_not_in_to_up' (h : (x, true) ∈ to_up' b) : False := by
  unfold to_up' at h
  induction b
  · simp only [FreeMonoid'.mem_of, Prod.mk.injEq, Bool.true_eq_false, and_false] at h
  simp only [FreeMonoid'.mem_map, Prod.mk.injEq, Bool.false_eq_true, and_false, exists_const] at h

theorem grid_style_to_partial {a b : FreeMonoid' ℕ}
    (h : SemiThue_one_step grid_style (to_up' a * to_over' b) c) :
    ∃ d e f, PartialGrid' (to_up' a) (to_over' b) d e f ∧ c = d * e * f := by
  generalize he : (to_up' a * to_over' b) = e at h
  induction h with
  | refl x =>
    use 1, to_up' a * to_over' b, 1
    constructor
    · exact PartialGrid'.empty _ _
    rw [← he, one_mul, mul_one]
  | one_step h1 h2 ih =>
    rename_i i j k l m
    specialize ih he
    rcases ih with ⟨d₁, e₁, f₁, hf, hmf⟩
    generalize ha : to_up' a = a' at hf
    generalize hb : to_over' b = b' at hf
    induction h2 with
    | basic =>
      rename_i n
      have H : ∃ e1 e2, e₁ = e1 ++ [(some n, false), (some n, true)] ++ e2 := by sorry
      rcases H with ⟨e1, e2, h12⟩
      rw [h12] at hf
      generalize he12 : e1 ++ [(some n, false), (some n, true)] ++ e2 = e₁ at hf
      induction hf with
      | single_grid h =>
        exfalso
        apply congr_arg FreeMonoid'.length at he12
        change List.length _ = _ at he12
        simp only [List.append_assoc, List.cons_append, List.singleton_append, List.length_append,
          List.length_cons, Nat.succ_eq_add_one, FreeMonoid'.length_one, add_eq_zero,
          List.length_eq_zero, one_ne_zero, and_false, and_self] at he12
      | empty a b =>
        induction a using FreeMonoid'.inductionOn'
        · exfalso
          have H : (some n, false) ∈ e1 ++ [(some n, false), (some n, true)] ++ e2 := by
            simp only [List.append_assoc, List.cons_append, List.singleton_append, List.mem_append,
              List.mem_cons, Prod.mk.injEq, Bool.false_eq_true, and_false, false_or, true_or,
              or_true]
          rw [he12] at H
          rcases FreeMonoid'.mem_mul.mp H with h5 | h6
          · unfold to_up' at h5
            have H6 : (some n, false) ∈  FreeMonoid'.of (none, false) := h5
            simp only [FreeMonoid'.mem_of, Prod.mk.injEq, and_true] at H6
          exact false_not_in_to_over' h6
        rename_i head_a tail_a ih_a
        induction b using FreeMonoid'.inductionOn'
        · exfalso
          have H : (some n, true) ∈ e1 ++ [(some n, false), (some n, true)] ++ e2 := by
            simp only [List.append_assoc, List.cons_append, List.singleton_append, List.mem_append,
              List.mem_cons, Prod.mk.injEq, Bool.false_eq_true, and_false, false_or, true_or,
              or_true]
          rw [he12] at H
          rcases FreeMonoid'.mem_mul.mp H with h5 | h6
          · exact true_not_in_to_up' h5
          unfold to_over' at h6
          have H6 : (some n, true) ∈  FreeMonoid'.of (none, true) := h6
          simp only [FreeMonoid'.mem_of, Prod.mk.injEq, and_true] at H6
        rename_i head_b tail_b ih_b
        unfold to_up' at he12
        have H13 : e1 ++ [(some n, false), (some n, true)] ++ e2 =
            (FreeMonoid'.map fun x ↦ (some x, false)) (FreeMonoid'.of head_a * tail_a) *
            to_over' (FreeMonoid'.of head_b * tail_b) := by
          rw [he12]
          simp only [map_mul, FreeMonoid'.map_of, mul_left_inj]
          sorry


        use to_up' tail_a, [(none, true), (none, false)], to_over' tail_b
        constructor
        · have H_corner := PartialGrid'.single_grid (grid_from_cell (cell.top_left n))
          --change PartialGrid' [(some n, false)] [(some n, true)] [(none, true)] 1 [(none, false)] at H_corner
          have H_side := PartialGrid'.empty 1 tail_b
          have H_top := PartialGrid'.horizontal_append_one (grid_of_PartialGrid' H_corner) H_side
          have H_bot := PartialGrid'.empty tail_a 1
          have H_len : ((to_up' (1 : FreeMonoid' ℕ) : FreeMonoid' (Option ℕ × Bool)) * to_over' tail_b).length > 0 := by apply?
          rw [mul_one] at H_top
          sorry -- have H := PartialGrid'.vertical_append H_len H_top H_bot
        sorry
      | horizontal_append_one g1 g2 ih => sorry
      | horizontal_append h g1 g2 g1_ih g2_ih => sorry
      | vertical_append_one g1 g2 ih => sorry
      | vertical_append h g1 g2 g1_ih g2_ih => sorry
    | over => sorry
    | up => sorry
    | empty => sorry
    | apart h => sorry
    | close h => sorry

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
