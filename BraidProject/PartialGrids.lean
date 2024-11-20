import BraidProject.Grids
import BraidProject.Reversing

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

def grid_option (a b c d : FreeMonoid' (Option ℕ × Bool)) : Prop := grid (remover a) (remover b)
  (remover c) (remover d)

/-- A partial grid generalizes the notion of a grid to include "unfinished" grids. -/
inductive PartialGrid : FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) →
  FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → Prop
  | single_grid {a b c d : FreeMonoid' ℕ} (h : grid a b c d):
      PartialGrid (to_up a) (to_over b) (to_over d) 1 (to_up c)
  | empty (a b : FreeMonoid' ℕ) :
      PartialGrid (to_up a) (to_over b) 1 ((to_up a) * (to_over b)) 1
  | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : grid_option a b up bot)
      (g2 : PartialGrid up b2 bot2 mid2 up2) : PartialGrid a (b*b2) (bot * bot2) mid2 up2
  | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : FreeMonoid' (Option ℕ × Bool)}
      (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid up b2 bot2 mid2 up2) :
      PartialGrid a (b*b2) bot (mid * bot2 * mid2) up2

def frontier2 (pg : PartialGrid a b c d e) : FreeMonoid' (Option ℕ × Bool) := c * d * e

inductive pgrid : FreeMonoid' (Option ℕ) → FreeMonoid' (Option ℕ) → FreeMonoid' (Option ℕ) →
    FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ) →  Prop
  | spine (a b : FreeMonoid' (Option ℕ)): pgrid a b 1 (((FreeMonoid'.map fun x => (x, false)) a) *
      ((FreeMonoid'.map fun x => (x, true)) b)) 1
  | cell {a b c d} (h : cell a b c d) : pgrid ((FreeMonoid'.map fun x => some x) a)
      ((FreeMonoid'.map fun x => some x) b) ((FreeMonoid'.map fun x => some x) c.reverse) 1
      ((FreeMonoid'.map fun x => some x) d)
  | horizontal_L (h1 : pgrid a b c 1 e) (h2 : pgrid e f g h i) : pgrid a (b * f) (c * g) h i
  | horizontal (h1 : pgrid a b c d e) (h2 : pgrid e f g h i) : pgrid a (b * f) c
      (d * (FreeMonoid'.map (fun x => (x, true)) g) * h) i
  | vertical_L (h1 : pgrid a b c 1 e) (h2 : pgrid f c g h i) : pgrid (a * f) b g h (i * e)
  | vertical (h1 : pgrid a b c d e) (h2 : pgrid f c g h i) : pgrid a (b * f) c
      (d * (FreeMonoid'.map (fun x => (x, true)) g) * h) i

#exit
open FreeMonoid'

def get_across : List (FreeMonoid' ℕ × Bool) → FreeMonoid' ℕ :=
  fun L => match L with
  | (a, true) :: L1 => a * (get_across L1)
  | (_, false) :: _ => 1
  | [] => 1

-- should have a helper function because this is so inefficient
def get_right : List (FreeMonoid' ℕ × Bool) → FreeMonoid' ℕ :=
  fun L => match L.reverse with
  | (a, false) :: L1 => a * (get_across L1.reverse)
  | (_, true) :: _ => 1
  | [] => 1

def remove_right : List (FreeMonoid' ℕ × Bool) → List (FreeMonoid' ℕ × Bool) := sorry

def remove_across : List (FreeMonoid' ℕ × Bool) → List (FreeMonoid' ℕ × Bool) :=
  fun L => match L with
  | (_, false) :: _ => L
  | (_, true) :: L1 => remove_across L1
  | [] => []

def cfh : List (FreeMonoid' ℕ × Bool) → List (FreeMonoid' ℕ × Bool) →
  List (FreeMonoid' ℕ × Bool) := fun a b => (remove_right a) ++ b
def cfv : List (FreeMonoid' ℕ × Bool) → List (FreeMonoid' ℕ × Bool) →
  List (FreeMonoid' ℕ × Bool) := fun a b => a ++ remove_across b

--left side, top side, frontier, across, right
inductive pgrid4 : FreeMonoid' ℕ → FreeMonoid' ℕ → List (FreeMonoid' ℕ × Bool) →
    FreeMonoid' ℕ → FreeMonoid' ℕ → Prop
  | empty : pgrid4 1 1 [] 1 1
  | simple : pgrid4 (of a) (of b) [(of a, false), (of b, true)] 1 1
  | cell : cell a b c d → pgrid4 a b [(d, true), (c, false)] c d
  | append_horiz : pgrid4 a b c d e → pgrid4 d f g h i → pgrid4 a (b * f) (cfh c g)
      (get_across (cfh c g)) (get_right (cfh c g))
  | append_vert : pgrid4 a b c d e → pgrid4 f e g h i → pgrid4 (a * d) b (cfv c g)
      (get_across (cfv c g)) (get_right (cfh c g))

def lbw (c : List (FreeMonoid' ℕ × Bool)) : Prop := sorry

--claim : if L rws to L2, then we have a pgrid with a, b corresponding to L and a frontier corresponding to L2
theorem grid_of_pgrid (h1 : pgrid4 a b c d e) (h2 : lbw c) : grid a b d e := by
  induction h1
  · exact grid.empty
  · exfalso
    sorry
  · rename_i hc
    exact grid_from_cell hc
  · rename_i f g L i j k L2 l m pg1 pg2 ih1 ih2
    have H1 : lbw L := by sorry
    have H2 : lbw L2 := by sorry
    specialize ih1 H1
    specialize ih2 H2
    have H3 := grid.horizontal ih1 ih2
    have H4 : (get_across (cfh L L2)) = l := by sorry
    rw [H4]
    have H5 : (get_right (cfh L L2)) = j * m := by sorry
    rw [H5]
    exact H3
  sorry

def simp_list (L1 : List (FreeMonoid ℕ × Bool)) : List (FreeMonoid ℕ × Bool) :=
  match L1 with
  | [] => []
  | (a, true) :: t =>
    match t with
    | [] => L1
    | (b, true) :: r => ((a * b), true) :: (simp_list r)
    | (b, false) :: r => (a, true) :: (simp_list ((b, false) :: r))
  | (a, false) :: t =>
    match t with
    | [] => L1
    | (b, true) :: r => (a, false) :: (simp_list ((b, true) :: r))
    | (b, false) :: r => ((a * b), false) :: (simp_list r)

theorem empty_of_frontier_empty (h : pgrid2 i l []) : (grid i l 1 1) := by
  have H : ∀ i l L, pgrid2 i l L → L = [] → grid i l 1 1 := by
    intro i l L pg
    induction pg with
    | real =>
      intro h
      exact grid.empty
    | empty =>
        intro h_exf
        simp at h_exf
    | corner gr bot side ih_b ih_r =>
        rename_i L1 k L2
        intro list_is
        rename_i e f g h i j
        have H : L1 = [] ∧ L2 = [] := List.append_eq_nil.mp list_is
        rw [H.1] at bot
        rw [H.2] at side
        specialize ih_b H.1
        specialize ih_r H.2
        have H1 := grid.vertical gr ih_b
        have H2 := grid.vertical ih_r grid.empty
        exact grid.horizontal H1 H2
  exact H _ _ _ h rfl

-- theorem singleton_frontier (h : pgrid2 a b [(c, bb)]) : grid a b 1 1 := by
--   have H : ∀ d, pgrid2 a b d → d = [(c, bb)] → (grid a b 1 1) := by
--     intro d pg
--     induction pg with
--     | empty =>
--       intro h_exf
--       simp only [List.cons.injEq, Prod.mk.injEq, and_true, List.cons_ne_self, and_false] at h_exf
--     | corner gr bot side ih_b ih_r =>
--       rename_i e f g i j L1 k L2
--       intro list_is
--       have H : (L1 = [] ∧ L2 = [(c, bb)]) ∨ (L1 = [(c, bb)] ∧ L2 = []) := by sorry
--       rcases H with one | two
--       · rw [one.1] at bot
--         apply empty_of_frontier_empty at bot
--         rw [one.2] at side
--         specialize ih_r side one.2
--         have H1 := grid.horizontal gr ih_r
--         have H2 := grid.horizontal bot grid.empty
--         rw [mul_one] at H1
--         rw [mul_one, mul_one] at H2
--         exact grid.vertical H1 H2
--       rw [two.2] at side
--       apply empty_of_frontier_empty at side
--       rw [two.1] at bot
--       specialize ih_b bot two.1
--       have H1 := grid.vertical gr ih_b
--       have H2 := grid.vertical side grid.empty
--       exact grid.horizontal H1 H2
--   exact H _ h rfl

theorem list_fact_one (h : L1 ++ L2 =[a]) : L1 = [] ∧ L2 = [a] ∨ L1 = [a] ∧ L₂ = [] := by sorry
theorem list_fact_two (h : L1 ++ L2 = [a, b]) : (L₁ = [a, b] ∧ L₂ = []) ∨ (L₂ = [a, b] ∧ L₁ = []) ∨
        (L₁ = [a] ∧ L₂ = [b]) := by sorry
theorem singleton_frontier_up (h : pgrid2 a b [(c, false)]) : grid a b c 1 := by
  have H : ∀ d, pgrid2 a b d → d = [(c, false)] → (grid a b c 1) := by
    intro d pg
    induction pg with
    | real =>
      intro h
      simp only at h
    | empty =>
      intro h_exf
      simp only [List.cons.injEq, Prod.mk.injEq, and_true, List.cons_ne_self, and_false] at h_exf
    | corner gr bot side ih_b ih_r =>
      rename_i e f g i j L1 k L2
      intro list_is
      have H : (L1 = [] ∧ L2 = [(c, false)]) ∨ (L1 = [(c, false)] ∧ L2 = []) := list_fact_one list_is
      rcases H with one | two
      · rw [one.1] at bot
        apply empty_of_frontier_empty at bot
        rw [one.2] at side
        specialize ih_r side one.2
        have H1 := grid.horizontal gr ih_r
        have H2 := grid.horizontal bot grid.empty
        rw [mul_one] at H1
        rw [mul_one, mul_one] at H2
        have H3 := grid.vertical H1 H2
        rw [mul_one] at H3
        exact H3
      rw [two.2] at side
      apply empty_of_frontier_empty at side
      rw [two.1] at bot
      specialize ih_b bot two.1
      have H1 := grid.vertical gr ih_b
      have H2 := grid.vertical side (grid_sides_word c)
      have H3 := grid.horizontal H1 H2
      rw [mul_one] at H3
      exact H3
  exact H _ h rfl

theorem singleton_frontier_down (h : pgrid2 a b [(d, true)]) : grid a b 1 d := by
  have H : ∀ c, pgrid2 a b c → c = [(d, true)] → (grid a b 1 d) := by
    intro c pg
    induction pg with
    | real =>
      intro h
      simp only at h
    | empty =>
      intro h_exf
      simp only [List.cons.injEq, Prod.mk.injEq, and_true, List.cons_ne_self, and_false] at h_exf
    | corner gr bot side ih_b ih_r =>
      rename_i e f g i j L1 k L2
      intro list_is
      have H : (L1 = [] ∧ L2 = [(d, true)]) ∨ (L1 = [(d, true)] ∧ L2 = []) := list_fact_one list_is
      rcases H with one | two
      · rw [one.1] at bot
        apply empty_of_frontier_empty at bot
        rw [one.2] at side
        specialize ih_r side one.2
        have H1 := grid.horizontal gr ih_r
        have H2 := grid.horizontal bot (grid_top_bottom_word d)
        have H3 := grid.vertical H1 H2
        rw [mul_one] at H3
        exact H3
      rw [two.2] at side
      apply empty_of_frontier_empty at side
      rw [two.1] at bot
      specialize ih_b bot two.1
      have H1 := grid.vertical gr ih_b
      have H2 := grid.vertical side grid.empty
      have H3 := grid.horizontal H1 H2
      rw [mul_one, mul_one] at H3
      exact H3
  exact H _ h rfl

theorem grid_of_pgrid2 (h : pgrid2 a b [(d, true), (c, false)]) : grid a b c d := by
  have H : ∀ a b L, pgrid2 a b L → ∀ c d, L =[(d, true), (c, false)] → grid a b c d := by
    intro a b L pg
    induction pg with
    | real =>
      intro c d list_is
      simp at list_is
    | empty =>
      rename_i a b e f
      intro c d h_exf
      simp only [List.cons.injEq, Prod.mk.injEq, Bool.false_eq_true, and_false, Bool.true_eq_false,
        and_true, and_self] at h_exf
    | corner gr below right ih_b ih_r =>
      rename_i e f g h i j k L₁ l L₂
      intro c d frontier_is
      have H1 : (L₁ = [(d, true), (c, false)] ∧ L₂ = []) ∨ (L₂ = [(d, true), (c, false)] ∧ L₁ = []) ∨
        (L₁ = [(d, true)] ∧ L₂ = [(c, false)]) := list_fact_two frontier_is
      rcases H1
      · rename_i one
        specialize ih_b _ _ one.1
        have H := grid.vertical gr ih_b
        have H2 : grid i l 1 1 := by
          apply empty_of_frontier_empty
          rw [one.2] at right
          exact right
        have H3 := grid.vertical H2 (grid_sides_word c)
        have H4 := grid.horizontal H H3
        rw [one_mul, mul_one] at H4
        exact H4
      rename_i H2
      rcases H2
      · rename_i two
        specialize ih_r _ _ two.1
        have H := grid.horizontal gr ih_r
        have H2 : grid k j 1 1 := by
          apply empty_of_frontier_empty
          rw [two.2] at below
          exact below
        have H3 := grid.horizontal H2 (grid_top_bottom_word d)
        have H4 := grid.vertical H H3
        rw [mul_one, one_mul] at H4
        exact H4
      rename_i three
      rw [three.1] at below
      rw [three.2] at right
      have il := singleton_frontier_up right
      have kj := singleton_frontier_down below
      have H1 := grid.horizontal gr il
      have H2 := grid.horizontal kj grid.empty
      have H3 := grid.vertical H1 H2
      rw [mul_one, mul_one] at H3
      exact H3
  exact H _ _ _ h _ _ rfl

#exit
theorem grid_to_pgrid (h : grid a b c d) : pgrid2 a b [(d, true), (c, false)] := by sorry
theorem rev'_to_grid'' {a b c d : FreeMonoid' ℕ} (h : second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c))) : pgrid2 a b [(d, true), (c, false)] := by
  have H : ∀ e f, second_rw_closure reversing_rels' e f → ∀ a b c d, e = (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
      FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b) → f = (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
      FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c)) → pgrid2 a b [(d, true), (c, false)] := by
    intro e f hef
    induction hef with
    | refl g =>
      intro a b c d a1 a2
      have H := a1.symm.trans a2
      have H1 : a = 1 ∧ c = 1 ∧ b = d ∨ b = 1 ∧ d = 1 ∧ a = c := by sorry
      rcases H1 with one | two
      · rw [one.1, one.2.1, one.2.2]
        apply grid_to_pgrid
        exact grid_top_bottom_word d
      rw [two.1, two.2.1, two.2.2]
      apply grid_to_pgrid (grid_sides_word c)
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
        exact grid_to_pgrid <| grid_top_left_word b
      | adjacent i j h =>
        have H : a = FreeMonoid.of i ∧ b = FreeMonoid.of j ∧ d = [j, i] ∧ c = [i, j] := by sorry
        rw [H.1, H.2.1, H.2.2.1, H.2.2.2]
        exact grid_to_pgrid <| grid.adjacent _ _ h
      | separated i j h =>
        have H : a = FreeMonoid.of i ∧ b = FreeMonoid.of j ∧ d = FreeMonoid.of j ∧ c = FreeMonoid.of i := by sorry
        rw [H.1, H.2.1, H.2.2.1, H.2.2.2]
        apply grid_to_pgrid
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

#exit
theorem grid_of_pgrid' (h : pgrid (some a) (some b) (some c) (some d)) : grid a b c d := by
  have H : ∀ a' b' c' d', pgrid a' b' c' d' → ∀ a b c d, a' = some a → b' = some b → c' = some c → d' = some d → grid a b c d := by
    intro a' b' c' d'
    intro pg
    induction pg with
    | incomplete =>
      intro _ _ _ _ _ _ h1
      simp only at h1
    | single h =>
      intro a b c d ha hb hc hd
      rename_i e f g i
      have ea : e = a := by sorry
      have fb : f = b := by sorry
      have gc : g = c := by sorry
      have id : i = d := by sorry
      rw [ea, fb, gc, id] at h
      apply grid_from_cell
      assumption
    | horizontal h1 h2 h1_ih h2_ih =>
      rename_i e f g i j k l
      intro a1 b1 c1 d1
      intro k_is ed
      sorry
  apply H _ _ _ _ h _ _ _ _ rfl rfl
