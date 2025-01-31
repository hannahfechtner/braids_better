import BraidProject.Grids
import BraidProject.Reversing
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
  simp
  --change remover (_ :: _) = _
  rw [remover_split]
  --simp only [List.cons.injEq, true_and]
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
  change remover (_ :: _) = _
  rw [remover_mul]
  simp only [List.cons.injEq, true_and]
  cases b with
  | nil =>
    simp only [remover]
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


def is_false_up : is_false (to_up a) := by
  unfold to_up
  cases a with
  | nil =>
    simp [is_false]
  | cons head tail =>
    simp [is_false]

theorem is_false_append (h : is_false (a ++ b)) : is_false a ∧ is_false b := by
  constructor
  · exact fun x hx => h x (List.mem_append_of_mem_left b hx)
  exact fun x hx => h x (List.mem_append_of_mem_right a hx)
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
  · exact fun x hx => h x (List.mem_append_of_mem_left b hx)
  exact fun x hx => h x (List.mem_append_of_mem_right a hx)

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
    simp only [List.append_assoc, List.nil_eq_append, List.append_eq_nil] at he
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
    simp only [List.append_assoc, List.nil_eq_append, List.append_eq_nil] at he
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

theorem equiv_paths (h : PartialGrid a b c d e) : SemiThue_one_step grid_style' (a ++ b) (c ++ d ++ e) := by
  induction h with
  | single_grid h =>
    cases h with
    | empty =>
      simp
      apply one_step_equiv_reg.mp
      sorry
    | top_bottom i => sorry
    | sides i => sorry
    | top_left i => sorry
    | adjacent i k h => sorry
    | separated i j h => sorry
  | empty a b ha ha1 hb hb =>
    simp
    exact SemiThue_one_step.refl _
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp at g1_ih
    simp at g2_ih
    sorry
  | horizontal_append h g1 g2 g1_ih g2_ih => sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

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

theorem over_up_splits_at_i (h1 : is_false a) (h2 : is_false b) (h3 : a.length > 0) (h4 : b.length > 0)
      (h5 : a ++ b = k ++ ([(a3, false), (b3, true)] ++ l)) : ∃ a1 a2 b1 b2, a = a1 ++ a2 ∧ b = b1 ++ b2 ∧
      [(a3, false), (b3, true)] = a2 ++ b1 ∧ a1 = k ∧ b2 = l := by
  induction k generalizing a with
  | nil =>
    use [], [(a3, false)], [(b3, true)], l
  | cons head tail ih => sorry

theorem step_two (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b) (hb1 : b.length > 0) :
    SemiThue grid_style' (a ++ b) c → (∃ bot mid up, PartialGrid a b bot mid up ∧ bot ++ mid ++ up = c) := by
  intro h
  generalize ell : a ++ b = el at h
  induction one_step_equiv_reg.mp h with
  | refl x =>
    rw [← ell]
    use [], a++b, []
    constructor
    · exact PartialGrid.empty _ _ ha1 ha hb1 hb
    rw [List.append_nil, List.nil_append]
  | one_step h1 h2 ih =>
    rename_i i j k l m
    specialize ih ell (one_step_equiv_reg.mpr h1)
    rcases ih with ⟨bot1, mid1, up1, pg1, fe⟩
    induction pg1 generalizing m k l with
    | single_grid h =>
      exfalso
      rw [List.append_nil] at fe
      rcases grid_style_split h2 with ⟨a1, b1, i_is⟩
      rw [i_is] at fe
      exact over_up_neq_false_true fe
    | empty a b ha ha1 hb hb =>
      simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
                List.singleton_append] at fe
      rcases grid_style_split h2 with ⟨a3, b3, i_is⟩
      rw [i_is] at fe
      have H :  ∃ a1 a2 b1 b2, a = a1 ++ a2 ∧ b = b1 ++ b2 ∧ [(a3, false), (b3, true)] = a2 ++ b1 ∧ a1 = k ∧ b2 = l := by sorry
      rcases H with ⟨a1, a2, b1, b2, a_is, b_is, i_is, k_is, l_is⟩
      cases a1 with
      | nil =>
        cases b2 with
        | nil =>
          rw [← k_is, ← l_is]
          cases h2 with
          | basic =>
            use [(none, true)], [], [(none, false)]
            constructor
            · rename_i n
              have H := PartialGrid.single_grid (cell.top_left n)
              simp only [to_up_nil, to_over_nil] at H
              rw [List.nil_append] at a_is
              rw [a_is] at ha1
              rw [List.append_nil] at b_is
              rw [b_is] at hb1
              change [(some n, false)] ++[(some n, true)] = [(a3, false)] ++ [(b3, true)] at i_is
              have happ := List.append_eq_len_two (by simp) (by simp) i_is.symm
              simp at happ
              rename_i old_i
              have happ2 := List.append_eq_len_two ha1 hb1 old_i.symm
              rw [a_is, b_is, happ2.1, happ2.2, happ.1, happ.2]
              assumption
            rfl
          | over => sorry
          | up => sorry
          | empty => sorry
          | apart h => sorry
          | close h => sorry
        | cons head tail =>
          rw [← k_is, ← l_is]
          cases h2 with
          | basic =>
            rename_i n
            use [(none, true)], [(none, false)] ++ head :: tail, []
            constructor
            · have H := PartialGrid.single_grid (cell.top_left n)
              have h15 : is_false [(none, false)] := by
                unfold is_false
                simp only [List.mem_singleton, forall_eq]
              rw [← l_is, ← k_is] at fe
              have h18 : is_true (head :: tail) := by
                have h19 : is_true (b1 ++ (head :: tail)) := by
                  rw [← b_is]
                  exact hb
                exact (is_true_append h19).2
              have H2 := PartialGrid.empty [(none, false)] (head :: tail) (by simp) h15 (by simp) h18
              have H3 := PartialGrid.horizontal_append_one H H2
              simp only [to_up_singleton, to_over_singleton, List.singleton_append, to_over_nil] at H3
              simp at a_is
              rename_i old_i
              rw [← a_is] at old_i
              have H : a.length ≠ 2 := by
                intro h
                have hb1 : b1.length = 0 := by
                  apply congr_arg List.length at i_is
                  simp at i_is
                  omega
                have b1_is : b1 = [] := List.length_eq_zero.mp hb1
                rw [b1_is] at i_is
                simp at i_is
                rename_i false_a _ _ _ _
                rw [← i_is] at false_a
                simp [is_false] at false_a
              have H1 : ¬ a.length > 2 := by
                  intro h
                  apply congr_arg List.length at i_is
                  simp at i_is
                  omega
              have H : a.length = 1 := by omega
              have h4 : a = [(some n, false)] := Eq.symm (List.append_inj_left i_is (id (Eq.symm H)))
              rw [h4]
              have h5 : b = (some n, true) :: head :: tail := by
                rw [b_is]
                have H : b1 = [(some n, true)] := by
                  rw [h4] at i_is
                  change [(some n, false)] ++ [(some n, true)] = _ at i_is
                  exact List.append_cancel_left (id (Eq.symm i_is))
                rw [H]
                rfl
              rw [h5]
              assumption
            simp only [List.singleton_append, List.append_nil, List.nil_append, List.cons_append]
          | over => sorry
          | up => sorry
          | empty => sorry
          | apart h => sorry
          | close h => sorry
      | cons head tail => sorry
    | horizontal_append_one g1 g2 ih1 ih2 =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      rcases grid_style_split h2 with ⟨a1, b1, i_is⟩
      rw [i_is] at fe
      have hk : ∃ k₁ k₂, k = k₁ ++ k₂ ∧ bot3 ++ mid3 ++ up3 = k₂ ++ [(a1, false), (b1, true)] ++ l ∧ k₁ = bot2 := by sorry
      rcases hk with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
      rw [← i_is] at eq_rest
      have H1 : SemiThue grid_style' (up2 ++ b3) (k₂ ++ i ++ l) := by
        rw [← eq_rest]
        exact one_step_equiv_reg.mpr (equiv_paths g2)
      specialize @ih2 (right_frontier_is_false g1) (left_length_pos g2) (top_frontier_is_true g2) (top_length_pos g2) k₂ l (up2 ++ b3)
        (one_step_equiv_reg.mp H1) rfl (H1.trans _ (SemiThue.reduction h2)) eq_rest
      rcases ih2 with ⟨bot1, mid1, up1, pg1, fe1⟩
      use bot2 ++ bot1, mid1, up1
      constructor
      · exact PartialGrid.horizontal_append_one g1 pg1
      rw [List.append_assoc, List.append_assoc, ← List.append_assoc bot1, fe1, ← k₁_is, ← List.append_assoc, ← List.append_assoc, k_is]
    | horizontal_append h g1 g2 g1_ih g2_ih => sorry
    | vertical_append_one g1 g2 ih => sorry
    | vertical_append g1 g2 h g1_ih g2_ih => sorry
