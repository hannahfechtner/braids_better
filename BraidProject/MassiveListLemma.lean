import BraidProject.PartialGrids
import BraidProject.StepOne
import Mathlib.Data.List.Infix

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


open PartialGrid
theorem List.prefix_of_append {α : Type} {l1 l2 l3: List α} (h : l1 <+: l2) : l1 <+: l2 ++ l3 := by
  rcases h with ⟨rest, spec⟩
  use rest ++ l3
  rw [← spec, List.append_assoc]

theorem suffix_of_append (h : l₁ <:+ l2) : l₁ <:+ l3 ++ l2 := by
  rcases h with ⟨rest, spec⟩
  use l3 ++ rest
  simp [spec]

theorem List.suffix_append_right (h : l1 <:+ l2) : l1 ++ l3 <:+ l2 ++ l3 := by
  rcases h with ⟨rest, spec⟩
  use rest
  rw [← spec, List.append_assoc]

theorem is_true_cons (h : is_true (a :: b)) : is_true [a] ∧ is_true b := by
  change is_true ([a]++b) at h
  exact is_true_append h

theorem is_false_cons (h : is_false (a :: b)) : is_false [a] ∧ is_false b := by
  change is_false ([a]++b) at h
  exact is_false_append h

theorem is_true_singleton (h : is_true [a]) : ∃ a', a = (a', true) := by
  rcases a with ⟨c, b⟩
  use c
  simp
  specialize h (c, b) (List.mem_singleton.mpr rfl)
  exact h

theorem is_false_singleton (h : is_false [a]) : ∃ a', a = (a', false) := by
  rcases a with ⟨c, b⟩
  use c
  simp
  specialize h (c, b) (List.mem_singleton.mpr rfl)
  exact h

def PartialGrid.extend_bottom (h : PartialGrid a b c d e) (a2) (h2 : is_false a2) (h3 : a2 ≠ []) :
    PartialGrid (a2 ++ a) b [] (a2 ++ c ++ d) e := by
  induction h with
  | single_grid h =>
    cases a2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i d
      have H := PartialGrid.vertical_append_one (PartialGrid.single_grid h)
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
    have H := PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos.mpr h3)) ih1 g2
    rw [List.append_nil] at H
    rw [← List.append_assoc]
    exact H
  | horizontal_append h g1 g2 ih1 ih2 =>
    have H := PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos.mpr h3)) ih1 g2
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

def PartialGrid.extend_side (h : PartialGrid a b c d e) (b2) (h2 : is_true b2) (h3 : b2 ≠ []) :
    PartialGrid a (b ++ b2) c (d ++ e ++ b2) [] := by
  induction h with
  | single_grid h =>
    cases b2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i c _
      have H := PartialGrid.horizontal_append_one (PartialGrid.single_grid h)
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
    have H := PartialGrid.vertical_append g1_ih g2 (by simp; exact Or.inr (List.length_pos.mpr h3))
    rw [← List.append_assoc, ← List.append_assoc, List.append_nil] at H
    rw [← List.append_assoc]
    exact H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    have H := PartialGrid.vertical_append g1_ih g2 (by simp; exact Or.inr (Or.inr (List.length_pos.mpr h3)))
    rw [← List.append_assoc, ← List.append_assoc] at H
    exact H

def middle_spec (d : List (α × Bool)) := d = [] ∨ ∃ front mid caboose, d = [(front, false)] ++ mid ++ [(caboose, true)]

def middle_end (d : List (α × Bool)) := d = [] ∨ ∃ mid caboose, d = mid ++ [(caboose, true)]

def middle_start (d : List (α × Bool)) := d = [] ∨ ∃ front mid, d = [(front, false)] ++ mid

theorem middle_start_append (h : middle_start (d1 ++ d2)) : middle_start d1 := by
  cases d1 with
  | nil => left; rfl
  | cons head tail =>
    right
    rcases h with h1 | ⟨f, m, spec⟩
    · simp at h1
    simp at spec
    use f, tail
    rw [spec.1]
    simp

theorem middle_start_from_spec (h : middle_spec d) : middle_start d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use f, m ++ [(c, true)]
  exact spec

theorem middle_end_from_spec (h : middle_spec d) : middle_end d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use [(f, false)] ++ m, c

theorem middle_frontier_nil_or_caps (h : PartialGrid a b c d e) : middle_spec d := by
  induction h with
  | single_grid h =>
    left; rfl
  | empty a b ha ha1 hb hb =>
    right
    generalize hn : a ++ b = n
    induction n using List.reverseRecOn with
    | nil =>
      exfalso
      simp at hn
      rw [hn.1] at ha
      simp at ha
    | append_singleton fn cn _ =>
      cases fn with
      | nil =>
        apply congr_arg List.length at hn
        simp at hn
        omega
      | cons hf td =>
        have H : ∃ cb, cn = (cb, true) := by
          apply is_true_singleton
          rename_i length_b _
          induction b using List.reverseRecOn with
          | nil => simp at length_b
          | append_singleton front caboose _ =>
            rw [← List.append_assoc] at hn
            apply List.append_singleton_eq_append_singleton at hn
            rw [← hn.2]
            exact (is_true_append hb).2
        have H2 : ∃ bb, hf = (bb, false) := by
          apply is_false_singleton
          induction a with
          | nil => simp at ha
          | cons front caboose _ =>
            simp at hn
            rw [← hn.1]
            exact (is_false_append ha1).1
        rcases H with ⟨cb, hcb⟩
        rw [hcb]
        rcases H2 with ⟨hbb, hhbb⟩
        rw [hhbb]
        use hbb, td, cb
        simp
  | horizontal_append_one g1 g2 g1_ih g2_ih => assumption
  | horizontal_append h1 g1 g2 g1_ih g2_ih =>
    rename_i bot2 _ _
    rcases g1_ih with ha | hb
    · rw [ha] at h1
      simp at h1
    rcases g2_ih with hc | hd
    · right; rw [hc, List.append_nil];
      rcases hc with ⟨f1, c1, h1⟩
      induction bot2 using List.reverseRecOn with
      | nil => rw [List.append_nil]; exact hb
      | append_singleton f2 c2 _ =>
        rcases hb with ⟨f1, m1, c1, h1⟩
        rw [h1]
        have H : ∃ cb, c2 = (cb, true) := is_true_singleton <| (is_true_append (bottom_frontier_is_true g2)).2
        rcases H with ⟨cb, cbspec⟩
        rw [cbspec]
        use f1, m1 ++ [(c1, true)] ++ f2, cb
        simp
    rcases hb with ⟨front1, m1, caboose1, h1⟩
    rcases hd with ⟨front2, m2, caboose2, h2⟩
    right
    rw [h1, h2]
    use front1, m1 ++ [(caboose1, true)] ++ bot2 ++ [(front2, false)] ++ m2, caboose2
    simp
  | vertical_append_one g1 g2 g1_ih g2_ih => assumption
  | vertical_append g1 g2 h g1_ih g2_ih =>
    right
    rcases g1_ih with h1 | h2
    · rw [h1] at h
      simp at h
    rcases g2_ih with h3 | h4
    · rw [h3, List.nil_append]
      rcases h2 with ⟨f1, m1, c1, spec⟩
      rename_i up2
      cases up2 with
      | nil =>
        use f1,m1, c1
        rw [spec]
        simp
      | cons head tail =>
        have H : is_false [head] := by
          exact (is_false_append (right_frontier_is_false g2)).1
        rcases is_false_singleton H with ⟨hf, spec2⟩
        use hf, tail ++ [(f1, false)] ++ m1, c1
        simp [spec2, spec]
    rcases h2 with ⟨f1, m1, c1, spec1⟩
    rcases h4 with ⟨f2, m2, c2, spec2⟩
    rw [spec1, spec2]
    rename_i up2
    use f2, m2 ++ [(c2, true)] ++ up2 ++ [(f1, false)] ++ m1, c1
    simp

theorem double_split_helper_two_one  (h : mid2 ++ bot3 = [(a1, false), (b1, true)] ++ b)
    (hm2 : middle_end mid2) (hbot3 : is_true bot3 ∨ is_false bot3) :
    (∃ m2, mid2 = [(a1, false), (b1, true)] ++ m2) := by
  induction bot3 using List.reverseRecOn generalizing b with
  | nil =>
    rw [List.append_nil] at h
    use b
  | append_singleton frontb cabooseb ihb =>
    induction b using List.reverseRecOn with
    | nil =>
      rw [List.append_nil, ← List.append_assoc] at h
      change _ = [(a1, false)] ++ [(b1, true)] at h
      apply List.append_singleton_eq_append_singleton at h
      rcases hm2 with is_nil | ⟨frontm, endm, hfe⟩
      · exfalso
        rw [is_nil, List.nil_append] at h
        rcases hbot3 with h3 | h4
        · rw [h.1] at h3
          apply is_true_append at h3
          simp [is_true] at h3
        rw [h.2] at h4
        apply is_false_append at h4
        simp [is_false] at h4
      rw [hfe] at h
      have H0 := congr_arg List.length h.1
      simp at H0
      have H1 : frontm = [] := List.length_eq_zero.mp (by omega)
      have H2 : frontb = [] := List.length_eq_zero.mp (by omega)
      rw [H1, H2] at h
      simp at h
    | append_singleton frontbb caboosebb _ =>
      rw [← List.append_assoc, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      rcases hbot3 with h3 | h4
      · exact @ihb frontbb h.1 (Or.inl (is_true_append h3).1)
      exact @ihb frontbb h.1 (Or.inr (is_false_append h4).1)

theorem double_split_helper_two_three (h : bot3 ++ mid3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hbot3 : is_true bot3 ∨ is_false bot3) (hm3 : middle_start mid3):
    ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 := by
  induction bot3 generalizing k with
  | nil => use k, l; simp at h; simp [h]
  | cons head tail ih =>
    cases k with
    | nil =>
      rw [List.nil_append] at h
      simp at h
      rcases hbot3 with h3 | h4
      · rw [h.1] at h3
        simp [is_true] at h3
      cases tail with
      | nil =>
        rcases hm3 with h5 | ⟨f1, m1, spec⟩
        · rw [h5] at h
          simp at h
        rw [spec] at h
        simp at h
      | cons head tail =>
        simp at h
        rw [h.2.1] at h4
        simp [is_false] at h4
    | cons headk tailk =>
      simp only [List.cons_append,List.cons.injEq] at h
      have h2 : is_true tail ∨ is_false tail := by
        rcases hbot3 with h1 | h2
        · exact Or.inl (is_true_cons h1).2
        exact Or.inr (is_false_cons h2).2
      exact @ih tailk h.2 h2

theorem empty_middle_helper {b : Bool} (hm2 : middle_end mid2) (hm3 : middle_start mid3)
    (h : mid2 ++ [(a', b)] ++ mid3 = [(a1, false), (b1, true)]) : False := by
    rcases hm2 with h3 | h4
    · rcases hm3 with h5 | h6
      · rw [h3, h5] at h
        simp at h
      rcases h6 with ⟨f, m, spec2⟩
      rw [spec2] at h
      have := congr_arg List.length h
      simp at this
      have : m.length = 0 ∧ mid2.length = 0 := by omega
      have H : m = [] ∧ mid2 = [] := ⟨List.length_eq_zero.mp this.1, List.length_eq_zero.mp this.2⟩
      rw [H.1, H.2] at h
      simp at h
    rcases h4 with ⟨f, m, spec2⟩
    rw [spec2] at h
    have := congr_arg List.length h
    simp at this
    have : f.length = 0 ∧ mid3.length = 0 := by omega
    have H : f = [] ∧ mid3 = [] := ⟨List.length_eq_zero.mp this.1, List.length_eq_zero.mp this.2⟩
    rw [H.1, H.2] at h
    simp at h

theorem double_split_helper_three_one_s (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)])
    (hm2 : middle_end mid2)
    (hm3 : middle_start mid3) (hbot3 : is_true bot3 ∨ is_false bot3) :
    (∃ m2, mid2 = [(a1, false), (b1, true)] ++ m2) ∨ ∃ m3, mid3 = m3 ++ [(a1, false), (b1, true)] := by
  have len := congr_arg List.length h
  simp only [List.append_assoc, List.length_append, List.length_cons, List.length_singleton,
    Nat.succ_eq_add_one, Nat.reduceAdd, List.length_nil, zero_add, Nat.reduceAdd] at len
  have : bot3.length ≠ 2 := by
    intro h1
    have H1 : mid2.length = 0 := by omega
    have H2 : mid3.length = 0 := by omega
    rw [List.length_eq_zero.mp H1, List.length_eq_zero.mp H2, List.nil_append, List.append_nil] at h
    rw [h] at hbot3
    simp [is_true, is_false] at hbot3
  have : bot3.length ≠ 1 := by
    intro h2
    have Hb : ∃ a, bot3 = [a] := List.length_eq_one.mp h2
    rcases Hb with ⟨a, ha⟩
    rcases hbot3 with h_t | h_f
    · rw [ha] at h_t
      rcases is_true_singleton h_t with ⟨a', spec⟩
      rw [ha, spec] at h
      exact empty_middle_helper hm2 hm3 h
    rw [ha] at h_f
    rcases is_false_singleton h_f with ⟨a', spec⟩
    rw [ha, spec] at h
    exact empty_middle_helper hm2 hm3 h
  have H : bot3 = [] := List.length_eq_zero.mp (by omega)
  rw [H, List.append_nil] at h
  have H : mid2.length ≠ 1 := by
    intro hm_length
    rcases List.length_eq_one.mp hm_length with ⟨a, ha⟩
    rw [ha] at h
    simp only [List.singleton_append, List.cons.injEq] at h
    rw [h.1] at ha
    rw [ha] at hm2
    rcases hm2 with h1 | ⟨a2, a3, ha2⟩
    · simp at h1
    have h4 : a2 = [] := by
      apply congr_arg List.length at ha2
      simp only [List.length_singleton, List.length_append, self_eq_add_left,
        List.length_eq_zero] at ha2
      exact ha2
    rw [h4, List.nil_append] at ha2
    simp at ha2
  have H2 : mid2.length = 0 ∨ mid2.length = 2 := by omega
  rcases H2 with zero | two
  · rw [List.length_eq_zero.mp zero, List.nil_append] at h
    right; use []; rw [h]; rfl
  have H3 : mid3.length = 0 := by omega
  rw [List.length_eq_zero.mp H3, List.append_nil] at h
  left; use []; rw [h]; rfl

theorem double_split_helper_three_one (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)])
    (hm2 : middle_end mid2)
    (hm3 : middle_start mid3) (hbot3 : is_true bot3 ∨ is_false bot3) :
    (∃ m2, mid2 = [(a1, false), (b1, true)] ++ m2) ∨ ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ [] = m4 := by
  rcases double_split_helper_three_one_s h hm2 hm3 hbot3 with h1 | ⟨m3, hm3⟩
  · left; exact h1
  right; use m3, []; simp [hm3]

theorem double_split_helper_three_two_s (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)] ++ l)
    (hm2 : middle_end mid2)
    (hm3 : middle_start mid3) (hbot3 : is_true bot3 ∨ is_false bot3) :
    (∃ m2, mid2 = [(a1, false), (b1, true)] ++ m2) ∨
    ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 := by
  induction l using List.reverseRecOn generalizing mid3 with
  | nil => exact double_split_helper_three_one h hm2 hm3 hbot3
  | append_singleton head tail ih =>
    induction mid3 using List.reverseRecOn with
    | nil =>
      rw [List.append_nil] at h
      left
      exact double_split_helper_two_one h hm2 hbot3
    | append_singleton headm tailm _ =>
      rw [← List.append_assoc, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      specialize @ih headm h.1 (middle_start_append hm3)
      rcases ih with ha | ⟨m3, m4, hm34⟩
      · left; exact ha
      right
      rw [hm34.1, hm34.2, ← h.2]
      use m3, m4 ++ [tailm]
      simp

theorem double_split_helper_three_two (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)] ++ l)
    (hm2 : middle_end mid2)
    (hm3 : middle_start mid3) (hbot3 : is_true bot3 ∨ is_false bot3) :
    (∃ m1 m2, mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ [] = m1) ∨
    ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 := by
  rcases double_split_helper_three_two_s h hm2 hm3 hbot3 with ⟨m2, hm2⟩ | h2
  · left; use [], m2
    rw [hm2]
    simp
  right; exact h2

theorem double_split_helper_three {mid2 bot3 mid3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
    (hbot3 : is_true bot3 ∨ is_false bot3)
    (hm2 : middle_end mid2)
    (hm3 : middle_start mid3)
    (h : mid2 ++ bot3 ++ mid3 = k ++ [(a1, false), (b1, true)] ++ l) :
    (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = m1)) ∨
    (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4)) := by
  induction k generalizing mid2 with
  | nil => exact double_split_helper_three_two h hm2 hm3 hbot3 --its own lemma
  | cons head tail ih =>
    cases mid2 with
    | nil =>
      right
      exact double_split_helper_two_three h hbot3 hm3 -- its own lemma
    | cons head tail =>
      simp at h
      have Ht : tail = [] ∨ ∃ front a, tail = front ++ [(a, true)] := by
        rcases hm2 with h1 | h2
        · simp at h1
        rcases h2 with ⟨f1, a1, spec⟩
        cases f1 with
        | nil => left; simp at spec; exact spec.2
        | cons head tail => right; simp at spec; use tail, a1; exact spec.2
      simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
        List.nil_eq_append_iff] at ih
      specialize @ih tail Ht h.2
      rcases ih with ⟨m1, m2, hm12⟩ | ⟨m3, m4, hm34⟩
      · left
        use head :: m1, m2
        rw [hm12.1, hm12.2, h.1]
        simp
      right
      use m3, m4
      simp
      exact hm34

theorem double_split_helper_four {mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
     (hbot3 : is_true bot3 ∨ is_false bot3) (hup3 : is_false up3)
    (h : (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
        (hm2 : middle_spec mid2)
    (hm3 : middle_spec mid3) :
    (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = m1)) ∨
    (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3)) := by
  induction up3 using List.reverseRecOn generalizing l with
  | nil =>
    rw [List.append_nil] at h
    simp
    have H2 := double_split_helper_three hbot3 (middle_end_from_spec hm2) (middle_start_from_spec hm3) h
    simp at H2
    exact H2
  | append_singleton front caboose ih =>
    induction l using List.reverseRecOn with
    | nil =>
      exfalso
      have H3 : [(a1, false), (b1, true)] = [(a1, false)] ++ [(b1, true)] := rfl
      rw [List.append_nil, ← List.append_assoc, H3, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      rw [h.2] at hup3
      apply is_false_append at hup3
      simp [is_false] at hup3
    | append_singleton headl taill =>
      have H : is_false front := (is_false_append hup3).1
      rw [← List.append_assoc, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      specialize @ih headl H h.1
      rcases ih with ⟨m1, m2, hm12, k_is⟩ | ⟨m3, m4, hm34, l_is⟩
      · left
        use m1, m2
      right
      use m3, m4
      constructor
      · simp at hm34
        simp
        exact hm34
      simp [l_is, h.2]

theorem double_split_helper' {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
    (hbot2 : is_true bot2) (hbot3 : is_true bot3 ∨ is_false bot3) (hup3 : is_false up3)
        (hm2 : middle_spec mid2)
    (hm3 : middle_spec mid3)
    (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l) :
    (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = bot2 ++ m1)) ∨
    (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3)) := by
  induction bot2 generalizing k with
  | nil =>
    rw [List.nil_append] at h
    exact double_split_helper_four hbot3 hup3 h hm2 hm3
  | cons head tail ih =>
    cases k with
    | nil =>
      simp at h
      rw [h.1] at hbot2
      simp [is_true] at hbot2
    | cons headl taill =>
      simp at h
      simp only [List.append_assoc, List.cons_append, List.singleton_append] at ih
      specialize @ih taill (is_true_cons hbot2).2 h.2
      rcases ih with ⟨m1, m2, hm12, k_is⟩ | ⟨m3, m4, hm34, l_is⟩
      · left
        use m1, m2
        constructor
        · simp at hm12
          simp
          exact hm12
        simp
        exact ⟨h.1.symm, k_is⟩
      right
      use m3, m4
      constructor
      · simp at hm34
        simp
        exact hm34
      exact l_is

theorem double_split_horiz {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
    (hbot2 : is_true bot2) (hbot3 : is_true bot3 ∨ is_false bot3) (hup3 : is_false up3)
    (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hm : middle_spec mid2)
    (hm3 : middle_spec mid3) :
    (∃ k₁ k₂, k = k₁ ++ k₂ ∧ k₁ = bot2 ++ mid2 ∧ k₂ ++ [(a1, false), (b1, true)] ++ l = bot3 ++ mid3 ++ up3) ∨
    (∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₂ = bot3 ++ mid3 ++ up3 ∧ k ++ [(a1, false), (b1, true)] ++ l₁ = bot2 ++ mid2) := by
  rcases @double_split_helper' bot2 mid2 bot3 mid3 up3 k l a1 b1 hbot2 hbot3 hup3 hm hm3 h with ⟨m1, m2, hm12, k_is⟩ | ⟨m3, m4, hm34, l_is⟩
  · right
    rw [hm12] at h
    rw [hm12]
    use m2, bot3 ++ mid3 ++ up3
    constructor
    · rw [k_is] at h
      simp at h
      simp
      exact h.symm
    constructor
    · rfl
    simp [k_is]
  left
  rw [hm34] at h
  rw [hm34]
  rw [l_is, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at h
  repeat apply List.append_cancel_right at h
  use bot2 ++ mid2, bot3 ++ m3
  constructor
  · rw [← List.append_assoc]
    exact h.symm
  constructor
  · rfl
  simp [l_is]

theorem prefix_true (h1 : is_true bot3) (h : k₂ ++ [(a1, false), (b1, true)] ++ l = bot3 ++ mid3 ++ up3) :
    bot3 <+: k₂ := by
  induction k₂ generalizing bot3 with
  | nil =>
    cases bot3 with
    | nil => exact List.nil_prefix
    | cons head tail =>
      simp at h
      rw [← h.1] at h1
      simp [is_true] at h1
  | cons head tail ih =>
    cases bot3 with
    | nil => exact List.nil_prefix
    | cons head1 tail1 =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      specialize @ih tail1 (is_true_cons h1).2 h.2
      rw [h.1]
      exact (List.prefix_cons_inj head1).mpr ih

theorem prefix_false (h1 : is_false t3) (h : tk ++ [(a1, false), (b1, true)] ++ l =
    t3 ++ (f, false) :: (m ++ [(c, true)]) ++ up3) : t3 <+: tk := by
  induction tk generalizing t3 with
  | nil =>
    cases t3 with
    | nil => exact List.nil_prefix
    | cons head tail =>
      cases tail with
      | nil =>
        simp at h
      | cons ht tt =>
        simp at h
        rw [← h.2.1] at h1
        simp [is_false] at h1
  | cons head tail ih =>
    cases t3 with
    | nil =>
      exact List.nil_prefix
    | cons ht tt =>
      simp at h
      specialize @ih tt (is_false_cons h1).2 (by simp [h.2])
      rw [h.1]
      exact (List.prefix_cons_inj ht).mpr ih


theorem double_split_horiz' {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
    (hbot2 : is_true bot2) (hbot3 : is_true bot3 ∨ is_false bot3) (hup3 : is_false up3)
    (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hm : middle_spec mid2)
    (hm3 : middle_spec mid3) :
    (∃ k₁ k₂, k = k₁ ++ k₂ ∧ k₁ = bot2 ++ mid2 ++ bot3 ∧ k₂ ++ [(a1, false), (b1, true)] ++ l =  mid3 ++ up3) ∨
    (∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₂ = mid3 ++ up3 ∧ k ++ [(a1, false), (b1, true)] ++ l₁ = bot2 ++ mid2 ++ bot3) := by
  have H := double_split_horiz hbot2 hbot3 hup3 h hm hm3
  rcases H with ⟨k₁, k₂, k_is, k12_is⟩ | ⟨l₁, l₂, l_is, l12_is⟩
  · left
    cases k₂
    · rw [k12_is.1, List.append_nil] at k_is
      rw [k_is]
      rcases hm3 with h1 | ⟨f, m, c, spec⟩
      · rw [h1, List.nil_append, List.append_nil] at k12_is
        rw [h1, List.nil_append]
        use k₁, []
        constructor
        · rw [List.append_nil]
          exact k12_is.1.symm
        rcases hbot3 with h3 | h4
        · exfalso
          cases bot3 with
          | nil =>
            rw [List.nil_append] at k12_is
            rw [← k12_is.2] at hup3
            simp [is_false] at hup3
          | cons head tail =>
            simp at k12_is
            rw [← k12_is.2.1] at h3
            simp [is_true] at h3
        exfalso
        have H : is_false (bot3 ++ up3) := is_false_of_false_false h4 hup3
        rw [← k12_is.2] at H
        simp [is_false] at H
      have H : bot3 = [] := by
        cases bot3 with
        | nil => rfl
        | cons head tail =>
          cases tail with
          | nil =>
            simp [spec] at k12_is
          | cons head2 tail2 =>
            simp [spec] at k12_is
            rcases hbot3 with h3 | h4
            · rw [← k12_is.2.1] at h3
              simp [is_true] at h3
            rw [← k12_is.2.2.1] at h4
            simp [is_false] at h4
      use k₁, bot3
      constructor
      · rw [H, List.append_nil]
        exact k12_is.1.symm
      rw [H, List.append_nil, List.nil_append]
      rw [H, List.nil_append, List.nil_append] at k12_is
      exact k12_is
    rename_i hk tk
    cases bot3
    · use k₁, hk :: tk
      constructor
      · exact k_is
      rw [List.nil_append] at k12_is
      rw [List.append_nil]
      exact k12_is
    rename_i h3 t3
    have : ∃ ender, hk::tk = h3 :: t3 ++ ender := by
      rcases hbot3 with h3 | h4
      · have H := prefix_true h3 k12_is.2
        rcases H with ⟨w, hw⟩
        use w; exact hw.symm
      rcases hm3 with h5 | ⟨f, m ,c, spec⟩
      · have H := is_false_of_false_false h4 hup3
        rw [h5, List.append_nil] at k12_is
        rw [← k12_is.2] at H
        apply is_false_append at H
        have H2 := is_false_append H.1
        simp [is_false] at H2
      rw [spec] at k12_is
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at k12_is
      rw [k12_is.2.1]
      simp only [List.cons_append, List.cons.injEq, true_and]
      rcases prefix_false (is_false_cons h4).2 k12_is.2.2 with ⟨f, spec⟩
      rw [← spec]
      use f
    rcases this with ⟨e, he⟩
    use k₁ ++ h3::t3, e
    constructor
    · rw [List.append_assoc, ← he]
      exact k_is
    constructor
    · rw [k12_is.1]
    rw [he] at k12_is
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq,
      List.append_cancel_left_eq, true_and] at k12_is
    simp [k12_is.2]
  right
  use l₁ ++ bot3
  have : bot3 <+: l₂ := by
    use mid3 ++ up3
    rw [← List.append_assoc]
    exact l12_is.1.symm
  rcases this with ⟨f, spec⟩
  use f
  rw [← spec] at l12_is
  simp only [List.append_assoc, List.append_cancel_left_eq, List.cons_append,
    List.nil_append] at l12_is
  constructor
  · rw [List.append_assoc, spec]
    exact l_is
  constructor
  · exact l12_is.1
  rw [← l12_is.2]
  simp

def add_cell (h : PartialGrid a b bot mid up) (hg : grid_style' i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
    ∃ nb nm nu, PartialGrid a b nb nm nu ∧ nb ++ nm ++ nu = k ++ j ++ l ∧ up <:+ nu ∧ bot <+: nb := by
  rcases grid_style_split hg with ⟨a1, b1, i_is⟩
  rw [i_is] at fe
  induction h generalizing k l with
  | single_grid h =>
    exfalso
    rw [List.append_nil] at fe
    exact over_up_neq_false_true fe
  | empty a b ha ha1 hb hb1 =>
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
              List.singleton_append] at fe
    rcases over_up_splits_at_i ha1 hb1 ha fe with ⟨a1, a2, b1, b2, a_is, b_is, i_is, k_is, l_is⟩
    cases a1 with
    | nil =>
      rw [List.nil_append] at a_is
      rw [a_is] at ha1
      rw [← k_is]
      cases b2 with
      | nil =>
        rw [← l_is, List.append_nil]
        rw [List.append_nil] at b_is
        rw [b_is] at hb
        rw [← a_is,← b_is] at i_is
        rw [List.nil_append]
        rw [← b_is] at hb
        have H := skeleton_one_one hg (by assumption) hb (by assumption) i_is
        rcases H with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix, List.nil_prefix⟩⟩⟩
      | cons head tail =>
        rw [← l_is]
        rw [← k_is, List.nil_append, ← l_is] at fe
        rw [← a_is] at ha1
        have := skeleton_one_cons hg fe b_is ha1 ha hb1 (by rw [← a_is] at i_is; exact i_is)
          (by assumption)
        rcases this with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix, List.nil_prefix⟩⟩⟩
    | cons head tail =>
      cases b2 with
      | nil =>
        rw [← k_is, ← l_is,]
        rw [List.append_nil] at b_is
        have := skeleton_cons_one hg a_is ha1 hb1 i_is (by assumption) b_is hb
        rcases this with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix, List.nil_prefix⟩⟩⟩
      | cons headb tailb =>
        rw [a_is] at ha1
        rw [b_is] at hb1
        have H3 := bool_split (is_false_append ha1).2 (is_true_append hb1).1 i_is
        rw [← k_is, ← l_is, a_is, b_is, H3.1, H3.2]
        have := skeleton_cons_cons hg (is_false_append ha1).1 (is_true_append hb1).2 (by assumption)
        rcases this with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix, List.nil_prefix⟩⟩⟩
  | horizontal_append_one g1 g2 ih1 ih2 =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    rcases big_split_first (bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
    rcases @ih2 k₂ l eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
    use bot2 ++ bot1, mid1, up1
    constructor
    · exact PartialGrid.horizontal_append_one g1 pg1
    constructor
    · simp [k_is, fe1, k₁_is]
    exact ⟨h5, (List.prefix_append_right_inj bot2).mpr h6⟩
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
    have := double_split_horiz (bottom_frontier_is_true g1) (Or.inl (bottom_frontier_is_true g2))
      (right_frontier_is_false g2) fe (middle_frontier_nil_or_caps g1)
      (middle_frontier_nil_or_caps g2)
    rcases this with hl | hr
    · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
      rcases g2_ih k2_is.symm with ⟨bot3, mid3, up3, hpg, hf⟩
      use bot2, mid2 ++ bot3++mid3, up3
      constructor
      · exact PartialGrid.horizontal_append h g1 hpg
      simp [k_is, k1_is, k2_is, hf]
    rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
    have H3 : bot2 ++ mid2 ++ up2 = k ++ [(a1, false), (b1, true)] ++ (l₁ ++ up2) := by
      rw [← l2_is]
      simp
    rcases @g1_ih k (l₁ ++ up2) H3 with ⟨bot4, mid4, up4, hpg, hf, ⟨to_add, spec⟩, h6⟩
    cases mid4 with
    | nil =>
      cases to_add with
      | nil =>
        use bot4 ++ bot3, mid3, up3
        rw [List.nil_append] at spec
        rw [← spec] at hpg
        constructor
        · exact PartialGrid.horizontal_append_one hpg g2
        constructor
        · rw [spec, ← List.append_assoc, List.append_nil] at hf
          apply List.append_cancel_right at hf
          rw [hf, l_is, l1_is]
          simp
        exact ⟨List.suffix_refl up3, List.prefix_of_append h6⟩
      | cons heade taile =>
        use bot4, (heade :: taile) ++ bot3 ++ mid3, up3
        constructor
        · have lf : is_false (heade :: taile) := by
            have H0 : is_false up4 := by exact right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_append H0).1
          have H := PartialGrid.extend_bottom g2 (heade::taile) lf (by simp)
          rw [← spec] at hpg
          have H2 := PartialGrid.horizontal_append_one hpg H
          simp only [List.append_nil, List.cons_append, List.append_assoc] at H2
          simp only [List.cons_append, List.append_assoc]
          exact H2
        constructor
        · rw [l_is, l1_is]
          rw [← spec, ← List.append_assoc, ← List.append_assoc] at hf
          apply List.append_cancel_right at hf
          conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
          simp
        exact ⟨List.suffix_refl up3, h6⟩
    | cons head tail =>
      cases to_add with
      | nil =>
        use bot4, head::tail ++ bot3 ++ mid3, up3
        rw [List.nil_append] at spec
        rw [← spec] at hpg
        constructor
        · exact PartialGrid.horizontal_append (by simp) hpg g2
        constructor
        · rw [spec, ← List.append_assoc] at hf
          change bot4 ++ ([head] ++ tail) ++ up4 = k ++ j ++ l₁ ++ up4 at hf
          rw [← List.append_assoc] at hf
          change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up3 = _
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.append_cancel_right hf]
          simp [l_is, l1_is]
        exact ⟨List.suffix_refl up3, h6⟩
      | cons heade taile =>
        use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up3
        constructor
        · have lf : is_false (heade :: taile) := by
            have H0 : is_false up4 := right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_append H0).1
          rw [← spec] at hpg
          have H2 := PartialGrid.horizontal_append (by simp) hpg
            (PartialGrid.extend_bottom g2 (heade::taile) lf (by simp))
          simp only [List.append_nil, List.cons_append, List.append_assoc] at H2
          simp only [List.cons_append, List.append_assoc]
          exact H2
        constructor
        · rw [l_is, l1_is]
          rw [← spec, ← List.append_assoc, ← List.append_assoc] at hf
          apply List.append_cancel_right at hf
          conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
          simp
        exact ⟨List.suffix_refl up3, h6⟩
  | vertical_append_one g1 g2 ih1 ih2 =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
      rcases @ih2 _ _ eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
      use bot1, mid1, up1 ++ up2
      constructor
      · exact PartialGrid.vertical_append_one g1 pg1
      constructor
      · rw [l_is, l₂_is, ← List.append_assoc, fe1, ← List.append_assoc]
      exact ⟨List.suffix_append_right h5, h6⟩
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a b bot mid up a2 bot2 mid2 up2
    have := double_split_horiz' (bottom_frontier_is_true g2) (Or.inr (right_frontier_is_false g2))
      (right_frontier_is_false g1) fe (middle_frontier_nil_or_caps g2) (middle_frontier_nil_or_caps g1)
    rcases this with ⟨k1, k2, k_is, k1_is, k2_is⟩ | ⟨l1, l2, l_is, l1_is, l2_is⟩
    · specialize @g1_ih (bot ++ k2) l (by rw [List.append_assoc, ← k2_is]; simp)
      rcases g1_ih with ⟨nb, nm, nu, pg, fe', upp, botp⟩
      rcases botp with ⟨to_add, spec⟩
      cases to_add with
      | nil =>
        rw [List.append_nil] at spec
        rw [← spec] at pg
        rw [spec] at fe'
        cases nm with
        | nil =>
          use bot2, mid2, up2++nu
          constructor
          · exact PartialGrid.vertical_append_one pg g2
          simp only [List.append_nil, List.append_assoc, List.append_cancel_left_eq] at fe'
          constructor
          · rw [fe', k_is, k1_is]
            simp
          exact ⟨suffix_of_append upp, List.prefix_rfl⟩
        | cons head tail =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          constructor
          · exact PartialGrid.vertical_append pg g2 (by simp)
          constructor
          · rw [k_is]
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            conv => rhs; rw [List.append_assoc, List.append_assoc, ← fe', k1_is]
            simp
          exact ⟨upp, List.prefix_rfl⟩
      | cons head tail =>
        cases nm with
        | nil =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          constructor
          · have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec] at H
              exact (is_true_append H).2
            have H2 := (extend_side g2 (head::tail) H1 (by simp))
            rw [spec] at H2
            exact PartialGrid.vertical_append_one pg H2
          constructor
          · rw [← spec] at fe'
            simp only [List.append_nil, List.append_assoc, List.cons_append,
              List.append_cancel_left_eq] at fe'
            simp [k_is, k1_is, spec, fe']
          exact ⟨upp, List.prefix_rfl⟩
        | cons head1 tail1 =>
          use bot2, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
          constructor
          · have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec] at H
              exact (is_true_append H).2
            have H2 := (extend_side g2 (head::tail) H1 (by simp))
            rw [spec] at H2
            have H := PartialGrid.vertical_append pg H2 (by simp)
            rw [List.append_nil] at H
            exact H
          constructor
          · rw [← spec] at fe'
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            simp [k_is, k1_is, spec, fe']
          exact ⟨upp, List.prefix_rfl⟩
    rw [← l2_is] at g2_ih
    rcases @g2_ih k l1 (by simp) with ⟨nb, nm, nu, pg, fe', upp, botp⟩
    use nb, nm ++ nu ++mid, up
    constructor
    · exact PartialGrid.vertical_append g1 pg h
    constructor
    · rw [l_is, l1_is, ← List.append_assoc, ← List.append_assoc, fe', ← List.append_assoc, ← List.append_assoc]
    exact ⟨List.suffix_refl up, botp⟩

theorem step_two (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b) (hb1 : b.length > 0) :
    SemiThue grid_style' (a ++ b) c → (∃ bot mid up, PartialGrid a b bot mid up ∧ bot ++ mid ++ up = c) := by
  intro h
  generalize ell : a ++ b = el at h
  induction one_step_equiv_reg.mp h with
  | refl x =>
    rw [← ell]
    use [], a ++ b, []
    constructor
    · exact PartialGrid.empty _ _ ha1 ha hb1 hb
    rw [List.append_nil, List.nil_append]
  | one_step h1 h2 ih =>
    rcases ih ell (one_step_equiv_reg.mpr h1) with ⟨bot, mid, up, h3, h4⟩
    rcases add_cell h3 h2 h4 with ⟨b, m, u, h3, h4⟩
    use b, m, u
    exact ⟨h3, h4.1⟩
