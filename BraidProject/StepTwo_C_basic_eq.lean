import BraidProject.PartialGrids_C
import BraidProject.StepOne_C_basic_eq
import Mathlib.Data.List.Infix
import BraidProject.SpecificConstructiveThings

noncomputable def grid_style_split (h : grid_style i j) : Σ a b, PLift (i = [(a, false), (b, true)]) := by
  induction h with
  | basic =>
    rename_i n
    use n, n
    exact {down := rfl}
  | over =>
    rename_i n
    use n, none
    exact {down := rfl}
  | up =>
    rename_i n
    use none, n
    exact {down := rfl}
  | empty =>
    use none, none
    exact {down := rfl}
  | apart h =>
    rename_i i j
    use i, j
    exact {down := rfl}
  | close h =>
    rename_i i j
    use i, j
    exact {down := rfl}

noncomputable def grid_rel_means (h : grid_style i j) : Σ a b c d,
    cell (option_to_cell a) (option_to_cell b) c d × PLift (i = [(a, false), (b, true)] ∧ j = to_over d ++ to_up c) := by
  cases h with
  | basic n =>
    use some n, some n, [], []
    exact ⟨cell.top_left n, {down := ⟨rfl, rfl⟩}⟩
  | over n =>
    use some n, none, [n], []
    exact ⟨cell.sides n, {down := ⟨rfl, rfl⟩}⟩
  | up n =>
    use none, some n, [], [n]
    exact ⟨cell.top_bottom n, {down := ⟨rfl, rfl⟩}⟩
  | empty =>
    use none, none, [], []
    exact ⟨cell.empty, {down := ⟨rfl, rfl⟩}⟩
  | apart h =>
    rename_i i j
    use some i, some j, [i], [j]
    exact ⟨cell.separated i j (or_dist_iff.mp h), {down := ⟨rfl, rfl⟩}⟩
  | close h =>
    rename_i i j
    use some i, some j, [i, j], [j, i]
    exact ⟨cell.adjacent i j h, {down := ⟨rfl, rfl⟩}⟩

noncomputable def skeleton_one_one (h : grid_style i j) (ha : a.length > 0) (hb : b.length > 0)
    (i_is : i = [(a3, false), (b3, true)]) (ab : [(a3, false), (b3, true)] = a ++ b) :
    Σ bot mid up, PartialGrid a b bot mid up × PLift (bot ++ mid ++ up = j) := by
  rcases grid_rel_means h with ⟨a1, b1, c1, d1, h_cell, i_is', j_is⟩
  use to_over d1, [], to_up c1
  have ab_is := List.append_eq_len_two ha hb ab.symm
  rw [ab_is.1, ab_is.2]
  change _ = [(a3, false)] ++ [(b3, true)] at i_is
  rw [i_is'] at i_is
  have happ := List.append_eq_len_two (by simp) (by simp) i_is.symm
  rw [happ.1, happ.2]
  constructor
  · rw [← over_oc, ← up_oc]
    exact PartialGrid.single_gridt h_cell
  rw [List.append_nil]
  exact {down := j_is.symm}

theorem grid_style_includes_true (h : grid_style i j) : (∀ (a : Option ℕ), (a, true) ∉ i) → False := by
  rcases grid_rel_means h with ⟨a1, b1, c1, d1, _, ⟨i_is, _⟩⟩
  intro h
  specialize h b1
  rw [i_is] at h
  simp at h

noncomputable def skeleton_one_cons (h2 : grid_style i j) (fe : a ++ b = ([(a3, false), (b3, true)] ++ head :: tail))
    (b_is : b = b1 ++ head :: tail) (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b)
    (ab_is : [(a3, false), (b3, true)] = a ++ b1) (i_is : i = [(a3, false), (b3, true)]):
    Σ bot mid up, PartialGrid a b bot mid up × PLift (bot ++ mid ++ up = [] ++ j ++ head :: tail) := by
  have ht_true : is_true (head :: tail) := by
    rw [b_is] at hb
    exact (is_true_append hb).2
  rcases grid_rel_means h2 with ⟨a2, b2, c2, d2, h_cell, i_is', j_is⟩
  use to_over d2, to_up c2 ++ head :: tail, []
  constructor
  · have H2 := PartialGrid.empty (to_up c2) (head :: tail) (by simp [to_up_len_pos]) is_false_up (by simp) ht_true
    have H3 := PartialGrid.horizontal_append_one (PartialGrid.single_gridt h_cell) H2
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
  exact {down := by simp}

noncomputable def skeleton_cons_one (h2 : grid_style i j) (a_is : a = head :: tail ++ a2)
    (ha : is_false a) (hb : is_true b) (ab_is : [(a3, false), (b3, true)] = a2 ++ b1)
    (i_is : i = [(a3, false), (b3, true)]) (b_is : b = b1) (hb1 : b.length > 0) :
    Σ bot mid up, PartialGrid a b bot mid up × PLift (bot ++ mid ++ up = head :: tail ++ j ++ []) := by
  rcases grid_rel_means h2 with ⟨a5, b2, c2, d2, h_cell, i_is', j_is⟩
  have ht_false : is_false (head :: tail) := by
    rw [a_is] at ha
    exact (is_false_append ha).1
  have H2 := PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos]) ht_false (by simp [to_over_len_pos]) is_true_over
  have H3 := PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell) H2
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
  exact {down := by simp}

noncomputable def skeleton_cons_cons (gs : grid_style i j) (ha : is_false (head :: tail)) (hb : is_true (headb :: tailb))
    (i_is : i = [(a3, false), (b3, true)]) :
    Σ bot mid up, PartialGrid (head :: tail ++ [(a3, false)]) ([(b3, true)] ++ headb :: tailb) bot mid up ×
    PLift (bot ++ mid ++ up = head :: tail ++ j ++ headb :: tailb) := by
  rcases grid_rel_means gs with ⟨a5, b2, c2, d2, h_cell,  i_is', j_is⟩
  use [], head :: tail ++ to_over d2 ++ to_up c2 ++ headb :: tailb, []
  constructor
  · have H2 := PartialGrid.empty (head :: tail) (to_over d2) (by simp) ha (by simp [to_over_len_pos]) is_true_over
    have H3 := PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell) H2
    have H4 := PartialGrid.empty (to_up c2) (headb :: tailb) to_up_len_pos is_false_up (by simp) hb
    have H5 := PartialGrid.horizontal_append (by simp) H3 H4
    rw [List.append_nil] at H5
    have hi := i_is.symm.trans i_is'
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hi
    rw [← hi.1, up_oc, ← hi.2, over_oc] at H5
    simp only [List.cons_append, List.singleton_append, List.append_assoc]
    simp only [List.cons_append, List.singleton_append, List.append_assoc] at H5
    exact H5
  exact {down := by simp [j_is]}


open PartialGrid

noncomputable def add_cell (h : PartialGrid a b bot mid up) (hg : grid_style i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
    Σ nb nm nu, PartialGrid a b nb nm nu × PLift (nb ++ nm ++ nu = k ++ j ++ l) × List.Suffix' up nu × List.Prefix' bot nb := by
  rcases grid_style_split hg with ⟨a1, b1, ⟨i_is⟩⟩
  rw [i_is] at fe
  induction h generalizing k l with
  | single_gridt h =>
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
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix_C, List.nil_prefix_C⟩⟩⟩
      | cons head tail =>
        rw [← l_is]
        rw [← k_is, List.nil_append, ← l_is] at fe
        rw [← a_is] at ha1
        have := skeleton_one_cons hg fe b_is ha1 ha hb1 (by rw [← a_is] at i_is; exact i_is)
          (by assumption)
        rcases this with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix_C, List.nil_prefix_C⟩⟩⟩
    | cons head tail =>
      cases b2 with
      | nil =>
        rw [← k_is, ← l_is,]
        rw [List.append_nil] at b_is
        have := skeleton_cons_one hg a_is ha1 hb1 i_is (by assumption) b_is hb
        rcases this with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix_C, List.nil_prefix_C⟩⟩⟩
      | cons headb tailb =>
        rw [a_is] at ha1
        rw [b_is] at hb1
        have H3 := bool_split (is_false_append ha1).2 (is_true_append hb1).1 i_is
        rw [← k_is, ← l_is, a_is, b_is, H3.1, H3.2]
        have := skeleton_cons_cons hg (is_false_append ha1).1 (is_true_append hb1).2 (by assumption)
        rcases this with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix_C, List.nil_prefix_C⟩⟩⟩
  | horizontal_append_one g1 g2 ih1 ih2 =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    rcases big_split_first (bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
    rcases @ih2 k₂ l eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
    use bot2 ++ bot1, mid1, up1
    constructor
    · exact PartialGrid.horizontal_append_one g1 pg1
    constructor
    · simp [k_is, k₁_is, fe]
      simp at fe1
      exact fe1
    exact ⟨h5, (List.prefix_append_right_inj_C).2 h6⟩
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
    have := double_split_horiz (bottom_frontier_is_true g1) (Sum.inl (bottom_frontier_is_true g2))
      (right_frontier_is_false g2) fe (middle_frontier_nil_or_caps g1)
      (middle_frontier_nil_or_caps g2)
    rcases this with hl | hr
    · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
      rcases g2_ih k2_is.symm with ⟨bot3, mid3, up3, hpg, hf⟩
      use bot2, mid2 ++ bot3++mid3, up3
      constructor
      · exact PartialGrid.horizontal_append h g1 hpg
      simp [k_is, k1_is, k2_is, hf.1.1]
      constructor
      · exact ⟨trivial⟩
      constructor
      · exact hf.2.1
      exact bot2.prefix_refl_C
    rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
    have H3 : bot2 ++ mid2 ++ up2 = k ++ [(a1, false), (b1, true)] ++ (l₁ ++ up2) := by
      rw [← l2_is]
      simp
    have H := @g1_ih k (l₁ ++ up2) H3
    rcases @g1_ih k (l₁ ++ up2) H3 with ⟨bot4, mid4, up4, hpg, ⟨hf⟩, ⟨to_add, ⟨spec⟩⟩, back2, ⟨h6⟩⟩
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
          exact ⟨by simp⟩
        constructor
        · exact List.suffix_refl_C
        rw [← h6]
        have H : bot2 = bot2 ++ [] := by simp
        nth_rewrite 1 [H]
        rw [List.append_assoc]
        exact List.prefix_append_right_inj_C.2 List.nil_prefix_C
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
          conv => rhs; rw [← List.append_assoc, ← List.append_assoc (k ++ j), ← hf]
          exact ⟨by simp⟩
        rw [← h6]
        have H : bot2 = bot2 ++ [] := by simp
        nth_rewrite 1 [H]
        exact ⟨List.suffix_refl_C, List.prefix_append_right_inj_C.2 List.nil_prefix_C⟩
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
          constructor
          change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up3 = _
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.append_cancel_right hf]
          simp [l_is, l1_is]
        rw [← h6]
        exact ⟨List.suffix_refl_C, List.prefix_append_self_C⟩
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
          constructor
          conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
          simp
        rw [← h6]
        exact ⟨List.suffix_refl_C, List.prefix_append_self_C⟩
  | vertical_append_one g1 g2 ih1 ih2 =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
      rcases @ih2 _ _ eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
      use bot1, mid1, up1 ++ up2
      constructor
      · exact PartialGrid.vertical_append_one g1 pg1
      constructor
      · constructor
        rw [l_is, l₂_is, ← List.append_assoc, fe1.1, ← List.append_assoc]
      exact ⟨List.suffix_append_right_C h5, h6⟩
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a b bot mid up a2 bot2 mid2 up2
    have := double_split_horiz' (bottom_frontier_is_true g2) (Sum.inr (right_frontier_is_false g2))
      (right_frontier_is_false g1) fe (middle_frontier_nil_or_caps g2) (middle_frontier_nil_or_caps g1)
    rcases this with ⟨k1, k2, k_is, k1_is, k2_is⟩ | ⟨l1, l2, l_is, l1_is, l2_is⟩
    · specialize @g1_ih (bot ++ k2) l (by rw [List.append_assoc, ← k2_is]; simp)
      rcases g1_ih with ⟨nb, nm, nu, pg, fe', upp, botp⟩
      rcases botp with ⟨to_add, spec⟩
      cases to_add with
      | nil =>
        rw [List.append_nil] at spec
        rw [← spec.1] at pg
        rw [spec.1] at fe'
        cases nm with
        | nil =>
          use bot2, mid2, up2++nu
          constructor
          · exact PartialGrid.vertical_append_one pg g2
          simp only [List.append_nil, List.append_assoc, List.append_cancel_left_eq] at fe'
          constructor
          · constructor
            rw [fe'.1, k_is, k1_is]
            simp
          rcases upp with ⟨t, ⟨ht⟩⟩
          exact ⟨by use up2 ++ t; exact ⟨by simp [ht]⟩ , List.prefix_refl_C⟩
        | cons head tail =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          constructor
          · exact PartialGrid.vertical_append pg g2 (by simp)
          constructor
          · rw [k_is]
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            constructor
            conv => rhs; rw [List.append_assoc, List.append_assoc, ← fe'.1, k1_is]
            simp
          exact ⟨upp, List.prefix_refl_C⟩
      | cons head tail =>
        cases nm with
        | nil =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          constructor
          · have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec.1] at H
              exact (is_true_append H).2
            have H2 := (extend_side g2 (head::tail) H1 (by simp))
            rw [spec.1] at H2
            exact PartialGrid.vertical_append_one pg H2
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_nil, List.append_assoc, List.cons_append,
              List.append_cancel_left_eq] at fe'
            constructor
            simp [k_is, k1_is, spec.1, fe'.1]
          exact ⟨upp, List.prefix_refl_C⟩
        | cons head1 tail1 =>
          use bot2, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
          constructor
          · have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec.1] at H
              exact (is_true_append H).2
            have H2 := (extend_side g2 (head::tail) H1 (by simp))
            rw [spec.1] at H2
            have H := PartialGrid.vertical_append pg H2 (by simp)
            rw [List.append_nil] at H
            exact H
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            constructor
            simp [k_is, k1_is, spec.1, fe'.1]
          exact ⟨upp, List.prefix_refl_C⟩
    rw [← l2_is] at g2_ih
    rcases @g2_ih k l1 (by simp) with ⟨nb, nm, nu, pg, fe', upp, botp⟩
    use nb, nm ++ nu ++mid, up
    constructor
    · exact PartialGrid.vertical_append g1 pg h
    constructor
    · constructor
      rw [l_is, l1_is, ← List.append_assoc, ← List.append_assoc, fe'.1, ← List.append_assoc, ← List.append_assoc]
    exact ⟨List.suffix_refl_C, botp⟩

noncomputable def step_two (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b) (hb1 : b.length > 0) :
    SemiThue grid_style (a ++ b) c → (Σ bot mid up, PartialGrid a b bot mid up × PLift (bot ++ mid ++ up = c)) := by
  intro h
  generalize ell : a ++ b = el at h
  induction one_step_equiv_reg.1 h with
  | refl x =>
    rw [← ell]
    use [], a ++ b, []
    constructor
    · exact PartialGrid.empty _ _ ha1 ha hb1 hb
    rw [List.append_nil, List.nil_append]
    exact {down := rfl}
  | one_step h1 h2 ih =>
    rcases ih ell (one_step_equiv_reg.2 h1) with ⟨bot, mid, up, h3, ⟨h4⟩⟩
    rcases add_cell h3 h2 h4 with ⟨b, m, u, h3, h4⟩
    use b, m, u
    exact ⟨h3, h4.1⟩

theorem to_option_length : (to_option a).length = a.length := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    simp [to_option]

-- noncomputable def PartialGrid.length : PartialGrid a b c d e → ℕ := by
--   intro h
--   match h with
--   | single_gridt h =>
--     cases h with
--     | empty => exact 0
--     | top_bottom i => exact 0
--     | sides i => exact 0
--     | top_left i => exact 1
--     | adjacent i k h => exact 1
--     | separated i j h => exact 1
--   | empty a b ha ha1 hb _ => exact 0
--   | horizontal_append_one g1 g2 => exact PartialGrid.length g1 + PartialGrid.length g2
--   | horizontal_append h g1 g2  => exact PartialGrid.length g1 + PartialGrid.length g2
--   | vertical_append_one g1 g2  => exact PartialGrid.length g1 + PartialGrid.length g2
--   | vertical_append g1 g2 h  => exact PartialGrid.length g1 + PartialGrid.length g2

noncomputable def chain_length (h : SemiThue reversing (a1 ++ a2) (b1 ++ b2))
  (ha1 : is_false a1) (a1_len : a1.length >0) (ha2 : is_true a2) (a2_len : a2.length > 0) (hb1 : is_true b1) (hb2 : is_false b2) : ℕ := by
  have H := stepOne h (by use a1, a2; exact ⟨ha1, ⟨ha2, ⟨rfl⟩⟩⟩)
      (by use b1, b2; exact ⟨hb1, ⟨hb2, ⟨rfl⟩⟩⟩)
  rcases H with ⟨c, spec1, spec2, spec3, spec35⟩
  unfold to_option at spec1
  simp [List.map_append] at spec1
  change SemiThue grid_style (to_option a1 ++ to_option a2) c at spec1
  rw [← to_option_length] at a1_len
  rw [← to_option_length] at a2_len
  rcases step_two (is_false_to_option ha1) a1_len (is_true_to_option ha2) a2_len spec1 with ⟨bot, mid, up, pg, c_is⟩
  exact PartialGrid.length pg


-- theorem first_chain (h : SemiThue reversing (a1 ++ a2) (b1 ++ b2))
--   (ha1 : is_false a1) (a1_len : a1.length >0) (ha2 : is_true a2) (a2_len : a2.length > 0) (hb1 : is_true b1) (hb2 : is_false b2) : False := by
--   have H := stepOne h ⟨a1, ⟨a2, ⟨ha1, ⟨ha2, ⟨rfl⟩⟩⟩⟩⟩ ⟨b1, ⟨b2, ⟨hb1, ⟨hb2, ⟨rfl⟩⟩⟩⟩⟩
--   rcases H with ⟨c, spec1, spec2, spec3, spec35⟩
--   unfold to_option at spec1
--   simp [List.map_append] at spec1
--   change SemiThue grid_style (to_option a1 ++ to_option a2) c at spec1
--   rw [← to_option_length] at a1_len
--   rw [← to_option_length] at a2_len
--   rcases step_two (is_false_to_option ha1) a1_len (is_true_to_option ha2) a2_len spec1 with ⟨bot, mid, up, pg, c_is⟩
--   rcases spec3 with ⟨c1, c2, spec4, spec5, c_is'⟩
--   have H : mid = [] := by sorry
--   rw [H] at pg
--   have bot_is : bot = c1 := by sorry
--   have up_is : up = c2 := by sorry
--   apply gridt_of_PartialGrid at pg
--   rw [bot_is, up_is] at pg
--   simp [gridt_option] at pg
--   sorry

-- theorem second_chain (h : SemiThue reversing (a1 ++ a2) c)
--   (ha1 : is_false a1) (a1_len : a1.length >0) (ha2 : is_true a2) (a2_len : a2.length > 0) : False := by
--   have H := stepOne_mid h ⟨a1, ⟨a2, ⟨ha1, ⟨ha2, ⟨rfl⟩⟩⟩⟩⟩
--   rcases H with ⟨c, spec1, spec2⟩
--   unfold to_option at spec1
--   simp [List.map_append] at spec1
--   change SemiThue grid_style (to_option a1 ++ to_option a2) c at spec1
--   rw [← to_option_length] at a1_len
--   rw [← to_option_length] at a2_len
--   rcases step_two (is_false_to_option ha1) a1_len (is_true_to_option ha2) a2_len spec1 with ⟨bot, mid, up, pg, c_is⟩
--   have H : mid = [] := by sorry
--   rw [H] at pg
--   have bot_is : bot = c1 := by sorry
--   have up_is : up = c2 := by sorry
--   apply grid_of_PartialGrid at pg
--   rw [bot_is, up_is] at pg
--   simp [grid_option] at pg
--   sorry
--theorem grid_of_PartialGrid (h : PartialGrid a b d [] c) : grid_option a b c d :=
