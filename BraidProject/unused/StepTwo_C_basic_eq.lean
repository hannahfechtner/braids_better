import BraidProject.PartialGrid.Basic
import BraidProject.StepOne
import Mathlib.Data.List.Infix
import BraidProject.SpecificConstructiveThings

open Braid GridData

def grid_style_to_cell (h : grid_style i j) : Σ a b c d,
    CellData (option_to_list a) (option_to_list b) c d ×
    PLift (i = [(a, false), (b, true)] ∧ j = to_horizontal_edge c ++ to_vertical_edge d) := by
  match h with
  | grid_style.basic n =>
    use some n, some n, [], []
    exact ⟨CellData.top_left n, {down := ⟨rfl, rfl⟩}⟩
  | grid_style.over n =>
    use some n, none, [], [n]
    exact ⟨CellData.sides n, {down := ⟨rfl, rfl⟩}⟩
  | grid_style.up n =>
    use none, some n, [n], []
    exact ⟨CellData.top_bottom n, {down := ⟨rfl, rfl⟩}⟩
  | grid_style.empty =>
    use none, none, [], []
    exact ⟨CellData.empty, {down := ⟨rfl, rfl⟩}⟩
  | grid_style.apart h =>
    rename_i i j
    use some i, some j, [j], [i]
    exact ⟨CellData.separated i j h, {down := ⟨rfl, rfl⟩}⟩
  | grid_style.close h =>
    rename_i i j
    use some i, some j, [j, i], [i, j]
    exact ⟨CellData.adjacent i j h, {down := ⟨rfl, rfl⟩}⟩

noncomputable def skeleton_one_one (h : grid_style i j) (ha : a.length > 0) (hb : b.length > 0)
    (i_is : i = [(a3, false), (b3, true)]) (ab : [(a3, false), (b3, true)] = a ++ b) :
    Σ bot mid up, PartialGrid a b bot mid up × PLift (bot ++ mid ++ up = j) := by
  rcases grid_style_to_cell h with ⟨a1, b1, c1, d1, h_cell, i_is', j_is⟩
  use to_horizontal_edge c1, [], to_vertical_edge d1
  have ab_is := List.append_eq_len_two ha hb ab.symm
  rw [ab_is.1, ab_is.2]
  change _ = [(a3, false)] ++ [(b3, true)] at i_is
  rw [i_is'] at i_is
  have happ := List.append_eq_len_two (by simp) (by simp) i_is.symm
  rw [happ.1, happ.2]
  constructor
  · rw [← to_horizontal_edge_option_to_list, ← to_vertical_edge_option_to_list]
    exact PartialGrid.single_cell h_cell
  rw [List.append_nil]
  exact {down := j_is.symm}

open SignedList
noncomputable def skeleton_one_cons (h2 : grid_style i j) (fe : a ++ b = ([(a3, false), (b3, true)] ++ head :: tail))
    (b_is : b = b1 ++ head :: tail) (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b)
    (ab_is : [(a3, false), (b3, true)] = a ++ b1) (i_is : i = [(a3, false), (b3, true)]):
    Σ bot mid up, PartialGrid a b bot mid up × PLift (bot ++ mid ++ up = [] ++ j ++ head :: tail) := by
  have ht_true : is_true (head :: tail) := by
    rw [b_is] at hb
    exact (is_true_of_append hb).2
  rcases grid_style_to_cell h2 with ⟨a2, b2, c2, d2, h_cell, i_is', j_is⟩
  use to_horizontal_edge c2, to_vertical_edge d2 ++ head :: tail, []
  constructor
  · have H2 := PartialGrid.empty (to_vertical_edge d2) (head :: tail) (by simp [to_vertical_edge_length_pos]) is_false_to_vertical_edge (by simp) ht_true
    have H3 := PartialGrid.horizontal_append_one (PartialGrid.single_cell h_cell) H2
    simp only [to_vertical_edge_option_to_list, to_horizontal_edge_option_to_list, List.singleton_append, List.append_nil] at H3
    have helper := i_is.symm.trans i_is'
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at helper
    have ha : a = [(a2, false)] := by
      rw [← helper.1]
      exact eq_left_singleton_of_is_false_append_eq_unfinished_cell ha1 ha (id (Eq.symm ab_is))
    have hb : b = (b2, true) :: head :: tail := by
      rw [← helper.2]
      rw [ha] at fe
      simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq, and_true] at fe
      exact fe.2
    rw [ha, hb]
    exact H3
  rw [j_is]
  exact {down := by simp}

noncomputable def skeleton_cons_one (h2 : grid_style i j) (a_is : a = head :: tail ++ a2)
    (ha : is_false a) (hb : is_true b) (ab_is : [(a3, false), (b3, true)] = a2 ++ b1)
    (i_is : i = [(a3, false), (b3, true)]) (b_is : b = b1) (hb1 : b.length > 0) :
    Σ bot mid up, PartialGrid a b bot mid up × PLift (bot ++ mid ++ up = head :: tail ++ j ++ []) := by
  rcases grid_style_to_cell h2 with ⟨a5, b2, c2, d2, h_cell, i_is', j_is⟩
  have ht_false : is_false (head :: tail) := by
    rw [a_is] at ha
    exact (is_false_of_append ha).1
  have H2 := PartialGrid.empty (head :: tail) (to_horizontal_edge c2) (by simp) ht_false (by simp [to_horizontal_edge_length_pos]) is_true_to_horizontal_edge
  have H3 := PartialGrid.vertical_append_one (PartialGrid.single_cell h_cell) H2
  use [], head::tail ++ to_horizontal_edge c2, to_vertical_edge d2
  constructor
  · rw [a_is]
    have H := i_is.symm.trans i_is'
    simp at H
    rw [List.nil_append, to_vertical_edge_option_to_list, to_horizontal_edge_option_to_list, ← H.1, ← H.2] at H3
    have H2 : b = [(b3, true)] := by
      rw [b_is]
      rw [b_is] at hb1
      rw [b_is] at hb
      exact eq_right_singleton_of_is_true_append_eq_unfinished_cell hb1 hb (id (Eq.symm ab_is))
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
  rcases grid_style_to_cell gs with ⟨a5, b2, c2, d2, h_cell,  i_is', j_is⟩
  use [], head :: tail ++ to_horizontal_edge c2 ++ to_vertical_edge d2 ++ headb :: tailb, []
  constructor
  · have H2 := PartialGrid.empty (head :: tail) (to_horizontal_edge c2) (by simp) ha (by simp [to_horizontal_edge_length_pos]) is_true_to_horizontal_edge
    have H3 := PartialGrid.vertical_append_one (PartialGrid.single_cell h_cell) H2
    have H4 := PartialGrid.empty (to_vertical_edge d2) (headb :: tailb) to_vertical_edge_length_pos is_false_to_vertical_edge (by simp) hb
    have H5 := PartialGrid.horizontal_append H3 H4 (by simp)
    rw [List.append_nil] at H5
    have hi := i_is.symm.trans i_is'
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hi
    rw [← hi.1, to_vertical_edge_option_to_list, ← hi.2, to_horizontal_edge_option_to_list] at H5
    simp only [List.cons_append, List.append_assoc]
    simp only [List.cons_append, List.append_assoc] at H5
    exact H5
  exact {down := by simp [j_is]}


open PartialGrid

noncomputable def add_cell (h : PartialGrid a b bot mid up) (hg : grid_style i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
    Σ nb nm nu, PartialGrid a b nb nm nu × PLift (nb ++ nm ++ nu = k ++ j ++ l) × List.SuffixData up nu × List.PrefixData bot nb := by
  rcases grid_style_spec hg with ⟨a1, b1, ⟨i_is⟩⟩
  rw [i_is] at fe
  induction h generalizing k l with
  | single_cell h =>
    exfalso
    rw [List.append_nil] at fe
    exact not_false_true_infix_horizontal_vertical_edge fe
  | empty a b ha ha1 hb hb1 =>
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append] at fe
    obtain ⟨a_eq, b_eq⟩ := over_up_splits_at_i' ha1 hb1 ha fe
    cases k with
    | nil =>
      rw [List.nil_append] at a_eq
      cases l with
      | nil =>
        have ab_is : [(a1, false), (b1, true)] = a ++ b := by rw [a_eq, b_eq]; rfl
        rcases skeleton_one_one hg ha hb i_is ab_is with ⟨nb, nm, nu, h3, h4⟩
        refine ⟨nb, nm, nu, h3, ?_, List.SuffixData.nil, List.PrefixData.nil⟩
        rw [List.nil_append, List.append_nil]
        exact h4
      | cons head tail =>
        have fe_new : a ++ b = [(a1, false), (b1, true)] ++ head :: tail := by
          rw [a_eq, b_eq]; rfl
        have b_split : b = [(b1, true)] ++ head :: tail := b_eq
        have ab_is : [(a1, false), (b1, true)] = a ++ [(b1, true)] := by rw [a_eq]; rfl
        rcases skeleton_one_cons hg fe_new b_split ha1 ha hb1 ab_is i_is with ⟨nb, nm, nu, h3, h4⟩
        exact ⟨nb, nm, nu, h3, h4, List.SuffixData.nil, List.PrefixData.nil⟩
    | cons head tail =>
      cases l with
      | nil =>
        have b_eq' : b = [(b1, true)] := b_eq
        have ab_is : [(a1, false), (b1, true)] = [(a1, false)] ++ [(b1, true)] := rfl
        rcases skeleton_cons_one hg a_eq ha1 hb1 ab_is i_is b_eq' hb with ⟨nb, nm, nu, h3, h4⟩
        exact ⟨nb, nm, nu, h3, h4, List.SuffixData.nil, List.PrefixData.nil⟩
      | cons headb tailb =>
        have ht_false : is_false (head :: tail) := by
          rw [a_eq] at ha1; exact (is_false_of_append ha1).1
        have hb_true : is_true (headb :: tailb) := by
          rw [b_eq] at hb1; exact is_true_tail hb1
        rw [a_eq, b_eq]
        rcases skeleton_cons_cons hg ht_false hb_true i_is with ⟨nb, nm, nu, h3, h4⟩
        exact ⟨nb, nm, nu, h3, h4, List.SuffixData.nil, List.PrefixData.nil⟩
  | horizontal_append_one g1 g2 ih1 ih2 =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    rcases big_split_first (bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
    rcases @ih2 k₂ l eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
    use bot2 ++ bot1, mid1, up1
    constructor
    · exact PartialGrid.horizontal_append_one g1 pg1
    constructor
    · simp only [List.append_assoc, k_is, k₁_is, List.append_cancel_left_eq]
      simp only [List.append_assoc] at fe1
      exact fe1
    exact (h5, h6.append_left)
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
    have := double_split_horiz (bottom_frontier_is_true g1) (Sum.inl ⟨(bottom_frontier_is_true g2)⟩)
      (right_frontier_is_false g2) fe (middle_frontier_spec g1)
      (middle_frontier_spec g2)
    rcases this with hl | hr
    · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
      rcases g2_ih k2_is.symm with ⟨bot3, mid3, up3, hpg, hf⟩
      use bot2, mid2 ++ bot3++mid3, up3
      constructor
      · exact PartialGrid.horizontal_append g1 hpg h
      simp only [List.append_assoc, hf.1.1, k_is, k1_is]
      exact ({ down := trivial }, hf.2.1, List.PrefixData.refl)
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
        · exact List.SuffixData.refl
        rw [← h6]
        have H : bot2 = bot2 ++ [] := by simp
        nth_rewrite 1 [H]
        rw [List.append_assoc]
        exact List.PrefixData.append_left List.PrefixData.nil
      | cons heade taile =>
        use bot4, (heade :: taile) ++ bot3 ++ mid3, up3
        constructor
        · have lf : is_false (heade :: taile) := by
            have H0 : is_false up4 := by exact right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_of_append H0).1
          have H := PartialGrid.extend_left_side g2 (heade::taile) lf (by simp)
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
        exact ⟨List.SuffixData.refl, List.PrefixData.append_left List.PrefixData.nil⟩
    | cons head tail =>
      cases to_add with
      | nil =>
        use bot4, head::tail ++ bot3 ++ mid3, up3
        rw [List.nil_append] at spec
        rw [← spec] at hpg
        constructor
        · exact PartialGrid.horizontal_append hpg g2 (by simp)
        constructor
        · rw [spec, ← List.append_assoc] at hf
          change bot4 ++ ([head] ++ tail) ++ up4 = k ++ j ++ l₁ ++ up4 at hf
          rw [← List.append_assoc] at hf
          constructor
          change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up3 = _
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.append_cancel_right hf]
          simp [l_is, l1_is]
        rw [← h6]
        exact ⟨List.SuffixData.refl, List.PrefixData.append_self⟩
      | cons heade taile =>
        use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up3
        constructor
        · have lf : is_false (heade :: taile) := by
            have H0 : is_false up4 := right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_of_append H0).1
          rw [← spec] at hpg
          have H2 := PartialGrid.horizontal_append hpg
            (PartialGrid.extend_left_side g2 (heade::taile) lf (by simp)) (by simp)
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
        exact ⟨List.SuffixData.refl, List.PrefixData.append_self⟩
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
      exact ⟨List.SuffixData.append_right h5, h6⟩
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a b bot mid up a2 bot2 mid2 up2
    have := double_split_horiz' (bottom_frontier_is_true g2) (Sum.inr ⟨right_frontier_is_false g2⟩)
      (right_frontier_is_false g1) fe (middle_frontier_spec g2) (middle_frontier_spec g1)
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
          exact ⟨by use up2 ++ t; exact ⟨by simp [ht]⟩ , List.PrefixData.refl⟩
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
          exact ⟨upp, List.PrefixData.refl⟩
      | cons head tail =>
        cases nm with
        | nil =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          constructor
          · have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec.1] at H
              exact (is_true_of_append H).2
            have H2 := (extend_top_side g2 (head::tail) H1 (by simp))
            rw [spec.1] at H2
            exact PartialGrid.vertical_append_one pg H2
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_nil, List.append_assoc, List.cons_append,
              List.append_cancel_left_eq] at fe'
            constructor
            simp [k_is, k1_is, fe'.1]
          exact ⟨upp, List.PrefixData.refl⟩
        | cons head1 tail1 =>
          use bot2, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
          constructor
          · have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec.1] at H
              exact (is_true_of_append H).2
            have H2 := (extend_top_side g2 (head::tail) H1 (by simp))
            rw [spec.1] at H2
            have H := PartialGrid.vertical_append pg H2 (by simp)
            rw [List.append_nil] at H
            exact H
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            constructor
            simp only [List.append_assoc, List.cons_append, fe'.1, k_is, k1_is]
          exact ⟨upp, List.PrefixData.refl⟩
    rw [← l2_is] at g2_ih
    rcases @g2_ih k l1 (by simp) with ⟨nb, nm, nu, pg, fe', upp, botp⟩
    use nb, nm ++ nu ++mid, up
    constructor
    · exact PartialGrid.vertical_append g1 pg h
    constructor
    · constructor
      rw [l_is, l1_is, ← List.append_assoc, ← List.append_assoc, fe'.1, ← List.append_assoc, ← List.append_assoc]
    exact ⟨List.SuffixData.refl, botp⟩


noncomputable def step_two (ha : is_false a) (ha1 : a.length > 0)
    (hb : is_true b) (hb1 : b.length > 0) :
    SemiThueData grid_style (a ++ b) c →
    (Σ bot mid up, PartialGrid a b bot mid up × PLift (bot ++ mid ++ up = c)) := by
  intro h
  generalize hab : a ++ b = ab at h
  induction SemiThueData.toSemiThueDataDerivation h with
  | refl =>
    rw [← hab]
    use [], a ++ b, []
    constructor
    · exact PartialGrid.empty _ _ ha1 ha hb1 hb
    constructor
    rw [List.append_nil, List.nil_append]
  | step h1 h2 ih =>
    rcases ih hab (SemiThueDataDerivation.toSemiThueData h1) with ⟨bot, mid, up, h3, ⟨h4⟩⟩
    rcases add_cell h3 h2 h4 with ⟨b, m, u, h3, h4⟩
    use b, m, u
    exact ⟨h3, h4.1⟩

-- noncomputable def chain_length (h : SemiThue reversing (a1 ++ a2) (b1 ++ b2))
--     (ha1 : is_false a1) (a1_len : a1.length >0) (ha2 : is_true a2) (a2_len : a2.length > 0)
--     (hb1 : is_true b1) (hb2 : is_false b2) : ℕ := by
--   have H := stepOne h (by use a1, a2; exact ⟨ha1, ⟨ha2, rfl⟩⟩)
--       (by use b1, b2; exact ⟨hb1, ⟨hb2, rfl⟩⟩)
--   rcases H with ⟨c, spec1, spec2, spec3, spec35⟩
--   unfold to_SignedOptionList at spec1
--   simp [List.map_append] at spec1
--   change SemiThue grid_style (to_SignedOptionList a1 ++ to_SignedOptionList a2) c at spec1
--   rw [← SignedList.to_SignedOptionList_length] at a1_len
--   rw [← SignedList.to_SignedOptionList_length] at a2_len
--   rcases step_two (is_false_to_SignedOptionList ha1) a1_len (is_true_to_SignedOptionList ha2)
--     a2_len spec1 with ⟨bot, mid, up, pg, c_is⟩
--   exact PartialGrid.length pg
