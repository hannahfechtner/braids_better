import BraidProject.Relations
import BraidProject.SpecificConstructiveThings

namespace Braid
open PartialGrid SignedList SignedOptionList GridData

def grid_style.toCellData (h : grid_style i j) : Σ a b c d,
    (h1 : CellData (option_to_list a) (option_to_list b) c d) ×
    PLift (i = [(a, false), (b, true)] ∧ j = to_horizontal_edge c ++ to_vertical_edge d) ×
    PLift ((PartialGrid.single_cell h1).length = h.length):= by
  match h with
  | grid_style.basic n =>
    use n, n, [], []
    exact ⟨CellData.top_left n, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | grid_style.apart h =>
    rename_i i j
    use i, j, [j], [i]
    exact ⟨CellData.separated i j h, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | grid_style.close h =>
    rename_i i j
    use i, j, [j, i], [i, j]
    exact ⟨CellData.adjacent i j h, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | grid_style.empty =>
    use none, none, [], []
    exact ⟨CellData.empty, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | grid_style.over i =>
    use some i, none, [], [i]
    exact ⟨CellData.sides i, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | grid_style.up i =>
    use none, some i, [i], []
    exact ⟨CellData.top_bottom i, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩

 def grid_style.toPartialGrid (h : grid_style i j) (ha : a.length > 0) (hb : b.length > 0)
    (i_is : i = [(a3, false), (b3, true)]) (ab : [(a3, false), (b3, true)] = a ++ b) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = j) × PLift (h1.length = h.length) := by
  rcases grid_style.toCellData h with ⟨a1, b1, c1, d1, h_cell, ⟨i_is', j_is⟩, len⟩
  use to_horizontal_edge c1, [], to_vertical_edge d1
  have ⟨a_is, b_is⟩ := List.append_eq_len_two ha hb ab.symm
  rw [a_is, b_is]
  change _ = [(a3, false)] ++ [(b3, true)] at i_is
  rw [i_is'] at i_is
  have ⟨rfl, rfl⟩ := List.append_eq_len_two (by simp) (by simp) i_is.symm
  rw [← to_horizontal_edge_option_to_list, ← to_vertical_edge_option_to_list]
  use PartialGrid.single_cell h_cell
  rw [List.append_nil]
  exact ⟨⟨j_is.symm⟩, len⟩

def grid_style.toPartialGrid_extend_top_side (h2 : grid_style i j)
    (fe : a ++ b = ([(a3, false), (b3, true)] ++ head :: tail))
    (b_is : b = b1 ++ head :: tail) (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b)
    (ab_is : [(a3, false), (b3, true)] = a ++ b1) (i_is : i = [(a3, false), (b3, true)]):
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = [] ++ j ++ head :: tail) ×
    PLift (h1.length = h2.length):= by
  have ht_true : is_true (head :: tail) := by
    rw [b_is] at hb
    exact (is_true_of_append hb).2
  rcases grid_style.toCellData h2 with ⟨a2, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  use to_horizontal_edge c2, to_vertical_edge d2 ++ head :: tail, []
  have helper := i_is.symm.trans i_is'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at helper
  have ha : a = [(a2, false)] := by
    rw [← helper.1]
    exact eq_left_singleton_of_is_false_append_eq_unfinished_cell ha1 ha (id (Eq.symm ab_is))
  have hb : b = (b2, true) :: head :: tail := by
    rw [← helper.2]
    rw [ha] at fe
    simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq,
      and_true] at fe
    exact fe.2
  have hc : to_horizontal_edge c2 = to_horizontal_edge c2 ++ [] := by simp
  have hb1 : (b2, true) :: head :: tail = to_horizontal_edge (option_to_list b2) ++ head :: tail := by
    simp
  rw [ha, hb, hc, ← to_vertical_edge_option_to_list, hb1]
  use (PartialGrid.horizontal_append_one (PartialGrid.single_cell h_cell)
    (PartialGrid.empty (to_vertical_edge d2) (head :: tail) (by simp [to_vertical_edge_length_pos]) is_false_to_vertical_edge (by simp) ht_true))
  constructor
  · rw [j_is]
    exact {down := by simp}
  constructor
  unfold PartialGrid.length
  erw [hl.1]
  rw [PartialGrid.length]
  rfl

def grid_style.toPartialGrid_extend_left_side (h2 : grid_style i j)
    (a_is : a = head :: tail ++ a2)
    (ha : is_false a) (hb : is_true b) (ab_is : [(a3, false), (b3, true)] = a2 ++ b1)
    (i_is : i = [(a3, false), (b3, true)]) (b_is : b = b1) (hb1 : b.length > 0) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = head :: tail ++ j ++ []) ×
    PLift (h1.length = h2.length):= by
  rcases grid_style.toCellData h2 with ⟨a5, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  have ht_false : is_false (head :: tail) := by
    rw [a_is] at ha
    exact (is_false_of_append ha).1
  use [], head::tail ++ to_horizontal_edge c2, to_vertical_edge d2
  rw [a_is]
  have H := i_is.symm.trans i_is'
  simp at H
  have H4 : b = [(b3, true)] := by
    rw [b_is]
    rw [b_is] at hb1
    rw [b_is] at hb
    exact eq_right_singleton_of_is_true_append_eq_unfinished_cell hb1 hb ab_is.symm
  have H1 : a2 = [(a3, false)] := by
    rw [← b_is, ← H4] at ab_is
    change [(a3, false)] ++ b = _ ++ b at ab_is
    exact (List.append_cancel_right ab_is).symm
  have hc : to_vertical_edge d2 = [] ++ to_vertical_edge d2 := by simp
  have hb : to_horizontal_edge (option_to_list (b2)) = [(b3, true)] := by
    rw [H.2]
    exact to_horizontal_edge_option_to_list
  have ha : (to_vertical_edge (option_to_list (a5))) = [(a3, false)] := by
    rw [H.1]
    exact to_vertical_edge_option_to_list
  rw [H1, H4, hc, ← hb, ← ha]
  use PartialGrid.vertical_append_one (PartialGrid.single_cell h_cell)
    (PartialGrid.empty (head :: tail) (to_horizontal_edge c2) (by simp)
    ht_false (by simp [to_horizontal_edge_length_pos]) is_true_to_horizontal_edge)
  constructor
  · rw [j_is]
    exact {down := by simp}
  constructor
  rw [PartialGrid.length, hl.1, PartialGrid.length]
  rfl

def grid_style.toPartialGrid_extend_both_sides (gs : grid_style i j)
    (ha : is_false (head :: tail)) (hb : is_true (headb :: tailb))
    (i_is : i = [(a3, false), (b3, true)]) :
    Σ bot mid up, (h1 : PartialGrid (head :: tail ++ [(a3, false)])
    ([(b3, true)] ++ headb :: tailb) bot mid up) ×
    PLift (bot ++ mid ++ up = head :: tail ++ j ++ headb :: tailb) × PLift (h1.length = gs.length):= by
  have ha_singleton : is_false ([(a3, false)] : List (Option ℕ × Bool)) := by
    intro x hx; simp at hx; rw [hx]
  have hb_full : is_true ([(b3, true)] ++ headb :: tailb) :=
    is_true_append (by intro x hx; simp at hx; rw [hx]) hb
  rcases gs.toPartialGrid_extend_top_side (a := [(a3, false)]) (b1 := [(b3, true)])
      (by simp) rfl ha_singleton (by simp) hb_full rfl i_is
    with ⟨bot, mid, up, pg, ⟨hf⟩, ⟨hl⟩⟩
  have res := PartialGrid.extend_left_side_w_length pg (head :: tail) ha (by simp)
  refine ⟨[], head :: tail ++ bot ++ mid, up, res.1, ⟨?_⟩, ⟨?_⟩⟩
  · show [] ++ (head :: tail ++ bot ++ mid) ++ up = head :: tail ++ j ++ headb :: tailb
    rw [List.nil_append, List.append_assoc, List.append_assoc,
      ← List.append_assoc bot mid up, hf]
    simp
  rw [← res.2.down, hl]

open PartialGrid

-- this can be done computably (see below), but the noncomputable version is easier prove,
-- as we can see the inductive hypotheses listed. The PLifts are ugly, but are preferable to
-- subtypes while implementing this proof, as subtypes hide the type of the object in the infoview
noncomputable def PartialGrid.add_cell_with_length (h : PartialGrid a b bot mid up)
    (hg : grid_style i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
    Σ nb nm nu, (h1 : PartialGrid a b nb nm nu) × PLift (nb ++ nm ++ nu = k ++ j ++ l) ×
    List.SuffixData up nu × List.PrefixData bot nb ×
    PLift (h.length + hg.length = h1.length) := by
  rcases Braid.grid_style_spec hg with ⟨a1, b1, ⟨i_is⟩⟩
  rw [i_is] at fe
  induction h generalizing k l with
  | single_cell h =>
    rw [List.append_nil] at fe
    exact (not_false_true_infix_horizontal_vertical_edge fe).elim
  | empty a b ha ha1 hb hb1 =>
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append] at fe
    rcases over_up_splits_at_i ha1 hb1 ha fe with ⟨a1, a2, b1, b2, a_is, b_is, i_is, k_is, l_is⟩
    cases a1 with
    | nil =>
      rw [List.nil_append] at a_is
      rw [a_is] at ha1
      rw [← k_is]
      cases b2 with
      | nil =>
        rw [← l_is, List.append_nil, List.nil_append]
        rw [List.append_nil] at b_is
        rw [← a_is,← b_is] at i_is
        have := grid_style.toPartialGrid hg ha hb (by assumption) i_is
        rcases this with ⟨b, m, u, h3, h4, hl⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.SuffixData.nil, ⟨List.PrefixData.nil, ?_⟩⟩⟩⟩
        constructor
        simp [PartialGrid.length, hl.1]
      | cons head tail =>
        rw [← l_is]
        rw [← k_is, List.nil_append, ← l_is] at fe
        rw [← a_is] at ha1
        have := grid_style.toPartialGrid_extend_top_side hg fe b_is ha1 ha hb1 (by rw [← a_is] at i_is; exact i_is)
          (by assumption)
        rcases this with ⟨b, m, u, h3, h4, hl⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.SuffixData.nil, ⟨List.PrefixData.nil, ?_⟩⟩⟩⟩
        constructor
        simp [PartialGrid.length, hl.1]
    | cons head tail =>
      cases b2 with
      | nil =>
        rw [← k_is, ← l_is,]
        rw [List.append_nil] at b_is
        have := grid_style.toPartialGrid_extend_left_side hg a_is ha1 hb1 i_is (by assumption) b_is hb
        rcases this with ⟨b, m, u, h3, h4, ⟨hl⟩⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.SuffixData.nil, ⟨List.PrefixData.nil, ?_⟩⟩⟩⟩
        simp only [length, zero_add]
        constructor
        omega
      | cons headb tailb =>
        rw [a_is] at ha1
        rw [b_is] at hb1
        have ⟨h1, h2⟩ := eq_singletons_of_false_true_eq_unfinished_cell (is_false_of_append ha1).2 (is_true_of_append hb1).1 i_is
        rw [← k_is, ← l_is]
        have := grid_style.toPartialGrid_extend_both_sides hg (is_false_of_append ha1).1
          (is_true_of_append hb1).2 (by assumption)
        rcases this with ⟨b', m, u, h3, h4⟩
        use b', m, u
        subst a_is b_is h1 h2
        use h3
        exact ⟨h4.1, List.SuffixData.nil, List.PrefixData.nil, ⟨by simp [PartialGrid.length,
          ← h4.2.1]⟩⟩
  | horizontal_append_one g1 g2 ih1 ih2 =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    rcases big_split_first (PartialGrid.bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
    rcases @ih2 k₂ l eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
    use bot2 ++ bot1, mid1, up1
    use PartialGrid.horizontal_append_one g1 pg1
    constructor
    · simp only [List.append_assoc] at fe1
      simp only [List.append_assoc, k_is, k₁_is, List.append_cancel_left_eq]
      exact fe1
    refine ⟨h5, ⟨List.PrefixData.append_left h6.1, ⟨?_⟩⟩⟩
    simp only [PartialGrid.length, ← h6.2.1]
    omega
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
    have := double_split_horiz (bottom_frontier_is_true g1) (Sum.inl ⟨bottom_frontier_is_true g2⟩)
      (right_frontier_is_false g2) fe (middle_frontier_spec g1)
      (middle_frontier_spec g2)
    rcases this with hl | hr
    · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
      rcases g2_ih k2_is.symm with ⟨bot3, mid3, up3, hpg, hf⟩
      use bot2, mid2 ++ bot3++mid3, up3, PartialGrid.horizontal_append g1 hpg h
      simp only [List.append_assoc, hf.1.1, k_is, k1_is]
      refine ⟨⟨trivial⟩, hf.2.1, List.PrefixData.refl, ⟨?_⟩⟩
      rw [PartialGrid.length, PartialGrid.length, ← hf.2.2.2.1]
      omega
    rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
    have H3 : bot2 ++ mid2 ++ up2 = k ++ [(a1, false), (b1, true)] ++ (l₁ ++ up2) := by
      rw [← l2_is]
      simp
    rcases @g1_ih k (l₁ ++ up2) H3 with ⟨bot4, mid4, up4, hpg, ⟨hf⟩, ⟨to_add, ⟨spec⟩⟩, back2, ⟨h6⟩⟩
    cases mid4 with
    | nil =>
      cases to_add with
      | nil =>
        use bot4 ++ bot3, mid3, up3
        rw [List.nil_append] at spec
        subst spec
        use PartialGrid.horizontal_append_one hpg g2
        simp only [PartialGrid.length]
        constructor
        · rw [← List.append_assoc, List.append_nil] at hf
          apply List.append_cancel_right at hf
          rw [hf, l_is, l1_is]
          exact ⟨by simp⟩
        constructor
        · exact List.SuffixData.refl
        constructor
        · rcases back2 with ⟨r, hr⟩
          use r ++ bot3
          rw [← hr.1]
          constructor
          simp
        constructor
        rw [← h6]
        omega
      | cons heade taile =>
        use bot4, (heade :: taile) ++ bot3 ++ mid3, up3
        simp only [PartialGrid.length]
        have lf : is_false (heade :: taile) := by
            have H0 := right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_of_append H0).1
        have H := PartialGrid.extend_left_side_w_length g2 (heade::taile) lf (by simp)
        have nonsense := spec.symm
        subst nonsense
        simp only [List.cons_append, List.append_assoc, List.append_assoc]
        have hc' : bot4 = bot4 ++ [] := by simp
        have hd' : (heade :: (taile ++ bot3 ++ mid3)) = (heade :: taile ++ bot3 ++ mid3) := by simp
        rw [hc', hd']
        use PartialGrid.horizontal_append_one hpg H.1
        constructor
        · constructor
          rw [← spec, List.append_nil, ← List.append_assoc, ← List.append_assoc, List.append_left_inj] at hf
          rw [l_is, l1_is]
          have : k ++ (j ++ (l₁ ++ (bot3 ++ mid3 ++ up3))) =  k ++ j ++ l₁ ++ (bot3 ++ mid3 ++ up3) := by simp
          rw [this, ← hf]
          simp
        rw [PartialGrid.length, List.append_nil]
        have := H.2.1
        exact ⟨List.SuffixData.refl, ⟨back2, ⟨by omega⟩⟩⟩
    | cons head tail =>
      cases to_add with
      | nil =>
        use bot4, head::tail ++ bot3 ++ mid3, up3
        rw [List.nil_append] at spec
        have nonsense := spec.symm
        subst nonsense
        use PartialGrid.horizontal_append hpg g2 (by simp)
        constructor
        · rw [← List.append_assoc] at hf
          change bot4 ++ ([head] ++ tail) ++ up4 = k ++ j ++ l₁ ++ up4 at hf
          rw [← List.append_assoc] at hf
          constructor
          change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up3 = _
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.append_cancel_right hf]
          simp [l_is, l1_is]
        rw [PartialGrid.length, PartialGrid.length, ← h6]
        exact ⟨List.SuffixData.refl, ⟨by assumption, ⟨by omega⟩⟩⟩
      | cons heade taile =>
        use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up3
        have lf : is_false (heade :: taile) := by
          have H0 : is_false up4 := right_frontier_is_false hpg
          rw [← spec] at H0
          exact (is_false_of_append H0).1
        have nonsense := spec.symm
        subst nonsense
        have H3 := (PartialGrid.extend_left_side_w_length g2 (heade::taile) lf (by simp))
        have nonsense : head :: tail ++ [] ++ (heade :: taile ++ bot3 ++ mid3) =
          (head :: tail ++ heade :: taile ++ bot3 ++ mid3) := by simp
        rw [← nonsense]
        use PartialGrid.horizontal_append hpg H3.1 (by simp)
        constructor
        · rw [l_is, l1_is]
          rw [← spec, ← List.append_assoc, ← List.append_assoc] at hf
          apply List.append_cancel_right at hf
          constructor
          conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
          simp
        rw [PartialGrid.length, PartialGrid.length]
        have := H3.2.1
        exact ⟨List.SuffixData.refl, ⟨by assumption, ⟨by omega⟩⟩⟩
  | vertical_append_one g1 g2 ih1 ih2 =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
    rcases @ih2 _ _ eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
    use bot1, mid1, up1 ++ up2, PartialGrid.vertical_append_one g1 pg1
    rw [l_is, l₂_is, ← List.append_assoc, fe1.1, ← List.append_assoc]
    exact ⟨⟨rfl⟩, ⟨List.SuffixData.append_right h5, ⟨h6.1,
      ⟨by simp only [PartialGrid.length, ← h6.2.1]; omega⟩⟩⟩⟩
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a b bot mid up a2 bot2 mid2 up2
    have := double_split_horiz' (bottom_frontier_is_true g2) (Sum.inr ⟨right_frontier_is_false g2⟩)
      (right_frontier_is_false g1) fe (middle_frontier_spec g2) (middle_frontier_spec g1)
    rcases this with ⟨k1, k2, k_is, k1_is, k2_is⟩ | ⟨l1, l2, l_is, l1_is, l2_is⟩
    · specialize @g1_ih (bot ++ k2) l (by rw [List.append_assoc, ← k2_is]; simp)
      rcases g1_ih with ⟨nb, nm, nu, pg, fe', upp, botp, len⟩
      rcases botp with ⟨to_add, spec⟩
      cases to_add with
      | nil =>
        rw [List.append_nil] at spec
        have nonsense := spec.1.symm
        subst nonsense
        rw [spec.1] at fe'
        cases nm with
        | nil =>
          use bot2, mid2, up2++nu
          use PartialGrid.vertical_append_one pg g2
          simp only [List.append_nil, List.append_assoc, List.append_cancel_left_eq] at fe'
          constructor
          · constructor
            rw [fe'.1, k_is, k1_is]
            simp
          rcases upp with ⟨t, ⟨ht⟩⟩
          constructor
          · use up2 ++ t; exact ⟨by simp [ht]⟩
          constructor
          · exact List.PrefixData.refl
          constructor
          simp only [PartialGrid.length, ← len.1]
          omega
        | cons head tail =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          use PartialGrid.vertical_append pg g2 (by simp)
          refine ⟨⟨?_⟩, upp, List.PrefixData.refl, ⟨?_⟩⟩
          · rw [k_is]
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            conv => rhs; rw [List.append_assoc, List.append_assoc, ← fe'.1, k1_is]
            simp
          simp only [PartialGrid.length, ← len.1]
          omega
      | cons head tail =>
        cases nm with
        | nil =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          have H1 : is_true (head:: tail) := by
            have H : is_true nb := bottom_frontier_is_true pg
            rw [← spec.1] at H
            exact (is_true_of_append H).2
          have H2 := (PartialGrid.extend_top_side_w_length g2 (head::tail) H1 (by simp))
          rw [spec.1] at H2
          use PartialGrid.vertical_append_one pg H2.1
          refine ⟨⟨?_⟩, upp, List.PrefixData.refl, ⟨?_⟩⟩
          · rw [← spec.1] at fe'
            simp only [List.append_nil, List.append_assoc, List.cons_append,
              List.append_cancel_left_eq] at fe'
            simp [k_is, k1_is, fe'.1]
          simp only [PartialGrid.length, ← len.1, H2.2.1]
          omega
        | cons head1 tail1 =>
          use bot2, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
          have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec.1] at H
              exact (is_true_of_append H).2
          have H2 := (PartialGrid.extend_top_side_w_length g2 (head::tail) H1 (by simp))
          rw [spec.1] at H2
          have H := PartialGrid.vertical_append pg H2.1 (by simp)
          have nonsense : (mid2 ++ up2 ++ head :: tail ++ [] ++ head1 :: tail1) =
            (mid2 ++ up2 ++ head :: tail ++ head1 :: tail1) := by simp
          rw [← nonsense]
          use PartialGrid.vertical_append pg H2.1 (by simp)
          refine ⟨⟨?_⟩, upp, List.PrefixData.refl, ⟨?_⟩⟩
          · rw [← spec.1] at fe'
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            simp [k_is, k1_is, fe'.1]
          simp only [PartialGrid.length, ← H2.2.1, ← len.1]
          omega
    rw [← l2_is] at g2_ih
    rcases @g2_ih k l1 (by simp) with ⟨nb, nm, nu, pg, fe', upp, botp⟩
    use nb, nm ++ nu ++mid, up, PartialGrid.vertical_append g1 pg h
    refine ⟨⟨?_⟩, List.SuffixData.refl, botp.1, ⟨?_⟩⟩
    · rw [l_is, l1_is, ← List.append_assoc, ← List.append_assoc, fe'.1, ← List.append_assoc, ← List.append_assoc]
    simp only [PartialGrid.length, ← botp.2.1]
    omega

-- -- computable version of the above. we do not need this in the project but instructive to see that it can be done with a match statement
-- def PartialGrid.add_cell_with_length' (h : PartialGrid a b bot mid up)
--     (hg : grid_style i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
--     Σ nb nm nu, (h1 : PartialGrid a b nb nm nu) × PLift (nb ++ nm ++ nu = k ++ j ++ l) ×
--     List.SuffixData up nu × List.PrefixData bot nb ×
--     PLift (h.length + hg.length = h1.length) := by
--   rcases Braid.grid_style_spec hg with ⟨a1, b1, ⟨i_is⟩⟩
--   subst i_is
--   match h with
--   | single_cell h =>
--     rw [List.append_nil] at fe
--     exact (not_false_true_infix_horizontal_vertical_edge fe).elim
--   | empty a b ha ha1 hb hb1 =>
--     simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append] at fe
--     rcases over_up_splits_at_i ha1 hb1 ha fe with ⟨a1, a2, b1, b2, a_is, b_is, i_is, k_is, l_is⟩
--     cases a1 with
--     | nil =>
--       rw [List.nil_append] at a_is
--       rw [a_is] at ha1
--       rw [← k_is]
--       cases b2 with
--       | nil =>
--         rw [← l_is, List.append_nil, List.nil_append]
--         rw [List.append_nil] at b_is
--         rw [← a_is,← b_is] at i_is
--         have := grid_style.toPartialGrid hg ha hb rfl i_is
--         rcases this with ⟨b, m, u, h3, h4, hl⟩
--         use b, m, u
--         refine ⟨h3, ⟨h4, ⟨List.SuffixData.nil, ⟨List.PrefixData.nil, ?_⟩⟩⟩⟩
--         constructor
--         simp [PartialGrid.length, hl.1]
--       | cons head tail =>
--         rw [← l_is]
--         rw [← k_is, List.nil_append, ← l_is] at fe
--         rw [← a_is] at ha1
--         have := grid_style.toPartialGrid_extend_top_side hg fe b_is ha1 ha hb1 (by rw [← a_is] at i_is; exact i_is)
--           rfl
--         rcases this with ⟨b, m, u, h3, h4, hl⟩
--         use b, m, u
--         refine ⟨h3, ⟨h4, ⟨List.SuffixData.nil, ⟨List.PrefixData.nil, ?_⟩⟩⟩⟩
--         constructor
--         simp [PartialGrid.length, hl.1]
--     | cons head tail =>
--       cases b2 with
--       | nil =>
--         rw [← k_is, ← l_is,]
--         rw [List.append_nil] at b_is
--         have := grid_style.toPartialGrid_extend_left_side hg a_is ha1 hb1 i_is rfl b_is hb
--         rcases this with ⟨b, m, u, h3, h4, ⟨hl⟩⟩
--         use b, m, u
--         refine ⟨h3, ⟨h4, ⟨List.SuffixData.nil, ⟨List.PrefixData.nil, ?_⟩⟩⟩⟩
--         simp only [length, zero_add]
--         constructor
--         omega
--       | cons headb tailb =>
--         rw [a_is] at ha1
--         rw [b_is] at hb1
--         have ⟨h1, h2⟩ := eq_singletons_of_false_true_eq_unfinished_cell (is_false_of_append ha1).2 (is_true_of_append hb1).1 i_is
--         rw [← k_is, ← l_is]
--         have := grid_style.toPartialGrid_extend_both_sides hg (is_false_of_append ha1).1
--           (is_true_of_append hb1).2 rfl
--         rcases this with ⟨b', m, u, h3, h4⟩
--         use b', m, u
--         subst a_is b_is h1 h2
--         use h3
--         exact ⟨h4.1, List.SuffixData.nil, List.PrefixData.nil, ⟨by simp [PartialGrid.length,
--           ← h4.2.1]⟩⟩
--   | horizontal_append_one g1 g2 =>
--     rename_i up2 b3 bot3 mid3 up3
--     rcases big_split_first (PartialGrid.bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
--     rcases @PartialGrid.add_cell_with_length' _ _ _ _ _ _ _ k₂ l g2 hg eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
--     use b3 ++ bot1, mid1, up1
--     use PartialGrid.horizontal_append_one g1 pg1
--     constructor
--     · simp only [List.append_assoc] at fe1
--       simp only [List.append_assoc, k_is, k₁_is, List.append_cancel_left_eq]
--       exact fe1
--     refine ⟨h5, ⟨List.PrefixData.append_left h6.1, ⟨?_⟩⟩⟩
--     simp only [PartialGrid.length, ← h6.2.1]
--     omega
--   | horizontal_append g1 g2 h =>
--     rename_i b2 mid2 up2 b3 bot3 mid3
--     have := double_split_horiz (bottom_frontier_is_true g1) (Sum.inl ⟨bottom_frontier_is_true g2⟩)
--       (right_frontier_is_false g2) fe (middle_frontier_spec g1)
--       (middle_frontier_spec g2)
--     rcases this with hl | hr
--     · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
--       rcases PartialGrid.add_cell_with_length' g2 hg k2_is.symm with ⟨bot3, mid3, up3, hpg, hf⟩
--       use bot, mid2 ++ bot3++mid3, up3, PartialGrid.horizontal_append g1 hpg h
--       simp only [List.append_assoc, hf.1.1, k_is, k1_is]
--       refine ⟨⟨trivial⟩, hf.2.1, List.PrefixData.refl, ⟨?_⟩⟩
--       rw [PartialGrid.length, PartialGrid.length, ← hf.2.2.2.1]
--       omega
--     rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
--     have H3 : bot ++ mid2 ++ up2 = k ++ [(a1, false), (b1, true)] ++ (l₁ ++ up2) := by
--       rw [← l2_is]
--       simp
--     rcases @PartialGrid.add_cell_with_length' _ _ _ _ _ _ _ k (l₁ ++ up2) g1 hg H3 with ⟨bot4, mid4, up4, hpg, ⟨hf⟩, ⟨to_add, ⟨spec⟩⟩, back2, ⟨h6⟩⟩
--     cases mid4 with
--     | nil =>
--       cases to_add with
--       | nil =>
--         rw [List.nil_append] at spec
--         subst spec
--         use bot4 ++ bot3, mid3, up
--         use PartialGrid.horizontal_append_one hpg g2
--         simp only [PartialGrid.length]
--         constructor
--         · rw [← List.append_assoc, List.append_nil] at hf
--           apply List.append_cancel_right at hf
--           rw [hf, l_is, l1_is]
--           exact ⟨by simp⟩
--         constructor
--         · exact List.SuffixData.refl
--         constructor
--         · rcases back2 with ⟨r, hr⟩
--           use r ++ bot3
--           rw [← hr.1]
--           constructor
--           simp
--         constructor
--         omega
--       | cons heade taile =>
--         use bot4, (heade :: taile) ++ bot3 ++ mid3, up
--         simp only [PartialGrid.length]
--         have lf : is_false (heade :: taile) := by
--             have H0 := right_frontier_is_false hpg
--             rw [← spec] at H0
--             exact (is_false_of_append H0).1
--         have H := PartialGrid.extend_left_side_w_length g2 (heade::taile) lf (by simp)
--         have nonsense := spec.symm
--         subst nonsense
--         simp only [List.cons_append, List.append_assoc, List.append_assoc]
--         have hc' : bot4 = bot4 ++ [] := by simp
--         have hd' : (heade :: (taile ++ bot3 ++ mid3)) = (heade :: taile ++ bot3 ++ mid3) := by simp
--         rw [hc', hd']
--         use PartialGrid.horizontal_append_one hpg H.1
--         constructor
--         · constructor
--           rw [← spec, List.append_nil, ← List.append_assoc, ← List.append_assoc, List.append_left_inj] at hf
--           rw [l_is, l1_is]
--           have : k ++ (j ++ (l₁ ++ (bot3 ++ mid3 ++ up))) =  k ++ j ++ l₁ ++ (bot3 ++ mid3 ++ up) := by simp
--           rw [this, ← hf]
--           simp
--         rw [PartialGrid.length, List.append_nil]
--         have := H.2.1
--         exact ⟨List.SuffixData.refl, ⟨back2, ⟨by omega⟩⟩⟩
--     | cons head tail =>
--       cases to_add with
--       | nil =>
--         use bot4, head::tail ++ bot3 ++ mid3, up
--         rw [List.nil_append] at spec
--         have nonsense := spec.symm
--         subst nonsense
--         use PartialGrid.horizontal_append hpg g2 (by simp)
--         constructor
--         · rw [← List.append_assoc] at hf
--           change bot4 ++ ([head] ++ tail) ++ up4 = k ++ j ++ l₁ ++ up4 at hf
--           rw [← List.append_assoc] at hf
--           constructor
--           change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up = _
--           rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.append_cancel_right hf]
--           simp [l_is, l1_is]
--         rw [PartialGrid.length, PartialGrid.length, ← h6]
--         exact ⟨List.SuffixData.refl, ⟨by assumption, ⟨by omega⟩⟩⟩
--       | cons heade taile =>
--         use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up
--         have lf : is_false (heade :: taile) := by
--           have H0 : is_false up4 := right_frontier_is_false hpg
--           rw [← spec] at H0
--           exact (is_false_of_append H0).1
--         have nonsense := spec.symm
--         subst nonsense
--         have H3 := (PartialGrid.extend_left_side_w_length g2 (heade::taile) lf (by simp))
--         have nonsense : head :: tail ++ [] ++ (heade :: taile ++ bot3 ++ mid3) =
--           (head :: tail ++ heade :: taile ++ bot3 ++ mid3) := by simp
--         rw [← nonsense]
--         use PartialGrid.horizontal_append hpg H3.1 (by simp)
--         constructor
--         · rw [l_is, l1_is]
--           rw [← spec, ← List.append_assoc, ← List.append_assoc] at hf
--           apply List.append_cancel_right at hf
--           constructor
--           conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
--           simp
--         rw [PartialGrid.length, PartialGrid.length]
--         have := H3.2.1
--         exact ⟨List.SuffixData.refl, ⟨by assumption, ⟨by omega⟩⟩⟩
--   | vertical_append_one g1 g2 =>
--     rename_i a2 bot2 up2 mid3 up3
--     rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
--     rcases PartialGrid.add_cell_with_length' g2 hg eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
--     use bot1, mid1, up1 ++ up2, PartialGrid.vertical_append_one g1 pg1
--     rw [l_is, l₂_is, ← List.append_assoc, fe1.1, ← List.append_assoc]
--     exact ⟨⟨by simp⟩, ⟨List.SuffixData.append_right h5, ⟨h6.1,
--       ⟨by simp only [PartialGrid.length, ← h6.2.1]; omega⟩⟩⟩⟩
--   | vertical_append g1 g2 h =>
--     rename_i a bot2 mid a2 mid2 up2
--     have := double_split_horiz' (bottom_frontier_is_true g2) (Sum.inr ⟨right_frontier_is_false g2⟩)
--       (right_frontier_is_false g1) fe (middle_frontier_spec g2) (middle_frontier_spec g1)
--     rcases this with ⟨k1, k2, k_is, k1_is, k2_is⟩ | ⟨l1, l2, l_is, l1_is, l2_is⟩
--     · have := @PartialGrid.add_cell_with_length' _ _ _ _ _ _ _ (bot2 ++ k2) l g1 hg (by rw [List.append_assoc, ← k2_is]; simp)
--       rcases this with ⟨nb, nm, nu, pg, fe', upp, botp, len⟩
--       rcases botp with ⟨to_add, spec⟩
--       cases to_add with
--       | nil =>
--         rw [List.append_nil] at spec
--         have nonsense := spec.1.symm
--         subst nonsense
--         rw [spec.1] at fe'
--         cases nm with
--         | nil =>
--           use bot, mid2, up2++nu
--           use PartialGrid.vertical_append_one pg g2
--           simp only [List.append_nil, List.append_assoc, List.append_cancel_left_eq] at fe'
--           constructor
--           · constructor
--             rw [fe'.1, k_is, k1_is]
--             simp
--           rcases upp with ⟨t, ⟨ht⟩⟩
--           constructor
--           · use up2 ++ t; exact ⟨by simp [ht]⟩
--           constructor
--           · exact List.PrefixData.refl
--           constructor
--           simp only [PartialGrid.length, ← len.1]
--           omega
--         | cons head tail =>
--           use bot, mid2 ++ up2 ++ head :: tail, nu
--           use PartialGrid.vertical_append pg g2 (by simp)
--           refine ⟨⟨?_⟩, upp, List.PrefixData.refl, ⟨?_⟩⟩
--           · rw [k_is]
--             simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
--             conv => rhs; rw [List.append_assoc, List.append_assoc, ← fe'.1, k1_is]
--             simp
--           simp only [PartialGrid.length, ← len.1]
--           omega
--       | cons head tail =>
--         cases nm with
--         | nil =>
--           use bot, mid2 ++ up2 ++ head :: tail, nu
--           have H1 : is_true (head:: tail) := by
--             have H : is_true nb := bottom_frontier_is_true pg
--             rw [← spec.1] at H
--             exact (is_true_of_append H).2
--           have H2 := (PartialGrid.extend_top_side_w_length g2 (head::tail) H1 (by simp))
--           rw [spec.1] at H2
--           use PartialGrid.vertical_append_one pg H2.1
--           refine ⟨⟨?_⟩, upp, List.PrefixData.refl, ⟨?_⟩⟩
--           · rw [← spec.1] at fe'
--             simp only [List.append_nil, List.append_assoc, List.cons_append,
--               List.append_cancel_left_eq] at fe'
--             simp [k_is, k1_is, fe'.1]
--           simp only [PartialGrid.length, ← len.1, H2.2.1]
--           omega
--         | cons head1 tail1 =>
--           use bot, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
--           have H1 : is_true (head:: tail) := by
--               have H : is_true nb := bottom_frontier_is_true pg
--               rw [← spec.1] at H
--               exact (is_true_of_append H).2
--           have H2 := (PartialGrid.extend_top_side_w_length g2 (head::tail) H1 (by simp))
--           rw [spec.1] at H2
--           have H := PartialGrid.vertical_append pg H2.1 (by simp)
--           have nonsense : (mid2 ++ up2 ++ head :: tail ++ [] ++ head1 :: tail1) =
--             (mid2 ++ up2 ++ head :: tail ++ head1 :: tail1) := by simp
--           rw [← nonsense]
--           use PartialGrid.vertical_append pg H2.1 (by simp)
--           refine ⟨⟨?_⟩, upp, List.PrefixData.refl, ⟨?_⟩⟩
--           · rw [← spec.1] at fe'
--             simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
--             simp [k_is, k1_is, fe'.1]
--           simp only [PartialGrid.length, ← H2.2.1, ← len.1]
--           omega
--     rcases @PartialGrid.add_cell_with_length' _ _ _ _ _ _ _ k l1 g2 hg (by simp [← l2_is]) with ⟨nb, nm, nu, pg, fe', upp, botp⟩
--     use nb, nm ++ nu ++mid, up, PartialGrid.vertical_append g1 pg h
--     refine ⟨⟨?_⟩, List.SuffixData.refl, botp.1, ⟨?_⟩⟩
--     · rw [l_is, l1_is, ← List.append_assoc, ← List.append_assoc, fe'.1, ← List.append_assoc, ← List.append_assoc]
--     simp only [PartialGrid.length, ← botp.2.1]
--     omega
--     termination_by structural h

-- -- clearer formulation without PLift, but a bit trickier to prove due to the lack of detail in the infoview
-- def PartialGrid.add_cell_with_length'' (h : PartialGrid a b bot mid up)
--     (hg : grid_style i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
--     Σ nb nm nu, {h1 : PartialGrid a b nb nm nu // nb ++ nm ++ nu = k ++ j ++ l ∧ h.length + hg.length = h1.length} ×
--     List.SuffixData up nu × List.PrefixData bot nb := by
--   rcases Braid.grid_style_spec hg with ⟨a1, b1, ⟨i_is⟩⟩
--   subst i_is
--   match h with
--   | single_cell h =>
--     rw [List.append_nil] at fe
--     exact (not_false_true_infix_horizontal_vertical_edge fe).elim
--   | empty a b ha ha1 hb hb1 =>
--     simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append] at fe
--     rcases over_up_splits_at_i ha1 hb1 ha fe with ⟨a1, a2, b1, b2, a_is, b_is, i_is, k_is, l_is⟩
--     cases a1 with
--     | nil =>
--       rw [List.nil_append] at a_is
--       rw [a_is] at ha1
--       rw [← k_is]
--       cases b2 with
--       | nil =>
--         rw [← l_is, List.append_nil, List.nil_append]
--         rw [List.append_nil] at b_is
--         rw [← a_is,← b_is] at i_is
--         have := grid_style.toPartialGrid hg ha hb rfl i_is
--         rcases this with ⟨b, m, u, h3, h4, hl⟩
--         use b, m, u
--         refine ⟨⟨h3, h4.1, ?_⟩, List.SuffixData.nil, List.PrefixData.nil⟩
--         simp [PartialGrid.length, hl.1]
--       | cons head tail =>
--         rw [← l_is]
--         rw [← k_is, List.nil_append, ← l_is] at fe
--         rw [← a_is] at ha1
--         have := grid_style.toPartialGrid_extend_top_side hg fe b_is ha1 ha hb1 (by rw [← a_is] at i_is; exact i_is)
--           rfl
--         rcases this with ⟨b, m, u, h3, h4, hl⟩
--         use b, m, u
--         refine ⟨⟨h3, h4.1, ?_⟩, List.SuffixData.nil, List.PrefixData.nil⟩
--         simp [PartialGrid.length, hl.1]
--     | cons head tail =>
--       cases b2 with
--       | nil =>
--         rw [← k_is, ← l_is,]
--         rw [List.append_nil] at b_is
--         have := grid_style.toPartialGrid_extend_left_side hg a_is ha1 hb1 i_is rfl b_is hb
--         rcases this with ⟨b, m, u, h3, h4, ⟨hl⟩⟩
--         use b, m, u
--         refine ⟨⟨h3, h4.1, ?_⟩, List.SuffixData.nil, List.PrefixData.nil⟩
--         simp only [length, zero_add]
--         omega
--       | cons headb tailb =>
--         rw [a_is] at ha1
--         rw [b_is] at hb1
--         have ⟨h1, h2⟩ := eq_singletons_of_false_true_eq_unfinished_cell (is_false_of_append ha1).2 (is_true_of_append hb1).1 i_is
--         rw [← k_is, ← l_is]
--         have := grid_style.toPartialGrid_extend_both_sides hg (is_false_of_append ha1).1
--           (is_true_of_append hb1).2 rfl
--         rcases this with ⟨b', m, u, h3, h4⟩
--         use b', m, u
--         subst a_is b_is h1 h2
--         exact ⟨⟨h3, h4.1.1, by simp [PartialGrid.length, ← h4.2.1]⟩,
--           List.SuffixData.nil, List.PrefixData.nil⟩
--   | horizontal_append_one g1 g2 =>
--     rename_i up2 b3 bot3 mid3 up3
--     rcases big_split_first (PartialGrid.bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
--     rcases @PartialGrid.add_cell_with_length' _ _ _ _ _ _ _ k₂ l g2 hg eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
--     use b3 ++ bot1, mid1, up1
--     refine ⟨⟨PartialGrid.horizontal_append_one g1 pg1, ?_, ?_⟩, h5, List.PrefixData.append_left h6.1⟩
--     · simp only [List.append_assoc] at fe1
--       simp only [List.append_assoc, k_is, k₁_is, List.append_cancel_left_eq]
--       exact fe1.1
--     · simp only [PartialGrid.length, ← h6.2.1]
--       omega
--   | horizontal_append g1 g2 h =>
--     rename_i b2 mid2 up2 b3 bot3 mid3
--     have := double_split_horiz (bottom_frontier_is_true g1) (Sum.inl ⟨bottom_frontier_is_true g2⟩)
--       (right_frontier_is_false g2) fe (middle_frontier_spec g1)
--       (middle_frontier_spec g2)
--     rcases this with hl | hr
--     · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
--       rcases PartialGrid.add_cell_with_length' g2 hg k2_is.symm with ⟨bot3, mid3, up3, hpg, hf⟩
--       use bot, mid2 ++ bot3++mid3, up3
--       refine ⟨⟨PartialGrid.horizontal_append g1 hpg h, ?_, ?_⟩, hf.2.1, List.PrefixData.refl⟩
--       · simp only [List.append_assoc, hf.1.1, k_is, k1_is]
--       · rw [PartialGrid.length, PartialGrid.length, ← hf.2.2.2.1]
--         omega
--     rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
--     have H3 : bot ++ mid2 ++ up2 = k ++ [(a1, false), (b1, true)] ++ (l₁ ++ up2) := by
--       rw [← l2_is]
--       simp
--     rcases @PartialGrid.add_cell_with_length' _ _ _ _ _ _ _ k (l₁ ++ up2) g1 hg H3 with ⟨bot4, mid4, up4, hpg, ⟨hf⟩, ⟨to_add, ⟨spec⟩⟩, back2, ⟨h6⟩⟩
--     cases mid4 with
--     | nil =>
--       cases to_add with
--       | nil =>
--         rw [List.nil_append] at spec
--         subst spec
--         use bot4 ++ bot3, mid3, up
--         refine ⟨⟨PartialGrid.horizontal_append_one hpg g2, ?_, ?_⟩, List.SuffixData.refl, ?_⟩
--         · rw [← List.append_assoc, List.append_nil] at hf
--           apply List.append_cancel_right at hf
--           rw [hf, l_is, l1_is]
--           simp
--         · simp only [PartialGrid.length]
--           omega
--         · rcases back2 with ⟨r, hr⟩
--           use r ++ bot3
--           rw [← hr.1]
--           constructor
--           simp
--       | cons heade taile =>
--         use bot4, (heade :: taile) ++ bot3 ++ mid3, up
--         have lf : is_false (heade :: taile) := by
--             have H0 := right_frontier_is_false hpg
--             rw [← spec] at H0
--             exact (is_false_of_append H0).1
--         have H := PartialGrid.extend_left_side_w_length g2 (heade::taile) lf (by simp)
--         have nonsense := spec.symm
--         subst nonsense
--         simp only [List.cons_append, List.append_assoc, List.append_assoc]
--         have hc' : bot4 = bot4 ++ [] := by simp
--         have hd' : (heade :: (taile ++ bot3 ++ mid3)) = (heade :: taile ++ bot3 ++ mid3) := by simp
--         rw [hc', hd']
--         refine ⟨⟨PartialGrid.horizontal_append_one hpg H.1, ?_, ?_⟩, List.SuffixData.refl,
--           by simpa using back2⟩
--         · rw [← spec, List.append_nil, ← List.append_assoc, ← List.append_assoc, List.append_left_inj] at hf
--           rw [l_is, l1_is]
--           have : k ++ (j ++ (l₁ ++ (bot3 ++ mid3 ++ up))) =  k ++ j ++ l₁ ++ (bot3 ++ mid3 ++ up) := by simp
--           rw [this, ← hf]
--           simp
--         · simp only [PartialGrid.length]
--           have := H.2.1
--           omega
--     | cons head tail =>
--       cases to_add with
--       | nil =>
--         use bot4, head::tail ++ bot3 ++ mid3, up
--         rw [List.nil_append] at spec
--         have nonsense := spec.symm
--         subst nonsense
--         refine ⟨⟨PartialGrid.horizontal_append hpg g2 (by simp), ?_, ?_⟩, List.SuffixData.refl, back2⟩
--         · rw [← List.append_assoc] at hf
--           change bot4 ++ ([head] ++ tail) ++ up4 = k ++ j ++ l₁ ++ up4 at hf
--           rw [← List.append_assoc] at hf
--           change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up = _
--           rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.append_cancel_right hf]
--           simp [l_is, l1_is]
--         · rw [PartialGrid.length, PartialGrid.length, ← h6]
--           omega
--       | cons heade taile =>
--         use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up
--         have lf : is_false (heade :: taile) := by
--           have H0 : is_false up4 := right_frontier_is_false hpg
--           rw [← spec] at H0
--           exact (is_false_of_append H0).1
--         have nonsense := spec.symm
--         subst nonsense
--         have H3 := (PartialGrid.extend_left_side_w_length g2 (heade::taile) lf (by simp))
--         have nonsense : head :: tail ++ [] ++ (heade :: taile ++ bot3 ++ mid3) =
--           (head :: tail ++ heade :: taile ++ bot3 ++ mid3) := by simp
--         rw [← nonsense]
--         refine ⟨⟨PartialGrid.horizontal_append hpg H3.1 (by simp), ?_, ?_⟩, List.SuffixData.refl, back2⟩
--         · rw [l_is, l1_is]
--           rw [← spec, ← List.append_assoc, ← List.append_assoc] at hf
--           apply List.append_cancel_right at hf
--           conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
--           simp
--         · rw [PartialGrid.length, PartialGrid.length]
--           have := H3.2.1
--           omega
--   | vertical_append_one g1 g2 =>
--     rename_i a2 bot2 up2 mid3 up3
--     rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
--     rcases PartialGrid.add_cell_with_length' g2 hg eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
--     refine ⟨bot1, mid1, up1 ++ up2,
--       ⟨PartialGrid.vertical_append_one g1 pg1, ?_, ?_⟩,
--       List.SuffixData.append_right h5, h6.1⟩
--     · rw [l_is, l₂_is, ← List.append_assoc, fe1.1, ← List.append_assoc]
--     · simp only [PartialGrid.length, ← h6.2.1]
--       omega
--   | vertical_append g1 g2 h =>
--     rename_i a bot2 mid a2 mid2 up2
--     have := double_split_horiz' (bottom_frontier_is_true g2) (Sum.inr ⟨right_frontier_is_false g2⟩)
--       (right_frontier_is_false g1) fe (middle_frontier_spec g2) (middle_frontier_spec g1)
--     rcases this with ⟨k1, k2, k_is, k1_is, k2_is⟩ | ⟨l1, l2, l_is, l1_is, l2_is⟩
--     · have := @PartialGrid.add_cell_with_length' _ _ _ _ _ _ _ (bot2 ++ k2) l g1 hg (by rw [List.append_assoc, ← k2_is]; simp)
--       rcases this with ⟨nb, nm, nu, pg, fe', upp, botp, len⟩
--       rcases botp with ⟨to_add, spec⟩
--       cases to_add with
--       | nil =>
--         rw [List.append_nil] at spec
--         have nonsense := spec.1.symm
--         subst nonsense
--         rw [spec.1] at fe'
--         cases nm with
--         | nil =>
--           use bot, mid2, up2++nu
--           simp only [List.append_nil, List.append_assoc, List.append_cancel_left_eq] at fe'
--           rcases upp with ⟨t, ⟨ht⟩⟩
--           refine ⟨⟨PartialGrid.vertical_append_one pg g2, ?_, ?_⟩,
--             ⟨up2 ++ t, ⟨by simp [ht]⟩⟩, List.PrefixData.refl⟩
--           · rw [fe'.1, k_is, k1_is]
--             simp
--           · simp only [PartialGrid.length, ← len.1]
--             omega
--         | cons head tail =>
--           use bot, mid2 ++ up2 ++ head :: tail, nu
--           refine ⟨⟨PartialGrid.vertical_append pg g2 (by simp), ?_, ?_⟩, upp, List.PrefixData.refl⟩
--           · rw [k_is]
--             simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
--             conv => rhs; rw [List.append_assoc, List.append_assoc, ← fe'.1, k1_is]
--             simp
--           · simp only [PartialGrid.length, ← len.1]
--             omega
--       | cons head tail =>
--         cases nm with
--         | nil =>
--           use bot, mid2 ++ up2 ++ head :: tail, nu
--           have H1 : is_true (head:: tail) := by
--             have H : is_true nb := bottom_frontier_is_true pg
--             rw [← spec.1] at H
--             exact (is_true_of_append H).2
--           have H2 := (PartialGrid.extend_top_side_w_length g2 (head::tail) H1 (by simp))
--           rw [spec.1] at H2
--           refine ⟨⟨PartialGrid.vertical_append_one pg H2.1, ?_, ?_⟩, upp, List.PrefixData.refl⟩
--           · rw [← spec.1] at fe'
--             simp only [List.append_nil, List.append_assoc, List.cons_append,
--               List.append_cancel_left_eq] at fe'
--             simp [k_is, k1_is, fe'.1]
--           · simp only [PartialGrid.length, ← len.1, H2.2.1]
--             omega
--         | cons head1 tail1 =>
--           use bot, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
--           have H1 : is_true (head:: tail) := by
--               have H : is_true nb := bottom_frontier_is_true pg
--               rw [← spec.1] at H
--               exact (is_true_of_append H).2
--           have H2 := (PartialGrid.extend_top_side_w_length g2 (head::tail) H1 (by simp))
--           rw [spec.1] at H2
--           have nonsense : (mid2 ++ up2 ++ head :: tail ++ [] ++ head1 :: tail1) =
--             (mid2 ++ up2 ++ head :: tail ++ head1 :: tail1) := by simp
--           rw [← nonsense]
--           refine ⟨⟨PartialGrid.vertical_append pg H2.1 (by simp), ?_, ?_⟩, upp, List.PrefixData.refl⟩
--           · rw [← spec.1] at fe'
--             simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
--             simp [k_is, k1_is, fe'.1]
--           · simp only [PartialGrid.length, ← H2.2.1, ← len.1]
--             omega
--     rcases @PartialGrid.add_cell_with_length' _ _ _ _ _ _ _ k l1 g2 hg (by simp [← l2_is]) with ⟨nb, nm, nu, pg, fe', upp, botp⟩
--     refine ⟨nb, nm ++ nu ++mid, up,
--       ⟨PartialGrid.vertical_append g1 pg h, ?_, ?_⟩,
--       List.SuffixData.refl, botp.1⟩
--     · rw [l_is, l1_is, ← List.append_assoc, ← List.append_assoc, fe'.1, ← List.append_assoc, ← List.append_assoc]
--     · simp only [PartialGrid.length, ← botp.2.1]
--       omega
