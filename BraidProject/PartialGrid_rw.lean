import BraidProject.PartialGrid_bounded
import BraidProject.pgf_def
import BraidProject.SpecificConstructiveThings
import BraidProject.ToOption

open PartialGrid

theorem empty_frontier_unique (h1: PartialGrid a1 b1 c1 d1 e1) (h2 : PartialGrid a2 b2 c2 d2 e2)
  (ha : a1 = a2) (hb : b1 = b2) (hd1 : d1 = []) (hd2 : d2 = [] ): c2 = c1 ∧ e2 = e1 := by
  induction h1 generalizing a2 b2 c2 d2 e2 with
  | single_gridt h =>
    cases h with
    | empty =>
      simp_all
      rw [← ha, ← hb]
      apply pg_empty h2 ha.symm hb.symm hd2
    | top_bottom i =>
      simp_all
      rw [← ha, ← hb]
      apply pg_top_bottom h2 ha.symm hb.symm hd2
    | sides i =>
      simp_all
      rw [← ha, ← hb]
      apply pg_side_side h2 ha.symm hb.symm hd2
    | top_left i =>
      simp_all
      apply pg_top_left h2 ha.symm hb.symm hd2
    | adjacent i k h =>
      have H := pg_adjacent h2 ha.symm hb.symm hd2 h
      simp_all
    | separated i j h =>
      have H := pg_separated h2 ha.symm hb.symm hd2 (or_dist_iff.mpr h)
      simp_all
  | empty a b ha ha1 hb hb =>
    simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i i j k l m n o p
    rcases splittable_vertically_of_pg' h2 _ _ hb.symm (PartialGrid.top_length_pos g1) (PartialGrid.top_length_pos g2)
      with ⟨mid, c4, d4, c5, d5, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
    · specialize g1_ih i1
      specialize g2_ih i2
      simp_all
      have c_t : is_true c2 := h2.bottom_frontier_is_true
      rw [long] at c_t
      apply is_true_append at c_t
      have d4_t : is_true d4 := (is_true_append c_t.2).1
      have d5_t : is_true d5 := (is_true_append (is_true_append c_t.2).2).2
      rcases middle_frontier_nil_or_caps i1 with ⟨⟨one⟩⟩ | ⟨fronti, midi, caboosei, speci⟩
      · rcases middle_frontier_nil_or_caps i2 with ⟨⟨three⟩⟩ | ⟨fronti1, midi2, caboosei2, ⟨speci2⟩⟩
        · simp_all
        rw [speci2] at d5_t
        specialize d5_t ⟨fronti1, false⟩ ⟨by simp⟩
        simp at d5_t
        exact d5_t.1.elim
      rw [speci.1] at d4_t
      specialize d4_t (fronti, false) ⟨by simp⟩
      simp only [Bool.false_eq_true] at d4_t
      exact d4_t.1.elim
    rcases b with ⟨d6, d7, h6, ⟨len⟩, ⟨e1_nil⟩, ⟨d1_is⟩, ⟨b4_is⟩⟩
    rw [hd2] at d1_is
    simp only [List.nil_eq, List.append_eq_nil_iff] at d1_is
    apply (not_both_empty h6 d1_is.1 rfl).elim
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i i j k l m n o p q
    rcases splittable_vertically_of_pg' h2 _ _ hb.symm (PartialGrid.top_length_pos g1) (PartialGrid.top_length_pos g2)
      with ⟨mid, c4, d4, c5, d5, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
    · specialize g1_ih i1
      specialize g2_ih i2
      simp_all only [gt_iff_lt, List.append_assoc, List.append_eq_nil_iff, List.append_nil,
        forall_const, List.length_nil, lt_self_iff_false]
    rcases b with ⟨d6, d7, h6, ⟨len⟩, ⟨e1_nil⟩, ⟨d1_is⟩, ⟨b4_is⟩⟩
    specialize g1_ih h6 ha rfl
    simp_all only [gt_iff_lt, List.append_assoc, List.append_eq_nil_iff, List.nil_eq, forall_const,
      true_and, List.length_nil, lt_self_iff_false]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i i j k l m n o p
    rcases splittable_horizontally_of_pg h2 _ _ ha.symm (PartialGrid.left_length_pos g1) (PartialGrid.left_length_pos g2)
      with ⟨mid, c4, d4, c5, d5, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
    · specialize g1_ih i1
      specialize g2_ih i2
      simp_all
      have e_f : is_false e2 := h2.right_frontier_is_false
      rw [← long] at e_f
      apply is_false_append at e_f
      have c4_f : is_false c4 := (e_f.1)
      have c5_f : is_false c5 := (is_false_append (is_false_append e_f.2).2).1
      rcases middle_frontier_nil_or_caps i1 with ⟨⟨one⟩⟩ | ⟨fronti, midi, caboosei, speci⟩
      · rcases middle_frontier_nil_or_caps i2 with ⟨⟨three⟩⟩ | ⟨fronti1, midi2, caboosei2, ⟨speci2⟩⟩
        · simp_all
        rw [speci2] at c4_f
        specialize c4_f ⟨caboosei2, true⟩ ⟨by simp⟩
        simp at c4_f
        exact c4_f.1.elim
      rw [speci.1] at c5_f
      specialize c5_f (caboosei, true) ⟨by simp⟩
      simp at c5_f
      exact c5_f.1.elim
    rcases b with ⟨db, cb, drest, h6, ⟨d2_is⟩, ⟨m_is⟩, ⟨c2_is⟩, ⟨len⟩⟩
    exfalso
    exact not_both_empty_early h2 c2_is hd2
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i i j k l m n o p q
    rcases splittable_horizontally_of_pg h2 _ _ ha.symm (PartialGrid.left_length_pos g1) (PartialGrid.left_length_pos g2)
      with ⟨mid, c4, d4, c5, d5, i1, i2, ⟨long⟩, ⟨len⟩⟩ | b
    · specialize g1_ih i1
      specialize g2_ih i2
      simp_all
    rcases b with ⟨db, cb, drest, h6, ⟨d2_is⟩, ⟨m_is⟩, ⟨c2_is⟩, ⟨len⟩⟩
    specialize g1_ih h6 rfl hb
    simp only [List.append_assoc, List.append_eq_nil_iff] at hd1
    have H : k = [] := by simp_all
    exfalso
    have H := PartialGrid.top_length_pos g2
    simp_all

theorem empty_helper
    (g : PartialGrid a b c d e) (c_is : c = []) (d_is : d = a ++ b) (e_is : e = []) :
    g.length = 0 := by
  induction g with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i => simp [to_up, to_over] at d_is
    | adjacent i j h => simp [to_up, to_over] at d_is
    | separated i j h => simp [to_up, to_over] at d_is
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp at c_is
    exact (not_both_empty_early g1 c_is.1 rfl).elim
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rcases middle_frontier_nil_or_caps g1 with ⟨⟨mid_nil⟩⟩ | ⟨frontm, midm, caboosem, specm⟩
    · exact (not_both_empty_early g1 c_is mid_nil).elim
    rcases middle_frontier_nil_or_caps g2 with ⟨⟨mid2_nil⟩⟩ | ⟨frontm2, midm2, caboosem2, specm2⟩
    · exact (not_both_empty g2 mid2_nil e_is).elim
    rw [specm.1, specm2.1] at d_is
    rename_i f g i j k l m n o
    rcases List.append_eq_append_iff.mp d_is with ⟨as, one, two⟩ | ⟨as, one, two⟩
    · have H : is_false f := g1.left_frontier_is_false
      rw [one] at H
      specialize H (caboosem, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    have H : is_true (g ++ l) := by
      apply is_true_of_true_true g1.top_frontier_is_true g2.top_frontier_is_true
    rw [two] at H
    specialize H (frontm2, false) ⟨by simp⟩
    simp at H
    exact H.1.elim
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    simp at e_is
    exact (not_both_empty g1 rfl e_is.2).elim
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases middle_frontier_nil_or_caps g1 with ⟨⟨mid_nil⟩⟩ | ⟨frontm, midm, caboosem, specm⟩
    · exact (not_both_empty g1 mid_nil e_is).elim
    rcases middle_frontier_nil_or_caps g2 with ⟨⟨mid2_nil⟩⟩ | ⟨frontm2, midm2, caboosem2, specm2⟩
    · exact (not_both_empty_early g2 c_is mid2_nil).elim
    rw [specm.1, specm2.1] at d_is
    rename_i f g i j k l m n o
    rcases List.append_eq_append_iff.mp d_is with ⟨as, one, two⟩ | ⟨as, one, two⟩
    · have H : is_false (l ++ f) := by
        apply is_false_of_false_false
        exact g2.left_frontier_is_false
        exact g1.left_frontier_is_false
      rw [one] at H
      specialize H (caboosem2, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    have H : is_true g := g1.top_frontier_is_true
    rw [two] at H
    specialize H (frontm, false) ⟨by simp⟩
    simp at H
    exact H.1.elim

noncomputable def grid_rel_real_means (h : grid_style_real i j) : Σ a b c d,
    (h1 : cell (option_to_cell (some a)) (option_to_cell (some b)) c d) ×
    PLift (i = [(some a, false), (some b, true)] ∧ j = to_over d ++ to_up c) ×
    PLift ((PartialGrid.single_gridt h1).length = 1):= by
  cases h with
  | basic n =>
    use n, n, [], []
    exact ⟨cell.top_left n, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | apart h =>
    rename_i i j
    use i, j, [i], [j]
    exact ⟨cell.separated i j (or_dist_iff.mp h), ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | close h =>
    rename_i i j
    use i, j, [i, j], [j, i]
    exact ⟨cell.adjacent i j h, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩

noncomputable def empty_fill_means (h : empty_fill i j) : Σ a b c d,
    (h1 : cell (option_to_cell a) (option_to_cell b) c d) ×
    PLift (i = [(a, false), (b, true)] ∧ j = to_over d ++ to_up c) ×
    PLift ((PartialGrid.single_gridt h1).length = 0):= by
  cases h with
  | empty =>
    use none, none, [], []
    exact ⟨cell.empty, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | over i =>
    use some i, none, [i], []
    exact ⟨cell.sides i, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩
  | up i =>
    use none, some i, [], [i]
    exact ⟨cell.top_bottom i, ⟨⟨rfl, rfl⟩, ⟨by simp [PartialGrid.length]⟩⟩⟩

noncomputable def skeleton_one_one_real (h : grid_style_real i j) (ha : a.length > 0) (hb : b.length > 0)
    (i_is : i = [(a3, false), (b3, true)]) (ab : [(a3, false), (b3, true)] = a ++ b) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = j) × PLift (h1.length = 1) := by
  rcases grid_rel_real_means h with ⟨a1, b1, c1, d1, h_cell, ⟨i_is', j_is⟩, len⟩
  use to_over d1, [], to_up c1
  have ab_is := List.append_eq_len_two ha hb ab.symm
  rw [ab_is.1, ab_is.2]
  change _ = [(a3, false)] ++ [(b3, true)] at i_is
  rw [i_is'] at i_is
  have happ := List.append_eq_len_two (by simp) (by simp) i_is.symm
  rw [happ.1, happ.2]
  rw [← over_oc, ← up_oc]
  use PartialGrid.single_gridt h_cell
  rw [List.append_nil]
  constructor
  · exact ⟨j_is.symm⟩
  exact len

noncomputable def skeleton_one_one_empty (h : empty_fill i j) (ha : a.length > 0) (hb : b.length > 0)
    (i_is : i = [(a3, false), (b3, true)]) (ab : [(a3, false), (b3, true)] = a ++ b) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = j) × PLift (h1.length = 0) := by
  rcases empty_fill_means h with ⟨a1, b1, c1, d1, h_cell, ⟨i_is', j_is⟩, len⟩
  use to_over d1, [], to_up c1
  have ab_is := List.append_eq_len_two ha hb ab.symm
  rw [ab_is.1, ab_is.2]
  change _ = [(a3, false)] ++ [(b3, true)] at i_is
  rw [i_is'] at i_is
  have happ := List.append_eq_len_two (by simp) (by simp) i_is.symm
  rw [happ.1, happ.2]
  rw [← over_oc, ← up_oc]
  use PartialGrid.single_gridt h_cell
  rw [List.append_nil]
  constructor
  · exact ⟨j_is.symm⟩
  exact len

noncomputable def skeleton_one_cons_real (h2 : grid_style_real i j) (fe : a ++ b = ([(a3, false), (b3, true)] ++ head :: tail))
    (b_is : b = b1 ++ head :: tail) (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b)
    (ab_is : [(a3, false), (b3, true)] = a ++ b1) (i_is : i = [(a3, false), (b3, true)]):
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = [] ++ j ++ head :: tail) ×
    PLift (h1.length = 1):= by
  have ht_true : is_true (head :: tail) := by
    rw [b_is] at hb
    exact (is_true_append hb).2
  rcases grid_rel_real_means h2 with ⟨a2, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  use to_over d2, to_up c2 ++ head :: tail, []
  have helper := i_is.symm.trans i_is'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at helper
  have ha : a = [(some a2, false)] := by
    rw [← helper.1]
    exact bool_change_second ha1 ha ab_is.symm
  have hb : b = (some b2, true) :: head :: tail := by
    rw [← helper.2]
    rw [ha] at fe
    simp only [List.singleton_append, List.cons_append, List.cons.injEq, Prod.mk.injEq,
      and_true] at fe
    exact fe.2
  have hd : to_over d2 = to_over d2 ++ [] := by simp
  rw [ha, hb, hd]
  use (PartialGrid.horizontal_append_one (PartialGrid.single_gridt h_cell)
    (PartialGrid.empty (to_up c2) (head :: tail) (by simp [to_up_len_pos]) is_false_up (by simp) ht_true))
  constructor
  · rw [j_is]
    exact {down := by simp}
  constructor
  rw [PartialGrid.length, hl.1, PartialGrid.length]

noncomputable def skeleton_one_cons_empty (h2 : empty_fill i j) (fe : a ++ b = ([(a3, false), (b3, true)] ++ head :: tail))
    (b_is : b = b1 ++ head :: tail) (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b)
    (ab_is : [(a3, false), (b3, true)] = a ++ b1) (i_is : i = [(a3, false), (b3, true)]):
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = [] ++ j ++ head :: tail) ×
    PLift (h1.length = 0):= by
  have ht_true : is_true (head :: tail) := by
    rw [b_is] at hb
    exact (is_true_append hb).2
  rcases empty_fill_means h2 with ⟨a2, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  use to_over d2, to_up c2 ++ head :: tail, []
  have helper := i_is.symm.trans i_is'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at helper
  have ha' : a = to_up (option_to_cell a2) := by
    rw [← helper.1]
    have H := bool_change_second ha1 ha ab_is.symm
    rw [H]
    exact Eq.symm up_oc
  have hb : b = (to_over (option_to_cell b2) ++ head :: tail) := by
    rw [← helper.2]
    have H : a = [(a2, false)] := by
      rw [← helper.1]
      exact bool_change_second ha1 ha ab_is.symm
    rw [H] at fe
    simp at fe
    simp [fe.2]
    have H2 : [(b3, true)] = to_over (option_to_cell b3) := by
      exact Eq.symm over_oc
    rw [← H2]
    simp
  have hd : to_over d2 = to_over d2 ++ [] := by simp
  rw [ha', hb, hd]
  use (PartialGrid.horizontal_append_one (PartialGrid.single_gridt h_cell)
    (PartialGrid.empty (to_up c2) (head :: tail) (by simp [to_up_len_pos]) is_false_up (by simp) ht_true))
  constructor
  · rw [j_is]
    exact {down := by simp}
  constructor
  rw [PartialGrid.length, hl.1, PartialGrid.length]

noncomputable def skeleton_cons_one_real (h2 : grid_style_real i j) (a_is : a = head :: tail ++ a2)
    (ha : is_false a) (hb : is_true b) (ab_is : [(a3, false), (b3, true)] = a2 ++ b1)
    (i_is : i = [(a3, false), (b3, true)]) (b_is : b = b1) (hb1 : b.length > 0) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = head :: tail ++ j ++ []) ×
    PLift (h1.length = 1):= by
  rcases grid_rel_real_means h2 with ⟨a5, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  have ht_false : is_false (head :: tail) := by
    rw [a_is] at ha
    exact (is_false_append ha).1
  use [], head::tail ++ to_over d2, to_up c2
  rw [a_is]
  have H := i_is.symm.trans i_is'
  simp at H
  have H4 : b = [(b3, true)] := by
    rw [b_is]
    rw [b_is] at hb1
    rw [b_is] at hb
    exact bool_change_first hb1 hb ab_is.symm
  have H1 : a2 = [(a3, false)] := by
    rw [← b_is, ← H4] at ab_is
    change [(a3, false)] ++ b = _ ++ b at ab_is
    exact (List.append_cancel_right ab_is).symm
  have hc : to_up c2 = [] ++ to_up c2 := by simp
  have hb : to_over (option_to_cell (some b2)) = [(b3, true)] := by
    simp [option_to_cell, H.2]
  have ha : (to_up (option_to_cell (some a5))) = [(a3, false)] := by
    simp [option_to_cell, H.1]
  rw [H1, H4, hc, ← hb, ← ha]
  use PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell)
    (PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos])
    ht_false (by simp [to_over_len_pos]) is_true_over)
  constructor
  · rw [j_is]
    exact {down := by simp}
  constructor
  rw [PartialGrid.length, hl.1, PartialGrid.length]

noncomputable def skeleton_cons_one_empty (h2 : empty_fill i j) (a_is : a = head :: tail ++ a2)
    (ha : is_false a) (hb : is_true b) (ab_is : [(a3, false), (b3, true)] = a2 ++ b1)
    (i_is : i = [(a3, false), (b3, true)]) (b_is : b = b1) (hb1 : b.length > 0) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = head :: tail ++ j ++ []) ×
    PLift (h1.length = 0):= by
  rcases empty_fill_means h2 with ⟨a5, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  have ht_false : is_false (head :: tail) := by
    rw [a_is] at ha
    exact (is_false_append ha).1
  use [], head::tail ++ to_over d2, to_up c2
  rw [a_is]
  have H := i_is.symm.trans i_is'
  simp at H
  have H4 : b = [(b3, true)] := by
    rw [b_is]
    rw [b_is] at hb1
    rw [b_is] at hb
    exact bool_change_first hb1 hb ab_is.symm
  have H1 : a2 = [(a3, false)] := by
    rw [← b_is, ← H4] at ab_is
    change [(a3, false)] ++ b = _ ++ b at ab_is
    exact (List.append_cancel_right ab_is).symm
  have hc : to_up c2 = [] ++ to_up c2 := by simp
  have hb : to_over (option_to_cell (b2)) = [(b3, true)] := by
    rw [H.2]
    exact over_oc
  have ha : (to_up (option_to_cell (a5))) = [(a3, false)] := by
    rw [H.1]
    exact up_oc
  rw [H1, H4, hc, ← hb, ← ha]
  use PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell)
    (PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos])
    ht_false (by simp [to_over_len_pos]) is_true_over)
  constructor
  · rw [j_is]
    exact {down := by simp}
  constructor
  rw [PartialGrid.length, hl.1, PartialGrid.length]

noncomputable def skeleton_cons_cons_real (gs : grid_style_real i j)
    (ha : is_false (head :: tail)) (hb : is_true (headb :: tailb))
    (i_is : i = [(a3, false), (b3, true)]) :
    Σ bot mid up, (h1 : PartialGrid (head :: tail ++ [(a3, false)])
    ([(b3, true)] ++ headb :: tailb) bot mid up) ×
    PLift (bot ++ mid ++ up = head :: tail ++ j ++ headb :: tailb) × PLift (h1.length = 1):= by
  rcases grid_rel_real_means gs with ⟨a5, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  use [], head :: tail ++ to_over d2 ++ to_up c2 ++ headb :: tailb, []
  have hi := i_is.symm.trans i_is'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hi
  simp only [List.cons_append, List.singleton_append, List.append_assoc]
  have ha' : (head :: (tail ++ [(a3, false)])) =
      (head :: tail ++ to_up (option_to_cell (some a5))) := by
    simp [option_to_cell, hi.1]
  have hb' : ((b3, true) :: ([] ++ headb :: tailb)) =
      (to_over (option_to_cell (some b2)) ++ headb :: tailb) := by
    simp [option_to_cell, hi.2]
  have hd : (head :: (tail ++ to_over d2 ++ to_up c2 ++ headb :: tailb)) =
    (head :: tail ++ to_over d2 ++ [] ++ (to_up c2 ++ headb :: tailb)) := by simp
  rw [ha', hb', hd]
  use PartialGrid.horizontal_append (by simp)
    (PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell)
    (PartialGrid.empty (head :: tail) (to_over d2) (by simp) ha (by simp [to_over_len_pos]) is_true_over))
    (PartialGrid.empty (to_up c2) (headb :: tailb) to_up_len_pos is_false_up (by simp) hb)
  constructor
  · exact {down := by simp [j_is]}
  constructor
  rw [PartialGrid.length, PartialGrid.length, hl.1, PartialGrid.length]
  simp [PartialGrid.length]

noncomputable def skeleton_cons_cons_empty (gs : empty_fill i j)
    (ha : is_false (head :: tail)) (hb : is_true (headb :: tailb))
    (i_is : i = [(a3, false), (b3, true)]) :
    Σ bot mid up, (h1 : PartialGrid (head :: tail ++ [(a3, false)])
    ([(b3, true)] ++ headb :: tailb) bot mid up) ×
    PLift (bot ++ mid ++ up = head :: tail ++ j ++ headb :: tailb) × PLift (h1.length = 0):= by
  rcases empty_fill_means gs with ⟨a5, b2, c2, d2, h_cell, ⟨i_is', j_is⟩, hl⟩
  use [], head :: tail ++ to_over d2 ++ to_up c2 ++ headb :: tailb, []
  have hi := i_is.symm.trans i_is'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hi
  simp only [List.cons_append, List.singleton_append, List.append_assoc]
  have ha' : (head :: (tail ++ [(a3, false)])) =
      (head :: tail ++ to_up (option_to_cell (a5))) := by
    rw [hi.1]
    simp only [List.cons_append, List.cons.injEq, List.append_cancel_left_eq, true_and]
    exact Eq.symm up_oc
  have hb' : ((b3, true) :: ([] ++ headb :: tailb)) =
      (to_over (option_to_cell (b2)) ++ headb :: tailb) := by
    simp only [hi.2, List.nil_append, over_oc, List.cons_append, List.nil_append]
  have hd : (head :: (tail ++ to_over d2 ++ to_up c2 ++ headb :: tailb)) =
    (head :: tail ++ to_over d2 ++ [] ++ (to_up c2 ++ headb :: tailb)) := by simp
  rw [ha', hb', hd]
  use PartialGrid.horizontal_append (by simp)
    (PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell)
    (PartialGrid.empty (head :: tail) (to_over d2) (by simp) ha (by simp [to_over_len_pos]) is_true_over))
    (PartialGrid.empty (to_up c2) (headb :: tailb) to_up_len_pos is_false_up (by simp) hb)
  constructor
  · exact {down := by simp [j_is]}
  constructor
  rw [PartialGrid.length, PartialGrid.length, hl.1, PartialGrid.length]
  simp [PartialGrid.length]

open PartialGrid

noncomputable def add_cell_w_len (h : PartialGrid a b bot mid up)
    (hg : grid_style_real i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
    Σ nb nm nu, (h1 : PartialGrid a b nb nm nu) × PLift (nb ++ nm ++ nu = k ++ j ++ l) ×
    List.Suffix' up nu × List.Prefix' bot nb ×
    PLift (h.length + 1 = h1.length) := by
  rcases grid_style_real_split hg with ⟨a1, b1, ⟨i_is⟩⟩
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
        have H := skeleton_one_one_real hg (by assumption) hb (by assumption) i_is
        rcases H with ⟨b, m, u, h3, h4, hl⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.nil_suffix_C, ⟨List.nil_prefix_C, ?_⟩⟩⟩⟩
        constructor
        simp [PartialGrid.length, hl.1]
      | cons head tail =>
        rw [← l_is]
        rw [← k_is, List.nil_append, ← l_is] at fe
        rw [← a_is] at ha1
        have := skeleton_one_cons_real hg fe b_is ha1 ha hb1 (by rw [← a_is] at i_is; exact i_is)
          (by assumption)
        rcases this with ⟨b, m, u, h3, h4, hl⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.nil_suffix_C, ⟨List.nil_prefix_C, ?_⟩⟩⟩⟩
        constructor
        simp [PartialGrid.length, hl.1]
    | cons head tail =>
      cases b2 with
      | nil =>
        rw [← k_is, ← l_is,]
        rw [List.append_nil] at b_is
        have := skeleton_cons_one_real hg a_is ha1 hb1 i_is (by assumption) b_is hb
        rcases this with ⟨b, m, u, h3, h4, ⟨hl⟩⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.nil_suffix_C, ⟨List.nil_prefix_C, ?_⟩⟩⟩⟩
        simp [PartialGrid.length]
        constructor
        omega
      | cons headb tailb =>
        rw [a_is] at ha1
        rw [b_is] at hb1
        have H3 := bool_split (is_false_append ha1).2 (is_true_append hb1).1 i_is
        rw [← k_is, ← l_is]
        have := skeleton_cons_cons_real hg (is_false_append ha1).1 (is_true_append hb1).2 (by assumption)
        rcases this with ⟨b', m, u, h3, h4⟩
        use b', m, u
        subst a_is b_is
        have := H3.1
        subst this
        have := H3.2
        subst this
        use h3
        constructor
        · exact h4.1
        constructor
        · exact List.nil_suffix_C
        constructor
        · exact List.nil_prefix_C
        constructor
        simp [PartialGrid.length, h4.2.1]
  | horizontal_append_one g1 g2 ih1 ih2 =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    rcases big_split_first (PartialGrid.bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
    rcases @ih2 k₂ l eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
    use bot2 ++ bot1, mid1, up1
    use PartialGrid.horizontal_append_one g1 pg1
    constructor
    · simp [k_is, k₁_is, fe]
      simp at fe1
      exact fe1
    refine ⟨h5, ⟨(List.prefix_append_right_inj_C).2 h6.1, ?_⟩⟩
    constructor
    simp only [PartialGrid.length, ← h6.2.1]
    omega
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
    have := double_split_horiz (bottom_frontier_is_true g1) (Sum.inl (bottom_frontier_is_true g2))
      (right_frontier_is_false g2) fe (middle_frontier_nil_or_caps g1)
      (middle_frontier_nil_or_caps g2)
    rcases this with hl | hr
    · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
      rcases g2_ih k2_is.symm with ⟨bot3, mid3, up3, hpg, hf⟩
      use bot2, mid2 ++ bot3++mid3, up3
      use PartialGrid.horizontal_append h g1 hpg
      simp [k_is, k1_is, k2_is, hf.1.1]
      constructor
      · exact ⟨trivial⟩
      constructor
      · exact hf.2.1
      constructor
      · exact bot2.prefix_refl_C
      constructor
      rw [length, length, ← hf.2.2.2.1]
      omega
    rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
    have H3 : bot2 ++ mid2 ++ up2 = k ++ [(some a1, false), (some b1, true)] ++ (l₁ ++ up2) := by
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
        --apply symm at spec
        subst spec
        --rw [← spec] at hpg
        use PartialGrid.horizontal_append_one hpg g2
        simp only [PartialGrid.length]
        constructor
        · rw [← List.append_assoc, List.append_nil] at hf
          apply List.append_cancel_right at hf
          rw [hf, l_is, l1_is]
          exact ⟨by simp⟩
        constructor
        · exact List.suffix_refl_C
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
            have H0 : is_false up4 := by exact right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_append H0).1
        have H := PartialGrid.extend_bottom_w_len g2 (heade::taile) lf (by simp)
        have nonsense := spec.symm
        subst nonsense
        simp only [List.cons_append, List.append_assoc, List.append_assoc]
        have hc' : bot4 = bot4 ++ [] := by simp
        have hd' : (heade :: (taile ++ bot3 ++ mid3)) = (heade :: taile ++ bot3 ++ mid3) := by simp
        rw [hc', hd']
        use PartialGrid.horizontal_append_one hpg H.1
        constructor
        · constructor
          rw [← spec] at hf
          rw [List.append_nil, ← List.append_assoc, ← List.append_assoc, List.append_left_inj] at hf
          rw [l_is, l1_is]
          have : k ++ (j ++ (l₁ ++ (bot3 ++ mid3 ++ up3))) =  k ++ j ++ l₁ ++ (bot3 ++ mid3 ++ up3) := by simp
          rw [this, ← hf]
          simp
        constructor
        · exact List.suffix_refl_C
        constructor
        · rw [List.append_nil]
          exact back2
        constructor
        rw [PartialGrid.length]
        have := H.2.1
        omega
    | cons head tail =>
      cases to_add with
      | nil =>
        use bot4, head::tail ++ bot3 ++ mid3, up3
        rw [List.nil_append] at spec
        have nonsense := spec.symm
        subst nonsense
        use PartialGrid.horizontal_append (by simp) hpg g2
        constructor
        · rw [← List.append_assoc] at hf
          change bot4 ++ ([head] ++ tail) ++ up4 = k ++ j ++ l₁ ++ up4 at hf
          rw [← List.append_assoc] at hf
          constructor
          change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up3 = _
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.append_cancel_right hf]
          simp [l_is, l1_is]
        constructor
        · exact List.suffix_refl_C
        constructor
        · assumption
        simp [PartialGrid.length]
        constructor
        rw [← h6]
        omega
      | cons heade taile =>
        use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up3
        have lf : is_false (heade :: taile) := by
          have H0 : is_false up4 := right_frontier_is_false hpg
          rw [← spec] at H0
          exact (is_false_append H0).1
        have nonsense := spec.symm
        subst nonsense
        have H3 := (PartialGrid.extend_bottom_w_len g2 (heade::taile) lf (by simp))
        have nonsense : head :: tail ++ [] ++ (heade :: taile ++ bot3 ++ mid3) =
          (head :: tail ++ heade :: taile ++ bot3 ++ mid3) := by simp
        rw [← nonsense]
        use PartialGrid.horizontal_append (by simp) hpg H3.1
        constructor
        · rw [l_is, l1_is]
          rw [← spec, ← List.append_assoc, ← List.append_assoc] at hf
          apply List.append_cancel_right at hf
          constructor
          conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
          simp
        constructor
        · exact List.suffix_refl_C
        constructor
        · assumption
        constructor
        rw [PartialGrid.length, PartialGrid.length]
        have := H3.2.1
        omega
  | vertical_append_one g1 g2 ih1 ih2 =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
      rcases @ih2 _ _ eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
      use bot1, mid1, up1 ++ up2
      use PartialGrid.vertical_append_one g1 pg1
      constructor
      · constructor
        rw [l_is, l₂_is, ← List.append_assoc, fe1.1, ← List.append_assoc]
      constructor
      · exact List.suffix_append_right_C h5
      constructor
      · exact h6.1
      constructor
      simp only [PartialGrid.length, ← h6.2.1]
      omega
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a b bot mid up a2 bot2 mid2 up2
    have := double_split_horiz' (bottom_frontier_is_true g2) (Sum.inr (right_frontier_is_false g2))
      (right_frontier_is_false g1) fe (middle_frontier_nil_or_caps g2) (middle_frontier_nil_or_caps g1)
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
          · exact List.prefix_refl_C
          constructor
          simp only [PartialGrid.length, ← len.1]
          omega
        | cons head tail =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          use PartialGrid.vertical_append pg g2 (by simp)
          constructor
          · rw [k_is]
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            constructor
            conv => rhs; rw [List.append_assoc, List.append_assoc, ← fe'.1, k1_is]
            simp
          constructor
          · exact upp
          constructor
          · exact List.prefix_refl_C
          constructor
          simp only [PartialGrid.length, ← len.1]
          omega
      | cons head tail =>
        cases nm with
        | nil =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          have H1 : is_true (head:: tail) := by
            have H : is_true nb := bottom_frontier_is_true pg
            rw [← spec.1] at H
            exact (is_true_append H).2
          have H2 := (extend_side_w_len g2 (head::tail) H1 (by simp))
          rw [spec.1] at H2
          use PartialGrid.vertical_append_one pg H2.1
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_nil, List.append_assoc, List.cons_append,
              List.append_cancel_left_eq] at fe'
            constructor
            simp [k_is, k1_is, spec.1, fe'.1]
          constructor
          · exact upp
          constructor
          · exact List.prefix_refl_C
          constructor
          simp only [PartialGrid.length, ← len.1, H2.2.1]
          omega
        | cons head1 tail1 =>
          use bot2, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
          have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec.1] at H
              exact (is_true_append H).2
          have H2 := (extend_side_w_len g2 (head::tail) H1 (by simp))
          rw [spec.1] at H2
          have H := PartialGrid.vertical_append pg H2.1 (by simp)
          have nonsense : (mid2 ++ up2 ++ head :: tail ++ [] ++ head1 :: tail1) =
            (mid2 ++ up2 ++ head :: tail ++ head1 :: tail1) := by simp
          rw [← nonsense]
          use PartialGrid.vertical_append pg H2.1 (by simp)
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            constructor
            simp [k_is, k1_is, spec.1, fe'.1]
          constructor
          · exact upp
          constructor
          · exact List.prefix_refl_C
          constructor
          simp only [PartialGrid.length, ← H2.2.1, ← len.1]
          omega
    rw [← l2_is] at g2_ih
    rcases @g2_ih k l1 (by simp) with ⟨nb, nm, nu, pg, fe', upp, botp⟩
    use nb, nm ++ nu ++mid, up
    use PartialGrid.vertical_append g1 pg h
    constructor
    · constructor
      rw [l_is, l1_is, ← List.append_assoc, ← List.append_assoc, fe'.1, ← List.append_assoc, ← List.append_assoc]
    constructor
    · exact List.suffix_refl_C
    constructor
    · exact botp.1
    constructor
    simp only [PartialGrid.length, ← botp.2.1]
    omega

noncomputable def add_empty_cell_w_len (h : PartialGrid a b bot mid up)
    (hg : empty_fill i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
    Σ nb nm nu, (h1 : PartialGrid a b nb nm nu) × PLift (nb ++ nm ++ nu = k ++ j ++ l) ×
    List.Suffix' up nu × List.Prefix' bot nb ×
    PLift (h.length = h1.length) := by
  rcases empty_fill_split hg with ⟨a1, b1, ⟨i_is⟩⟩
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
        have H := skeleton_one_one_empty hg (by assumption) hb (by assumption) i_is
        rcases H with ⟨b, m, u, h3, h4, hl⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.nil_suffix_C, ⟨List.nil_prefix_C, ?_⟩⟩⟩⟩
        constructor
        simp [PartialGrid.length, hl.1]
      | cons head tail =>
        rw [← l_is]
        rw [← k_is, List.nil_append, ← l_is] at fe
        rw [← a_is] at ha1
        have := skeleton_one_cons_empty hg fe b_is ha1 ha hb1 (by rw [← a_is] at i_is; exact i_is)
          (by assumption)
        rcases this with ⟨b, m, u, h3, h4, hl⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.nil_suffix_C, ⟨List.nil_prefix_C, ?_⟩⟩⟩⟩
        constructor
        simp [PartialGrid.length, hl.1]
    | cons head tail =>
      cases b2 with
      | nil =>
        rw [← k_is, ← l_is,]
        rw [List.append_nil] at b_is
        have := skeleton_cons_one_empty hg a_is ha1 hb1 i_is (by assumption) b_is hb
        rcases this with ⟨b, m, u, h3, h4, ⟨hl⟩⟩
        use b, m, u
        refine ⟨h3, ⟨h4, ⟨List.nil_suffix_C, ⟨List.nil_prefix_C, ?_⟩⟩⟩⟩
        simp [PartialGrid.length]
        constructor
        omega
      | cons headb tailb =>
        rw [a_is] at ha1
        rw [b_is] at hb1
        have H3 := bool_split (is_false_append ha1).2 (is_true_append hb1).1 i_is
        rw [← k_is, ← l_is]
        have := skeleton_cons_cons_empty hg (is_false_append ha1).1 (is_true_append hb1).2 (by assumption)
        rcases this with ⟨b', m, u, h3, h4⟩
        use b', m, u
        subst a_is b_is
        have := H3.1
        subst this
        have := H3.2
        subst this
        use h3
        constructor
        · exact h4.1
        constructor
        · exact List.nil_suffix_C
        constructor
        · exact List.nil_prefix_C
        constructor
        simp [PartialGrid.length, h4.2.1]
  | horizontal_append_one g1 g2 ih1 ih2 =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    rcases big_split_first (PartialGrid.bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
    rcases @ih2 k₂ l eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
    use bot2 ++ bot1, mid1, up1
    use PartialGrid.horizontal_append_one g1 pg1
    constructor
    · simp [k_is, k₁_is, fe]
      simp at fe1
      exact fe1
    refine ⟨h5, ⟨(List.prefix_append_right_inj_C).2 h6.1, ?_⟩⟩
    constructor
    simp only [PartialGrid.length, ← h6.2.1]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
    have := double_split_horiz (bottom_frontier_is_true g1) (Sum.inl (bottom_frontier_is_true g2))
      (right_frontier_is_false g2) fe (middle_frontier_nil_or_caps g1)
      (middle_frontier_nil_or_caps g2)
    rcases this with hl | hr
    · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
      rcases g2_ih k2_is.symm with ⟨bot3, mid3, up3, hpg, hf⟩
      use bot2, mid2 ++ bot3++mid3, up3
      use PartialGrid.horizontal_append h g1 hpg
      simp [k_is, k1_is, k2_is, hf.1.1]
      constructor
      · exact ⟨trivial⟩
      constructor
      · exact hf.2.1
      constructor
      · exact bot2.prefix_refl_C
      constructor
      rw [length, length, ← hf.2.2.2.1]
    rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
    -- have H3 : bot2 ++ mid2 ++ up2 = k ++ [(some a1, false), (some b1, true)] ++ (l₁ ++ up2) := by
    --   rw [← l2_is]
    --   simp
    have H := @g1_ih k (l₁ ++ up2) (by rw [← l2_is]; simp)
    rcases @g1_ih k (l₁ ++ up2) (by rw [← l2_is]; simp) with ⟨bot4, mid4, up4, hpg, ⟨hf⟩, ⟨to_add, ⟨spec⟩⟩, back2, ⟨h6⟩⟩
    cases mid4 with
    | nil =>
      cases to_add with
      | nil =>
        use bot4 ++ bot3, mid3, up3
        rw [List.nil_append] at spec
        --apply symm at spec
        subst spec
        --rw [← spec] at hpg
        use PartialGrid.horizontal_append_one hpg g2
        simp only [PartialGrid.length]
        constructor
        · rw [← List.append_assoc, List.append_nil] at hf
          apply List.append_cancel_right at hf
          rw [hf, l_is, l1_is]
          exact ⟨by simp⟩
        constructor
        · exact List.suffix_refl_C
        constructor
        · rcases back2 with ⟨r, hr⟩
          use r ++ bot3
          rw [← hr.1]
          constructor
          simp
        constructor
        rw [← h6]
      | cons heade taile =>
        use bot4, (heade :: taile) ++ bot3 ++ mid3, up3
        simp only [PartialGrid.length]
        have lf : is_false (heade :: taile) := by
            have H0 : is_false up4 := by exact right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_append H0).1
        have H := PartialGrid.extend_bottom_w_len g2 (heade::taile) lf (by simp)
        have nonsense := spec.symm
        subst nonsense
        simp only [List.cons_append, List.append_assoc, List.append_assoc]
        have hc' : bot4 = bot4 ++ [] := by simp
        have hd' : (heade :: (taile ++ bot3 ++ mid3)) = (heade :: taile ++ bot3 ++ mid3) := by simp
        rw [hc', hd']
        use PartialGrid.horizontal_append_one hpg H.1
        constructor
        · constructor
          rw [← spec] at hf
          rw [List.append_nil, ← List.append_assoc, ← List.append_assoc, List.append_left_inj] at hf
          rw [l_is, l1_is]
          have : k ++ (j ++ (l₁ ++ (bot3 ++ mid3 ++ up3))) =  k ++ j ++ l₁ ++ (bot3 ++ mid3 ++ up3) := by simp
          rw [this, ← hf]
          simp
        constructor
        · exact List.suffix_refl_C
        constructor
        · rw [List.append_nil]
          exact back2
        constructor
        rw [PartialGrid.length]
        have := H.2.1
        omega
    | cons head tail =>
      cases to_add with
      | nil =>
        use bot4, head::tail ++ bot3 ++ mid3, up3
        rw [List.nil_append] at spec
        have nonsense := spec.symm
        subst nonsense
        use PartialGrid.horizontal_append (by simp) hpg g2
        constructor
        · rw [← List.append_assoc] at hf
          change bot4 ++ ([head] ++ tail) ++ up4 = k ++ j ++ l₁ ++ up4 at hf
          rw [← List.append_assoc] at hf
          constructor
          change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up3 = _
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, List.append_cancel_right hf]
          simp [l_is, l1_is]
        constructor
        · exact List.suffix_refl_C
        constructor
        · assumption
        simp [PartialGrid.length]
        constructor
        rw [← h6]
      | cons heade taile =>
        use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up3
        have lf : is_false (heade :: taile) := by
          have H0 : is_false up4 := right_frontier_is_false hpg
          rw [← spec] at H0
          exact (is_false_append H0).1
        have nonsense := spec.symm
        subst nonsense
        have H3 := (PartialGrid.extend_bottom_w_len g2 (heade::taile) lf (by simp))
        have nonsense : head :: tail ++ [] ++ (heade :: taile ++ bot3 ++ mid3) =
          (head :: tail ++ heade :: taile ++ bot3 ++ mid3) := by simp
        rw [← nonsense]
        use PartialGrid.horizontal_append (by simp) hpg H3.1
        constructor
        · rw [l_is, l1_is]
          rw [← spec, ← List.append_assoc, ← List.append_assoc] at hf
          apply List.append_cancel_right at hf
          constructor
          conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
          simp
        constructor
        · exact List.suffix_refl_C
        constructor
        · assumption
        constructor
        rw [PartialGrid.length, PartialGrid.length]
        have := H3.2.1
        omega
  | vertical_append_one g1 g2 ih1 ih2 =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
      rcases @ih2 _ _ eq_rest with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
      use bot1, mid1, up1 ++ up2
      use PartialGrid.vertical_append_one g1 pg1
      constructor
      · constructor
        rw [l_is, l₂_is, ← List.append_assoc, fe1.1, ← List.append_assoc]
      constructor
      · exact List.suffix_append_right_C h5
      constructor
      · exact h6.1
      constructor
      simp only [PartialGrid.length, ← h6.2.1]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a b bot mid up a2 bot2 mid2 up2
    have := double_split_horiz' (bottom_frontier_is_true g2) (Sum.inr (right_frontier_is_false g2))
      (right_frontier_is_false g1) fe (middle_frontier_nil_or_caps g2) (middle_frontier_nil_or_caps g1)
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
          · exact List.prefix_refl_C
          constructor
          simp only [PartialGrid.length, ← len.1]
        | cons head tail =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          use PartialGrid.vertical_append pg g2 (by simp)
          constructor
          · rw [k_is]
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            constructor
            conv => rhs; rw [List.append_assoc, List.append_assoc, ← fe'.1, k1_is]
            simp
          constructor
          · exact upp
          constructor
          · exact List.prefix_refl_C
          constructor
          simp only [PartialGrid.length, ← len.1]
      | cons head tail =>
        cases nm with
        | nil =>
          use bot2, mid2 ++ up2 ++ head :: tail, nu
          have H1 : is_true (head:: tail) := by
            have H : is_true nb := bottom_frontier_is_true pg
            rw [← spec.1] at H
            exact (is_true_append H).2
          have H2 := (extend_side_w_len g2 (head::tail) H1 (by simp))
          rw [spec.1] at H2
          use PartialGrid.vertical_append_one pg H2.1
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_nil, List.append_assoc, List.cons_append,
              List.append_cancel_left_eq] at fe'
            constructor
            simp [k_is, k1_is, spec.1, fe'.1]
          constructor
          · exact upp
          constructor
          · exact List.prefix_refl_C
          constructor
          simp only [PartialGrid.length, ← len.1, H2.2.1]
        | cons head1 tail1 =>
          use bot2, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
          have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec.1] at H
              exact (is_true_append H).2
          have H2 := (extend_side_w_len g2 (head::tail) H1 (by simp))
          rw [spec.1] at H2
          have H := PartialGrid.vertical_append pg H2.1 (by simp)
          have nonsense : (mid2 ++ up2 ++ head :: tail ++ [] ++ head1 :: tail1) =
            (mid2 ++ up2 ++ head :: tail ++ head1 :: tail1) := by simp
          rw [← nonsense]
          use PartialGrid.vertical_append pg H2.1 (by simp)
          constructor
          · rw [← spec.1] at fe'
            simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq] at fe'
            constructor
            simp [k_is, k1_is, spec.1, fe'.1]
          constructor
          · exact upp
          constructor
          · exact List.prefix_refl_C
          constructor
          simp only [PartialGrid.length, ← H2.2.1, ← len.1]
    rw [← l2_is] at g2_ih
    rcases @g2_ih k l1 (by simp) with ⟨nb, nm, nu, pg, fe', upp, botp⟩
    use nb, nm ++ nu ++mid, up
    use PartialGrid.vertical_append g1 pg h
    constructor
    · constructor
      rw [l_is, l1_is, ← List.append_assoc, ← List.append_assoc, fe'.1, ← List.append_assoc, ← List.append_assoc]
    constructor
    · exact List.suffix_refl_C
    constructor
    · exact botp.1
    constructor
    simp only [PartialGrid.length, ← botp.2.1]

def skeleton_up_plain_over_plain : skeleton_order (to_up_plain a ++ to_over_plain b) := by
  use to_up_plain a
  use to_over_plain b
  constructor
  · exact to_up_plain_false
  constructor
  · exact to_over_plain_true
  exact ⟨rfl⟩

theorem pg_top_bottom_frontier (h : PartialGrid a b c d e) (ha : remove_ones a = []) :
  remove_ones b = remove_ones (c ++ d) ∧ remove_ones e = [] := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [remove_ones]
    | top_bottom i => simp [remove_ones]
    | sides i => simp [remove_ones] at ha
    | top_left i => simp [remove_ones] at ha
    | adjacent i k h => simp [remove_ones] at ha
    | separated i j h => simp [remove_ones] at ha
  | empty a b ha ha1 hb hb => simp [remove_ones, ha]
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih => simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all
  | vertical_append g1 g2 h g1_ih g2_ih => simp_all

theorem pg_side_frontier (h : PartialGrid a b c d e) (hb : remove_ones b = []) :
  remove_ones (d ++ e) = remove_ones a ∧ remove_ones c = [] := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [remove_ones]
    | top_bottom i => simp [remove_ones] at hb
    | sides i => simp [remove_ones]
    | top_left i => simp [remove_ones] at hb
    | adjacent i k h => simp [remove_ones] at hb
    | separated i j h => simp [remove_ones] at hb
  | empty a b ha ha1 hb hb1 => simp [remove_ones, hb]
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih => simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    specialize g1_ih hb
    specialize g2_ih g1_ih.2
    constructor
    · rw [List.nil_append] at g1_ih
      rw [← List.append_assoc, remove_ones_append, g2_ih.1, g1_ih.1, remove_ones_append]
    exact g2_ih.2
  | vertical_append g1 g2 h g1_ih g2_ih =>
    specialize g1_ih hb
    specialize g2_ih g1_ih.2
    constructor
    · simp_all [remove_ones_append]
      rw [← g2_ih.1]
      simp
    exact g2_ih.2

def is_true_remove_ones (h : is_true l) : is_true (remove_ones l) := by
  induction l with
  | nil => simp [remove_ones]; exact is_true_nil
  | cons head tail ih =>
    specialize ih (is_true_split h).2
    change is_true (remove_ones ([head]++tail))
    rw [remove_ones_append]
    refine is_true_of_true_true ?_ ih
    match head with
    | (none, b) =>
      simp only [remove_ones]
      exact is_true_nil
    | (some a, true) =>
      simp only [remove_ones]
      intro a1 ha1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha1
      rw [ha1.1]
      exact ⟨rfl⟩
    | (some a, false) =>
      simp only [remove_ones]
      specialize h (some a, false) ⟨by simp⟩
      simp only [Bool.false_eq_true] at h
      exact h.1.elim

def is_false_remove_ones (h : is_false l) : is_false (remove_ones l) := by
  induction l with
  | nil => simp [remove_ones]; exact is_false_nil
  | cons head tail ih =>
    specialize ih (is_false_split h).2
    change is_false (remove_ones ([head]++tail))
    rw [remove_ones_append]
    refine is_false_of_false_false ?_ ih
    match head with
    | (none, b) =>
      simp [remove_ones]
      exact is_false_nil
    | (some a, false) =>
      simp [remove_ones]
      intro a1 ha1
      simp at ha1
      rw [ha1.1]
      exact ⟨rfl⟩
    | (some a, true) =>
      simp [remove_ones]
      specialize h (some a, true) ⟨by simp⟩
      simp at h
      exact h.1.elim

theorem to_option_over_plain_eq_over (h : b.length > 0): to_option (to_over_plain b) = to_over b := by
  induction b with
  | nil => simp at h
  | cons head tail ih =>
    simp [to_option, to_over_plain, to_over]

theorem to_option_up_plain_eq_up (h : a.length > 0): to_option (to_up_plain a) = to_up a := by
  induction a with
  | nil => simp at h
  | cons head tail ih =>
    simp [to_option, to_up_plain, to_up]

theorem triple_split (h : remove_ones b = c0 ++ c2 ++ c3) :
  ∃ b1 b2 b3, b = b1 ++ b2 ++ b3 ∧ remove_ones b1 = c0 ∧
  remove_ones b2 = c2 ∧ remove_ones b3 = c3 := by
  rcases remove_ones_eq_append h with ⟨b1, b2, b_split, first_pair, c3_is⟩
  rcases remove_ones_eq_append first_pair with ⟨b11, b12, b1_is, c0_is, c2_is⟩
  use b11, b12, b2
  simp_all
