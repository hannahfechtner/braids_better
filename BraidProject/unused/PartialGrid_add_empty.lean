import BraidProject.PartialGrid_rw

open Braid

noncomputable def grid_style_trivial_split (h : grid_style_trivial i j) : Σ a b, PLift (i = [(a, false), (b, true)]) := by
  induction h with
  | up =>
    rename_i n
    use none, n
    exact {down := rfl}
  | over =>
    rename_i n
    use n, none
    exact {down := rfl}
  | empty =>
    use none, none
    exact {down := rfl}

noncomputable def grid_style_trivial_means_new (h : grid_style_trivial i j) : Σ a b c d,
    (h1 : CellData (option_to_list a) (option_to_list b) c d) ×
    PLift (i = [(a, false), (b, true)] ∧ j = to_horizontal_edge c ++ to_vertical_edge d ∧ (PartialGrid.single_cell h1).length = 0) := by
  cases h with
  | over n =>
    use some n, none, [], [n]
    exact ⟨CellData.sides n, {down := ⟨rfl, ⟨rfl, by rw [PartialGrid.length]⟩⟩}⟩
  | up n =>
    use none, some n, [n], []
    exact ⟨CellData.top_bottom n, {down := ⟨rfl, ⟨rfl, by rw [PartialGrid.length]⟩⟩}⟩
  | empty =>
    use none, none, [], []
    exact ⟨CellData.empty, {down := ⟨rfl, ⟨rfl, by rw [PartialGrid.length]⟩⟩}⟩

noncomputable def skeleton_one_one_empty (h : grid_style_trivial i j)
    (ha : a.length > 0) (hb : b.length > 0)
    (i_is : i = [(a3, false), (b3, true)]) (ab : [(a3, false), (b3, true)] = a ++ b) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up )× PLift (bot ++ mid ++ up = j) × PLift (h1.length = 0) := by
  rcases grid_style_trivial_means_new h with ⟨a1, b1, c1, d1, h_cell, i_is', j_is, len⟩
  use to_horizontal_edge c1, [], to_vertical_edge d1
  have ab_is := List.append_eq_len_two ha hb ab.symm
  rw [ab_is.1, ab_is.2]
  change _ = [(a3, false)] ++ [(b3, true)] at i_is
  rw [i_is'] at i_is
  have happ := List.append_eq_len_two (by simp) (by simp) i_is.symm
  rw [happ.1, happ.2]
  rw [← to_vertical_edge_option_to_list, ← to_horizontal_edge_option_to_list]
  use PartialGrid.single_cell h_cell
  rw [List.append_nil]
  constructor
  · exact {down := j_is.symm}
  exact ⟨len⟩

open SignedList

noncomputable def skeleton_one_cons_empty (h2 : grid_style_trivial i j) (fe : a ++ b = ([(a3, false), (b3, true)] ++ head :: tail))
    (b_is : b = b1 ++ head :: tail) (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b)
    (ab_is : [(a3, false), (b3, true)] = a ++ b1) (i_is : i = [(a3, false), (b3, true)]):
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = [] ++ j ++ head :: tail) ×
    PLift (h1.length = 0):= by
  have ht_true : is_true (head :: tail) := by
    rw [b_is] at hb
    exact (is_true_of_append hb).2
  rcases grid_style_trivial_means_new h2 with ⟨a2, b2, c2, d2, h_cell, i_is', j_is, hl⟩
  use to_horizontal_edge c2, to_vertical_edge d2 ++ head :: tail, []
  have H2 := PartialGrid.empty (to_vertical_edge d2) (head :: tail) (by simp [to_vertical_edge_length_pos]) is_false_to_vertical_edge (by simp) ht_true
  have H3 := PartialGrid.horizontal_append_one (PartialGrid.single_cell h_cell) H2
  simp only [to_horizontal_edge_option_to_list, to_vertical_edge_option_to_list, List.singleton_append, List.append_nil] at H3
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
  rw [ha, hb]
  use H3
  constructor
  · rw [j_is]
    exact {down := by simp}
  have : to_horizontal_edge (option_to_list b2) = [(b2, true)] := by
    rw [to_horizontal_edge_option_to_list]
  have : H3.length = (PartialGrid.horizontal_append_one (PartialGrid.single_cell h_cell) H2).length :=
    same_type_same_length_pg H3 ((PartialGrid.single_gridt h_cell).horizontal_append_one H2) (up_oc).symm
        (by rw [this]; simp) (by simp) rfl rfl
  rw [PartialGrid.length, hl] at this
  have : H2.length = (PartialGrid.empty (to_up c2) (head :: tail) (by simp [to_up_len_pos]) is_false_up (by simp) ht_true).length :=
    same_type_same_length_pg
      H2 (PartialGrid.empty (to_up c2) (head :: tail) (by simp [to_up_len_pos]) is_false_up (by simp) ht_true) rfl
        rfl (by simp) rfl rfl
  rw [PartialGrid.length] at this
  constructor
  omega

noncomputable def skeleton_cons_one_empty (h2 : grid_style_trivial i j) (a_is : a = head :: tail ++ a2)
    (ha : is_false a) (hb : is_true b) (ab_is : [(a3, false), (b3, true)] = a2 ++ b1)
    (i_is : i = [(a3, false), (b3, true)]) (b_is : b = b1) (hb1 : b.length > 0) :
    Σ bot mid up, (h1 : PartialGrid a b bot mid up) × PLift (bot ++ mid ++ up = head :: tail ++ j ++ []) ×
    PLift (h1.length = 0):= by
  rcases grid_style_trivial_means h2 with ⟨a5, b2, c2, d2, h_cell, i_is', j_is, hl⟩
  have ht_false : is_false (head :: tail) := by
    rw [a_is] at ha
    exact (is_false_append ha).1
  have H2 := PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos]) ht_false (by simp [to_over_len_pos]) is_true_over
  have H3 := PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell) H2
  use [], head::tail ++ to_over d2, to_up c2
  rw [a_is]
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
  use H3
  constructor
  · rw [j_is]
    exact {down := by simp}
  constructor
  have : H3.length = (PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell)
      (PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos])
      ht_false (by simp [to_over_len_pos]) is_true_over)).length :=
    same_type_same_length_pg H3
      ((PartialGrid.single_gridt h_cell).vertical_append_one
      (PartialGrid.empty (head :: tail) (to_over d2) (by simp [to_up_len_pos])
      ht_false (by simp [to_over_len_pos]) is_true_over)) (by simp [H.1, up_oc])
      (by simp [H.2, over_oc]) rfl rfl rfl
  rw [PartialGrid.length, hl, PartialGrid.length] at this
  exact this


noncomputable def skeleton_cons_cons_empty (gs : grid_style_trivial i j)
    (ha : is_false (head :: tail)) (hb : is_true (headb :: tailb))
    (i_is : i = [(a3, false), (b3, true)]) :
    Σ bot mid up, (h1 : PartialGrid (head :: tail ++ [(a3, false)])
    ([(b3, true)] ++ headb :: tailb) bot mid up) ×
    PLift (bot ++ mid ++ up = head :: tail ++ j ++ headb :: tailb) × PLift (h1.length = 0):= by
  rcases grid_style_trivial_means gs with ⟨a5, b2, c2, d2, h_cell, i_is', j_is, hl⟩
  use [], head :: tail ++ to_over d2 ++ to_up c2 ++ headb :: tailb, []
  have H2 := PartialGrid.empty (head :: tail) (to_over d2) (by simp) ha (by simp [to_over_len_pos]) is_true_over
  have H3 := PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell) H2
  have H4 := PartialGrid.empty (to_up c2) (headb :: tailb) to_up_len_pos is_false_up (by simp) hb
  have H5 := PartialGrid.horizontal_append (by simp) H3 H4
  rw [List.append_nil] at H5
  have hi := i_is.symm.trans i_is'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hi
  rw [← hi.1, up_oc, ← hi.2, over_oc] at H5
  simp only [List.cons_append, List.singleton_append, List.append_assoc]
  simp only [List.cons_append, List.singleton_append, List.append_assoc] at H5
  rw [← List.append_assoc (to_over d2), ← List.append_assoc tail, ← List.append_assoc tail] at H5
  use H5
  constructor
  · exact {down := by simp [j_is]}
  constructor
  have : H5.length = (PartialGrid.horizontal_append (by simp)
      (PartialGrid.vertical_append_one (PartialGrid.single_gridt h_cell)
      (PartialGrid.empty (head :: tail) (to_over d2) (by simp) ha (by simp [to_over_len_pos]) is_true_over))
      (PartialGrid.empty (to_up c2) (headb :: tailb) to_up_len_pos is_false_up (by simp) hb)).length :=
    same_type_same_length_pg H5 _ (by simp [hi.1, up_oc])
      (by simp [hi.2, over_oc]) rfl (by simp) rfl
  rw [this, PartialGrid.length, PartialGrid.length, hl, PartialGrid.length]
  simp [PartialGrid.length]

open PartialGrid

noncomputable def add_empty_cell_w_len (h : PartialGrid a b bot mid up)
    (hg : grid_style_trivial i j) (fe : bot ++ mid ++ up = k ++ i ++ l) :
    Σ nb nm nu, (h1 : PartialGrid a b nb nm nu) × PLift (nb ++ nm ++ nu = k ++ j ++ l) ×
    List.Suffix' up nu × List.Prefix' bot nb ×
    PLift (h.length = h1.length) := by
  rcases grid_style_trivial_split hg with ⟨a1, b1, ⟨i_is⟩⟩
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
        rw [← H3.1, ← H3.2, ← b_is, ← a_is] at h3
        use h3
        constructor
        · exact h4.1
        constructor
        · exact List.nil_suffix_C
        constructor
        · exact List.nil_prefix_C
        rename_i old
        have : h3.length = old.length :=
          same_type_same_length_pg h3 old (by rw [a_is, H3.1]) (by rw [b_is, H3.2]) rfl rfl (by simp [H3.1, H3.2])
        rw [this, h4.2.1]
        constructor
        simp [PartialGrid.length]
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
    simp [PartialGrid.length]
    exact h6.2.1
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
      simp [PartialGrid.length, hf.2.2.2.1]
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
        use PartialGrid.horizontal_append_one hpg g2
        simp only [PartialGrid.length]
        constructor
        · rw [spec, ← List.append_assoc, List.append_nil] at hf
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
        simp
        rename_i old
        have H : hpg.length = old.length :=
          same_type_same_length_pg hpg old rfl rfl rfl rfl spec
        simp [H, h6]
      | cons heade taile =>
        use bot4, (heade :: taile) ++ bot3 ++ mid3, up3
        simp only [PartialGrid.length]
        have lf : is_false (heade :: taile) := by
            have H0 : is_false up4 := by exact right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_append H0).1
        have H := PartialGrid.extend_bottom_w_len g2 (heade::taile) lf (by simp)
        rw [← spec] at hpg
        have H2 := PartialGrid.horizontal_append_one hpg H.1
        simp only [List.append_nil, List.cons_append] at H2
        simp only [List.cons_append, List.append_assoc, List.append_assoc]
        use H2
        constructor
        · constructor
          rw [← spec] at hf
          rw [List.append_nil, ← List.append_assoc, ← List.append_assoc, List.append_left_inj] at hf
          rw [l_is, l1_is]
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
            ← List.append_assoc, ← List.append_assoc, ← List.cons_append, ← List.cons_append,
            ← List.cons_append, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
            List.append_left_inj, List.append_left_inj, List.append_left_inj, hf]
        constructor
        · exact List.suffix_refl_C
        constructor
        · exact back2
        constructor
        have : H2.length = (PartialGrid.horizontal_append_one hpg H.1).length :=
          same_type_same_length_pg H2 (PartialGrid.horizontal_append_one hpg H.1) rfl rfl (by simp) rfl rfl
        rw [this]
        simp [PartialGrid.length]
        rename_i old
        have : hpg.length = old.length :=
          same_type_same_length_pg hpg old rfl rfl rfl rfl spec
        rw [this]
        have : g2.length = H.1.length := H.2.1
        rw [← this]
        simp_all
    | cons head tail =>
      cases to_add with
      | nil =>
        use bot4, head::tail ++ bot3 ++ mid3, up3
        rw [List.nil_append] at spec
        rw [← spec] at hpg
        use PartialGrid.horizontal_append (by simp) hpg g2
        constructor
        · rw [spec, ← List.append_assoc] at hf
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
        rename_i old
        have H : hpg.length = old.length :=
          same_type_same_length_pg hpg old rfl rfl rfl rfl spec
        simp [H, h6]
      | cons heade taile =>
        use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up3
        have lf : is_false (heade :: taile) := by
          have H0 : is_false up4 := right_frontier_is_false hpg
          rw [← spec] at H0
          exact (is_false_append H0).1
        rw [← spec] at hpg
        have H3 := (PartialGrid.extend_bottom_w_len g2 (heade::taile) lf (by simp))
        have H2 := PartialGrid.horizontal_append (by simp) hpg H3.1
        have nonsense : head :: tail ++ [] ++ (heade :: taile ++ bot3 ++ mid3) =
          (head :: tail ++ heade :: taile ++ bot3 ++ mid3) := by simp
        rw [← nonsense]
        use H2
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
        have : H2.length = (PartialGrid.horizontal_append (by simp) hpg
          H3.1).length :=
          same_type_same_length_pg H2 _ rfl rfl rfl rfl rfl
        simp [this, PartialGrid.length]
        rename_i old
        have : hpg.length = old.length :=
          same_type_same_length_pg hpg old rfl rfl rfl rfl spec
        rw [this]
        rw [← H3.2.1]
        constructor
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
      simp [PartialGrid.length, h6.2.1]
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
        rw [← spec.1] at pg
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
          simp [PartialGrid.length]
          rename_i old
          have H : pg.length = old.length :=
            same_type_same_length_pg pg old rfl rfl spec.1 rfl rfl
          rw [H]
          exact len.1
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
          simp [PartialGrid.length]
          rename_i old
          have H : pg.length = old.length :=
            same_type_same_length_pg pg old rfl rfl spec.1 rfl rfl
          rw [H]
          exact len.1
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
          simp [PartialGrid.length, len.1, H2.2.1]
        | cons head1 tail1 =>
          use bot2, mid2 ++ up2 ++ head :: tail ++ head1 :: tail1, nu
          have H1 : is_true (head:: tail) := by
              have H : is_true nb := bottom_frontier_is_true pg
              rw [← spec.1] at H
              exact (is_true_append H).2
          have H2 := (extend_side_w_len g2 (head::tail) H1 (by simp))
          rw [spec.1] at H2
          have H := PartialGrid.vertical_append pg H2.1 (by simp)
          rw [List.append_nil] at H
          use H
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
          simp [PartialGrid.length]
          have : H.length = (PartialGrid.vertical_append pg H2.1 (by simp)).length :=
            same_type_same_length_pg H (PartialGrid.vertical_append pg H2.1 (by simp)) rfl rfl rfl (by simp) rfl
          rw [this, PartialGrid.length]
          rw [← H2.2.1]
          simp [len.1]
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
    simp [PartialGrid.length, botp.2.1]

noncomputable def pg_of_st_grid_style_trivial (h : PartialGrid a b c d e)
    (hst : SemiThue grid_style_trivial (c ++ d ++ e) f) :
    Σ c1 d1 e1,
    (h1 : PartialGrid a b c1 d1 e1) × PLift (f = c1 ++ d1 ++ e1) ×
    PLift (h.length = h1.length) := by
  generalize hl : c ++ d ++ e = L at hst
  induction hst generalizing c d e with
  | refl a =>
    use c, d, e, h
    exact ⟨⟨hl.symm⟩, ⟨rfl⟩⟩
  | reduction h =>
    rename_i l m n o p
    have H := add_empty_cell_w_len h p hl
    rcases H with ⟨nb, nm, nu, h2, fe, _, _, ⟨len⟩⟩
    use nb, nm, nu, h2
    constructor
    · exact ⟨fe.1.symm⟩
    exact ⟨len⟩
  | trans a' b' c' _ _ ih1 ih2 =>
    specialize ih1 h hl
    rcases ih1 with ⟨c2, d2, e2, h2, fe2, hl2⟩
    specialize ih2 h2 fe2.1.symm
    rcases ih2 with ⟨c3, d3, e3, h3, fe3, hl3⟩
    use c3, d3, e3, h3
    constructor
    · exact fe3
    constructor
    exact hl2.1.trans hl3.1

noncomputable def pg_of_move_ones (h : PartialGrid a b c d e) : Σ c1 d1 e1,
    (h1 : PartialGrid a b c1 d1 e1) × PLift (move_ones (c ++ d ++ e) = c1 ++ d1 ++ e1) ×
    PLift (h.length = h1.length) := pg_of_st_grid_style_trivial h (equiv_move_ones_grid_style_trivial)
