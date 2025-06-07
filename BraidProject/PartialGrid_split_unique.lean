import BraidProject.PartialGrid_split

def split_vertically_pg_u (h : PartialGrid a b c d e)  := ∀ b₁ b₂, b = b₁ ++ b₂ →
  b₁.length > 0 → b₂.length > 0 →
  (Σ mid c1 d1 c2 d2,
  (h1 : PartialGrid a b₁ c1 d1 mid) × (h2 : PartialGrid mid b₂ c2 d2 e) ×
  PLift (c ++ d = c1 ++ d1 ++ c2 ++ d2) ×
  PLift (h.length = h1.length + h2.length) ×
  (∀ a3 b3 c3 d3 mid2 b4 c4 d4 e4, PartialGrid a3 b3 c3 d3 mid2 →
  PartialGrid mid2 b4 c4 d4 e4 → a3 = a → b3 = b₁ → b4 = b₂ → e4 = e →
  c ++ d = c3 ++ d3 ++ c4 ++ d4 →
  PLift (c3 = c1 ∧ d3 = d1 ∧ mid2 = mid ∧ c4 = c2 ∧ d4 = d2))) ⊕
  (Σ d1 d2, (h1 : PartialGrid a b₁ c d1 []) × PLift (h.length = h1.length) ×
    PLift (e = []) × PLift (d = d1 ++ d2) × PLift (b₂ = d2))

noncomputable def splittable_vertically_of_pg_unique (h : PartialGrid a b c d e) : split_vertically_pg_u h := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp only [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | top_bottom i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | sides i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | top_left i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | adjacent i k h =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | separated i j h =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
  | empty a b ha ha1 hb hb1 =>
    intro b₁ b₂ b_is b₁_len b₂_len
    right
    use a ++ b₁
    have itb₁ : is_true b₁ := by
      rw [b_is] at hb1
      exact (is_true_append hb1).1
    use b₂
    use PartialGrid.empty a b₁ ha ha1 b₁_len itb₁
    constructor
    · exact ⟨by simp [PartialGrid.length]⟩
    constructor
    · exact ⟨rfl⟩
    constructor
    · constructor
      rw [b_is]
      simp
    exact ⟨rfl⟩
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    intro b₃ b₄ b_is b₃_len b₄_len
    rcases List.append_eq_append' b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
    · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
      · left
        rw [silly, List.append_nil] at one
        rw [silly, List.nil_append] at two
        rw [one.1, ← two.1]
        use up1, bot1, [], bot2, mid2
        use g1, g2
        simp [one.1, two.1, PartialGrid.length]
        constructor
        · exact ⟨trivial⟩
        constructor
        · exact ⟨trivial⟩
        intro a3 b3 c3 d3 mid' b4 c4 d4 e4 p1 p2 a_again b1_again b2_again up_again long_again
        constructor
        sorry --simp_all
      rcases g2_ih _ _ two.1 fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩, unique⟩ | bad
      · left
        rw [one.1]
        use mid, (bot1 ++ c1), d1, c2, d2
        use PartialGrid.horizontal_append_one g1 h1
        use h2
        constructor
        · constructor
          rw [List.append_assoc, long, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
        constructor
        · constructor
          simp [PartialGrid.length, h_len, ← add_assoc]
        intro a3 b3 c3 d3 mid' b4 c4 d4 e4 p1 p2 a_again b1_again b2_again up_again long_again
        constructor
        sorry
      right
      rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
      rw [one.1]
      use d1, d2
      use PartialGrid.horizontal_append_one g1 h3
      constructor
      · exact ⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩
      exact end_is
    rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
    · left
      rw [silly, List.append_nil] at one
      rw [silly, List.nil_append] at two
      rw [← one.1, two.1]
      use up1, bot1, [], bot2, mid2, g1, g2
      simp [one.1, two.1, PartialGrid.length]
      constructor
      . exact ⟨trivial⟩
      constructor
      · exact ⟨trivial⟩
      sorry
    rcases g1_ih _ _ one.1 b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
    · left
      rw [two.1]
      use mid, c1, d1
      match d2 with
      | [] =>
        use c2 ++ bot2, mid2
        use h1
        use PartialGrid.horizontal_append_one h2 g2
        rw [List.append_nil, List.append_nil] at long
        constructor
        · rw [long]
          exact ⟨by simp⟩
        constructor
        · exact ⟨by simp [PartialGrid.length, h_len, ← add_assoc]⟩
      | d21 :: d22 =>
        use c2, d21 :: d22 ++ bot2 ++ mid2
        use h1
        use PartialGrid.horizontal_append (by simp) h2 g2
        repeat rw [List.append_nil] at long
        simp [long, h_len, PartialGrid.length, ← add_assoc]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    right
    rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
    have H := PartialGrid.left_length_pos g2
    rw [end_is.1.1] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 b2 bot2 mid2 up2
    intro b₃ b₄ b_is b₃_len b₄_len
    rcases List.append_eq_append' b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
    · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
      · left
        rw [silly, List.append_nil] at one
        rw [silly, List.nil_append] at two
        rw [one.1, ← two.1]
        use up1, bot1, mid1, bot2, mid2
        use g1, g2
        simp [one.1, two.1, PartialGrid.length]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
      rcases g2_ih _ _ two.1 fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
      · left
        rw [one.1]
        use mid, bot1, (mid1 ++ c1 ++ d1), c2, d2
        use PartialGrid.horizontal_append h g1 h1
        use h2
        constructor
        · constructor
          rw [List.append_assoc, long]
          simp
        constructor
        simp [PartialGrid.length, h_len, ← add_assoc]
      right
      rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
      rw [one.1]
      use (mid1 ++ bot2 ++ d1), d2
      use PartialGrid.horizontal_append h g1 h3
      constructor
      · exact ⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩
      constructor
      · exact end_is.1
      constructor
      · rw [end_is.2.1.1]
        simp
        exact ⟨trivial⟩
      exact end_is.2.2
    rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
    · left
      rw [silly, List.append_nil] at one
      rw [silly, List.nil_append] at two
      rw [← one.1, two.1]
      use up1, bot1, mid1, bot2, mid2, g1, g2
      simp [one.1, two.1, PartialGrid.length]
      exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    rcases g1_ih _ _ one.1 b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
    · left
      rw [two.1]
      use mid, c1, d1
      match d2 with
      | [] =>
        use c2 ++ bot2, mid2
        use h1
        use PartialGrid.horizontal_append_one h2 g2
        rw [List.append_nil] at long
        constructor
        · rw [← List.append_assoc,← List.append_assoc, long]
          exact ⟨by simp⟩
        exact ⟨by simp [PartialGrid.length, h_len, ← add_assoc]⟩
      | d21 :: d22 =>
        use c2, d21 :: d22 ++ bot2 ++ mid2
        use h1
        use PartialGrid.horizontal_append (by simp) h2 g2
        simp [← List.append_assoc, long, h_len, PartialGrid.length, ← add_assoc]
        exact ⟨⟨by simp⟩, ⟨trivial⟩⟩
    right
    rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
    have H := PartialGrid.left_length_pos g2
    rw [end_is.1.1] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 up1 a2 bot2 mid2 up2
    intro a₃ a₄ a_is a₃_len a₄_len
    rcases g1_ih _ _ a_is a₃_len a₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨len⟩⟩ | bad
    · match d1 with
      | [] =>
        match d2 with
        | [] =>
          left
          rw [List.append_nil, List.append_nil, List.append_nil] at long
          have hc1 : c1.length > 0 := by
            match c1 with
            | [] =>
              exact (not_both_empty_early h1 rfl rfl).elim
            | co :: ct => simp
          have hc2 : c2.length > 0 := by
             match c2 with
            | [] =>
              exact (not_both_empty_early h2 rfl rfl).elim
            | co :: ct => simp
          rcases g2_ih _ _ long hc1 hc2 with ⟨mid2, c3, d3, c4, d4, i1, i2, long1, len1⟩ | bad
          · use mid2 ++ mid, c3, d3, c4, d4
            use PartialGrid.vertical_append_one h1 i1
            use PartialGrid.vertical_append_one h2 i2
            constructor
            · exact long1
            constructor
            simp [PartialGrid.length, len1.1, len]
            omega
          rcases bad with ⟨d1, d2, h3, len1⟩
          match up2 with
          | [] =>
            use mid, bot2, d1, c2, []
            use PartialGrid.vertical_append_one h1 h3
            use h2
            constructor
            · constructor
              rw [List.append_assoc, List.append_assoc]
              apply (List.append_right_inj bot2).mpr
              rw [List.append_nil, len1.2.2.1.1]
              simp
              exact len1.2.2.2.1.symm
            constructor
            simp [PartialGrid.length, len, ← len1.1.1]
            omega
          | d21 :: d22 =>
            exfalso
            simp at len1
            exact len1.2.1.1
        | d21 :: d22 =>
          have H : is_true bot1 := by exact g2.top_frontier_is_true
          simp at long
          rw [long] at H
          have H2 := middle_frontier_nil_or_caps h2
          rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
          · simp at H2
            exact H2.1.elim
          rw [spec.1] at H
          specialize H (front, false)
          simp [is_true] at H
          exact (H ⟨trivial⟩).1.elim
      | d11 :: d12 =>
        have H : is_true bot1 := by exact g2.top_frontier_is_true
        simp only [List.append_nil, List.append_assoc] at long
        rw [long] at H
        have H2 := middle_frontier_nil_or_caps h1
        rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
        · simp at H2
          exact H2.1.elim
        rw [spec.1] at H
        specialize H (front, false)
        simp [is_true] at H
        exact (H ⟨trivial⟩).1.elim
    rcases bad with ⟨d1, d2, h3, ⟨len⟩, up1_is, ⟨d1h2_empty⟩, ⟨a2h4⟩⟩
    rw [up1_is.1] at g1
    right
    exact (pg_not_mid_right_empty g1).elim
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 a2 bot2 mid2 up2
    intro a₃ a₄ a_is a₃_len a₄_len
    rcases g1_ih _ _ a_is a₃_len a₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨len⟩⟩ | bad
    · match d1 with
      | [] =>
        have both_c : is_true (c1 ++ c2) :=
            is_true_of_true_true h1.bottom_frontier_is_true h2.bottom_frontier_is_true
        have bot1_is : bot1 = c1 ++ c2 := by
          rw [List.append_nil] at long
          rcases middle_frontier_nil_or_caps g1 with H | ⟨front, mid, caboose, spec⟩
          · rw [H.1] at h
            simp at h
          rw [spec.1] at long
          rcases middle_frontier_nil_or_caps h2 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp [H.1] at long
            rw [← long] at both_c
            specialize both_c (front, false)
            simp [is_true] at both_c
            exact (both_c ⟨trivial⟩).1.elim
          rw [spec1.1] at long
          rcases list_splits_somewhere long with ⟨h1⟩ | ⟨tm, one, two⟩ | ⟨fm, one, two⟩
          · exact h1.1
          · match tm with
            | [] =>
              simp at one
              exact one
            | (a, true) :: a1 =>
              simp at two
            | (a, false) :: a1 =>
              have H : is_true bot1 := g2.top_frontier_is_true
              rw [one] at H
              specialize H (a, false)
              simp at H
              exact (H ⟨trivial⟩).1.elim
          match fm with
          | [] =>
            rw [List.append_nil] at one
            exact one
          | (a, true) :: a1 =>
            simp at two
          | (a, false) :: a1 =>
            rw [← one] at both_c
            specialize both_c (a, false)
            simp at both_c
            exact (both_c ⟨trivial⟩).1.elim
        have mid_is : mid1 = d2 := by
          simp [bot1_is] at long
          exact long
        have c1_len : c1.length > 0 := by
          match c1 with
          | [] =>
            exact (not_both_empty_early h1 rfl rfl).elim
          | c11 :: c12 => simp
        match c2 with
        | [] =>
          left
          use up2 ++ mid, bot2, mid2, [], up2++ [] ++ d2
          rw [List.append_nil] at bot1_is
          subst bot1_is
          use PartialGrid.vertical_append_one h1 g2
          match up2 with
          | [] =>
            use h2
            constructor
            · constructor
              simp [mid_is]
            simp [PartialGrid.length, len]
            exact ⟨by omega⟩
          | up21 :: up22 =>
            use (PartialGrid.extend_bottom_w_len h2 (up21 :: up22) (PartialGrid.right_frontier_is_false g2) (by simp)).1
            constructor
            · constructor
              simp [mid_is]
            constructor
            simp [PartialGrid.length, len,
              (PartialGrid.extend_bottom_w_len h2 (up21 :: up22) (PartialGrid.right_frontier_is_false g2) (by simp)).2.1]
            omega
        | c21 :: c22 =>
          left
          rcases g2_ih _ _  bot1_is c1_len (by simp) with
              ⟨mid3, c3, d3, c4, d4, i1, i2, long1, len1⟩ | ⟨d1, d2', h3, ⟨len1⟩, rest⟩
          · use mid3 ++ mid, c3, d3, c4
            match d2 with
            | [] =>
              exfalso
              rw [mid_is] at h
              simp at h
            | d21 :: d22 =>
              use d4 ++ up2 ++ d21 :: d22
              use PartialGrid.vertical_append_one h1 i1
              use PartialGrid.vertical_append h2 i2 (by simp)
              constructor
              · constructor
                rw [← List.append_assoc, ← List.append_assoc, long1.1, mid_is]
                simp
              constructor
              simp [PartialGrid.length, len1.1, len]
              omega
          use mid, bot2, d1, c21::c22, d2
          use PartialGrid.vertical_append_one h1 h3
          use h2
          constructor
          · constructor
            rw [rest.2.1.1, mid_is, rest.1.1, rest.2.2.1]
            simp
          simp [PartialGrid.length, len1, len]
          exact ⟨by omega⟩
      | d11 :: d12 =>
        have H0 : is_true bot1 := by exact g2.top_frontier_is_true
        have bot1_is : bot1 = c1 := by
          rcases middle_frontier_nil_or_caps h1 with H | ⟨front, mid, caboose, spec⟩
          · simp at H
            exact H.1.elim
          rw [spec.1] at long
          rcases middle_frontier_nil_or_caps g1 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp [H.1] at long
            rw [long] at H0
            specialize H0 (front, false)
            simp [is_true] at H0
            specialize H0 ⟨trivial⟩
            exact H0.1.elim
          rw [spec1.1] at long
          simp at long
          rcases list_splits_somewhere long with ⟨h1⟩ | ⟨tm, one, two⟩ | ⟨fm, one, two⟩
          · exact h1.1
          · match tm with
            | [] =>
              simp at one
              exact one
            | (a, true) :: a1 =>
              simp at two
            | (a, false) :: a1 =>
              rw [one] at H0
              specialize H0 (a, false)
              simp at H0
              exact (H0 ⟨trivial⟩).1.elim
          match fm with
          | [] =>
            rw [List.append_nil] at one
            exact one
          | (a, true) :: a1 =>
            simp at two
          | (a, false) :: a1 =>
            have H36 : is_true c1 := h1.bottom_frontier_is_true
            rw [← one] at H36
            specialize H36 (a, false)
            simp at H36
            exact (H36 ⟨trivial⟩).1.elim
        simp [bot1_is] at long
        match c1 with
        | [] =>
          rw [bot1_is] at g2
          exfalso
          have H := PartialGrid.top_length_pos g2
          simp at H
        | c11 :: c12 =>
          left
          use mid, bot2, mid2 ++ up2 ++ (d11 :: d12), c2, d2
          subst bot1_is
          use PartialGrid.vertical_append h1 g2 (by simp)
          use h2
          constructor
          · constructor
            simp [long]
          simp [PartialGrid.length, len]
          exact ⟨by omega⟩
    rcases bad with ⟨d1, d2, h3, ⟨len⟩, ⟨up1_nil⟩, ⟨mid1_is⟩, ⟨a4d2⟩⟩
    right
    use mid2++ up2 ++d1, d2
    have H : d1.length > 0 := by
      match d1 with
      | [] =>
        exfalso
        apply not_both_empty h3 rfl rfl
      | d11 :: d12 => simp
    use PartialGrid.vertical_append h3 g2 H
    constructor
    · simp [PartialGrid.length, len]
      exact ⟨trivial⟩
    constructor
    · exact ⟨up1_nil⟩
    constructor
    · constructor
      simp [mid1_is]
    exact ⟨a4d2⟩
