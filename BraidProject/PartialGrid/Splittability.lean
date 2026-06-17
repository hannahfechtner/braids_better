import BraidProject.GridData_length
import BraidProject.PartialGrid.Basic
import BraidProject.SignedOptionList
import BraidProject.ConstructiveBasics.FreeMonoid

namespace Braid

namespace PartialGrid

open SignedList

def split_vertically (h : PartialGrid a b c d e)  := ∀ b₁ b₂, b = b₁ ++ b₂ →
  b₁.length > 0 → b₂.length > 0 →
  (Σ mid c1 d1 c2 d2,
  (h1 : PartialGrid a b₁ c1 d1 mid) × (h2 : PartialGrid mid b₂ c2 d2 e) ×
  PLift (c ++ d = c1 ++ d1 ++ c2 ++ d2) ×
  PLift (h.length = h1.length + h2.length)) ⊕
  (Σ d1 d2, (h1 : PartialGrid a b₁ c d1 []) × PLift (h.length = h1.length) ×
    PLift (e = []) × PLift (d = d1 ++ d2) × PLift (b₂ = d2))

noncomputable def splittable_vertically (h : PartialGrid a b c d e) : split_vertically h := by
  induction h with
  | single_cell h =>
    cases h
    all_goals
    intro b₁ b₂ b_is b₁_len b₂_len
    simp only [to_horizontal_edge] at b_is
    apply congr_arg List.length at b_is
    simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, zero_add,
      List.length_append] at b_is
    omega
  | empty a b ha ha1 hb hb1 =>
    intro b₁ b₂ b_is b₁_len b₂_len
    rw [b_is] at hb1
    right
    use a ++ b₁, b₂,  PartialGrid.empty a b₁ ha ha1 b₁_len (is_true_of_append hb1).1
    exact ⟨⟨by simp [PartialGrid.length]⟩, ⟨⟨rfl⟩, ⟨⟨by simp [b_is]⟩, ⟨rfl⟩⟩⟩⟩
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    intro b₃ b₄ b_is b₃_len b₄_len
    rcases List.append_eq_append_sum b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
    · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
      · left
        rw [silly, List.append_nil] at one
        rw [silly, List.nil_append] at two
        rw [one, ← two]
        use up1, bot1, [], bot2, mid2, g1, g2
        simp only [List.append_assoc, List.append_nil, PartialGrid.length]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
      rcases g2_ih _ _ two fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
      · left
        rw [one]
        use mid, (bot1 ++ c1), d1, c2, d2, PartialGrid.horizontal_append_one g1 h1, h2
        refine ⟨⟨?_⟩, ⟨by simp only [PartialGrid.length, h_len, ← add_assoc]⟩⟩
        rw [List.append_assoc, long, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
      right
      rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
      rw [one]
      use d1, d2, PartialGrid.horizontal_append_one g1 h3
      exact ⟨⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩, end_is⟩
    rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
    · left
      rw [silly, List.append_nil] at one
      rw [silly, List.nil_append] at two
      rw [← one, two]
      use up1, bot1, [], bot2, mid2, g1, g2
      simp only [PartialGrid.length, List.append_nil, List.append_assoc]
      exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    rcases g1_ih _ _ one b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
    · left
      rw [two]
      use mid, c1, d1
      match d2 with
      | [] =>
        use c2 ++ bot2, mid2, h1, PartialGrid.horizontal_append_one h2 g2
        rw [List.append_nil, List.append_nil] at long
        refine ⟨⟨?_⟩, ⟨by simp only [PartialGrid.length, h_len, ← add_assoc]⟩⟩
        rw [long]
        simp only [List.append_assoc]
      | d21 :: d22 =>
        use c2, d21 :: d22 ++ bot2 ++ mid2, h1, PartialGrid.horizontal_append h2 g2 (by simp)
        repeat rw [List.append_nil] at long
        simp only [long, h_len, PartialGrid.length, ← add_assoc, List.append_assoc]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    right
    rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
    have H := PartialGrid.left_side_length_pos g2
    rw [end_is.1.1] at H
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 b2 bot2 mid2 up2
    intro b₃ b₄ b_is b₃_len b₄_len
    rcases List.append_eq_append_sum b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
    · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
      · left
        rw [silly, List.append_nil] at one
        rw [silly, List.nil_append] at two
        rw [one, ← two]
        use up1, bot1, mid1, bot2, mid2, g1, g2
        simp only [PartialGrid.length, List.append_assoc]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
      rcases g2_ih _ _ two fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
      · left
        rw [one]
        use mid, bot1, (mid1 ++ c1 ++ d1), c2, d2, PartialGrid.horizontal_append g1 h1 h, h2
        refine ⟨⟨?_⟩, ⟨by simp only [PartialGrid.length, h_len, ← add_assoc]⟩⟩
        rw [List.append_assoc, long]
        simp only [List.append_assoc]
      right
      rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
      rw [one]
      use (mid1 ++ bot2 ++ d1), d2, PartialGrid.horizontal_append g1 h3 h
      refine ⟨⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩, end_is.1, ⟨?_⟩, end_is.2.2⟩
      rw [end_is.2.1.1]
      simp only [List.append_assoc]
    rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
    · left
      rw [silly, List.append_nil] at one
      rw [silly, List.nil_append] at two
      rw [← one, two]
      use up1, bot1, mid1, bot2, mid2, g1, g2
      simp only [PartialGrid.length, List.append_assoc]
      exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    rcases g1_ih _ _ one b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
    · left
      rw [two]
      use mid, c1, d1
      match d2 with
      | [] =>
        use c2 ++ bot2, mid2, h1, PartialGrid.horizontal_append_one h2 g2
        rw [List.append_nil] at long
        refine ⟨⟨?_⟩, ⟨by simp only [PartialGrid.length, h_len, ← add_assoc]⟩⟩
        rw [← List.append_assoc, ← List.append_assoc, long]
        simp only [List.append_assoc]
      | d21 :: d22 =>
        use c2, d21 :: d22 ++ bot2 ++ mid2, h1, PartialGrid.horizontal_append h2 g2 (by simp)
        simp only [← List.append_assoc, long, h_len, PartialGrid.length, ← add_assoc]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    right
    rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
    have H := PartialGrid.left_side_length_pos g2
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
              exact (bottom_middle_frontier_not_both_nil h1 rfl rfl).elim
            | co :: ct => simp
          have hc2 : c2.length > 0 := by
             match c2 with
            | [] =>
              exact (bottom_middle_frontier_not_both_nil h2 rfl rfl).elim
            | co :: ct => simp
          rcases g2_ih _ _ long hc1 hc2 with ⟨mid2, c3, d3, c4, d4, i1, i2, long1, len1⟩ | bad
          · use mid2 ++ mid, c3, d3, c4, d4,
              PartialGrid.vertical_append_one h1 i1, PartialGrid.vertical_append_one h2 i2
            refine ⟨long1, ⟨?_⟩⟩
            simp only [PartialGrid.length, len1.1, len]
            omega
          rcases bad with ⟨d1, d2, h3, len1⟩
          match up2 with
          | [] =>
            use mid, bot2, d1, c2, [], PartialGrid.vertical_append_one h1 h3, h2
            refine ⟨⟨?_⟩, ⟨?_⟩⟩
            · rw [List.append_assoc, List.append_assoc]
              apply (List.append_right_inj bot2).mpr
              simp [List.append_nil, len1.2.2.1.1, len1.2.2.2.1]
            simp [PartialGrid.length, len, ← len1.1.1]
            omega
          | d21 :: d22 =>
            simp only [List.cons_ne_nil] at len1
            exact (len1.2.1.1).elim
        | d21 :: d22 =>
          have H : is_true bot1 := by exact g2.top_side_is_true
          simp only [List.append_nil] at long
          rw [long] at H
          rcases PartialGrid.middle_frontier_spec h2 with H2 | ⟨front, mid, caboose, spec⟩
          · simp only [List.cons_ne_nil] at H2
            exact H2.1.elim
          rw [spec.1] at H
          specialize H (front, false)
          simp at H
      | d11 :: d12 =>
        have H : is_true bot1 := g2.top_side_is_true
        simp only [List.append_nil, List.append_assoc] at long
        rw [long] at H
        rcases PartialGrid.middle_frontier_spec h1 with H2 | ⟨front, mid, caboose, spec⟩
        · simp only [List.cons_ne_nil] at H2
          exact H2.1.elim
        rw [spec.1] at H
        specialize H (front, false)
        simp at H
    rcases bad with ⟨d1, d2, h3, ⟨len⟩, up1_is, ⟨d1h2_empty⟩, ⟨a2h4⟩⟩
    rw [up1_is.1] at g1
    right
    exact (middle_right_frontier_not_both_nil g1 rfl rfl).elim
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 a2 bot2 mid2 up2
    intro a₃ a₄ a_is a₃_len a₄_len
    rcases g1_ih _ _ a_is a₃_len a₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨len⟩⟩ | bad
    · match d1 with
      | [] =>
        have both_c : is_true (c1 ++ c2) :=
            is_true_append h1.bottom_frontier_is_true h2.bottom_frontier_is_true
        have bot1_is : bot1 = c1 ++ c2 := by
          rw [List.append_nil] at long
          rcases PartialGrid.middle_frontier_spec g1 with H | ⟨front, mid, caboose, spec⟩
          · rw [H.1] at h
            simp at h
          rw [spec.1] at long
          simp only [List.cons_append, List.nil_append, List.append_assoc] at long
          rcases PartialGrid.middle_frontier_spec h2 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp only [H.1, List.append_nil] at long
            rw [← long] at both_c
            specialize both_c (front, false)
            simp at both_c
          rw [spec1.1] at long
          simp only [List.cons_append, List.nil_append] at long
          have := SignedList.eq_of_is_true_append_false_append_eq (g2.top_side_is_true) both_c
            (by simp only [List.append_assoc, List.cons_append, List.nil_append]; exact long)
          aesop
        have mid_is : mid1 = d2 := by
          simp only [bot1_is, List.append_assoc, List.append_nil,
            List.append_cancel_left_eq] at long
          exact long
        have c1_len : c1.length > 0 := by
          match c1 with
          | [] => exact (bottom_middle_frontier_not_both_nil h1 rfl rfl).elim
          | c11 :: c12 => simp
        match c2 with
        | [] =>
          left
          rw [List.append_nil] at bot1_is
          subst bot1_is
          use up2 ++ mid, bot2, mid2, [], up2++ [] ++ d2, PartialGrid.vertical_append_one h1 g2
          match up2 with
          | [] =>
            use h2
            exact ⟨⟨by simp [mid_is]⟩, ⟨by grind [PartialGrid.length]⟩⟩
          | up21 :: up22 =>
            use (PartialGrid.extend_left_side_w_length h2 (up21 :: up22)
              (PartialGrid.right_frontier_is_false g2) (by simp)).1
            refine ⟨⟨by simp [mid_is]⟩, ⟨?_⟩⟩
            grind [PartialGrid.length, (PartialGrid.extend_left_side_w_length h2 (up21 :: up22)
              (PartialGrid.right_frontier_is_false g2) (by simp)).2.1]
        | c21 :: c22 =>
          left
          rcases g2_ih _ _  bot1_is c1_len (by simp) with
              ⟨mid3, c3, d3, c4, d4, i1, i2, long1, len1⟩ | ⟨d1, d2', h3, ⟨len1⟩, rest⟩
          · use mid3 ++ mid, c3, d3, c4
            match d2 with
            | [] =>
              simp [mid_is ]at h
            | d21 :: d22 =>
              use d4 ++ up2 ++ d21 :: d22, PartialGrid.vertical_append_one h1 i1,
                PartialGrid.vertical_append h2 i2 (by simp)
              exact ⟨⟨by simp [← List.append_assoc, ← List.append_assoc, long1.1, mid_is]⟩,
                ⟨by grind [PartialGrid.length, len1.1]⟩⟩
          use mid, bot2, d1, c21::c22, d2, PartialGrid.vertical_append_one h1 h3, h2
          exact ⟨⟨by simp [rest.2.1.1, mid_is, rest.1.1, rest.2.2.1]⟩, ⟨by grind [PartialGrid.length]⟩⟩
      | d11 :: d12 =>
        have H0 : is_true bot1 := g2.top_side_is_true
        have bot1_is : bot1 = c1 := by
          rcases PartialGrid.middle_frontier_spec h1 with H | ⟨front, mid, caboose, spec⟩
          · simp only [reduceCtorEq] at H
            exact H.1.elim
          rw [spec.1] at long
          rcases PartialGrid.middle_frontier_spec g1 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp only [H.1, List.append_nil, List.cons_append, List.nil_append,
            List.append_assoc] at long
            rw [long] at H0
            specialize H0 (front, false)
            simp at H0
          rw [spec1.1] at long
          simp only [List.cons_append, List.nil_append, List.append_assoc] at long
          have := SignedList.eq_of_is_true_append_false_append_eq (g2.top_side_is_true) h1.bottom_frontier_is_true
            (by simp only [List.append_assoc, List.cons_append, List.nil_append]; exact long)
          grind
        simp [bot1_is] at long
        match c1 with
        | [] =>
          rw [bot1_is] at g2
          have H := PartialGrid.top_length_pos g2
          simp at H
        | c11 :: c12 =>
          left
          subst bot1_is
          use mid, bot2, mid2 ++ up2 ++ (d11 :: d12), c2, d2,
            PartialGrid.vertical_append h1 g2 (by simp), h2
          exact ⟨⟨by simp [long]⟩, ⟨by grind [PartialGrid.length]⟩⟩
    rcases bad with ⟨d1, d2, h3, ⟨len⟩, ⟨up1_nil⟩, ⟨mid1_is⟩, ⟨a4d2⟩⟩
    right
    have H : d1.length > 0 := by
      match d1 with
      | [] =>
        exact (middle_right_frontier_not_both_nil h3 rfl rfl).elim
      | d11 :: d12 => simp
    use mid2 ++ up2 ++ d1, d2, PartialGrid.vertical_append h3 g2 H
    exact ⟨⟨by simp [PartialGrid.length, len]⟩, ⟨up1_nil⟩, ⟨by simp [mid1_is]⟩, ⟨a4d2⟩⟩

noncomputable def split_horizontally (h : PartialGrid a b c d e) := ∀ a1 a2,
  a = a2 ++ a1 → a1.length > 0 → a2.length > 0 → (Σ mid d1 e1 d2 e2,
  (h1 : PartialGrid a1 b mid d2 e2) × (h2 : PartialGrid a2 mid c d1 e1) ×
  PLift (d1 ++ e1 ++ d2 ++e2 = d ++ e) × PLift (h.length = h1.length + h2.length)) ⊕
  (Σ db c1 drest, (h1 : PartialGrid a1 b c1 drest e) × PLift (d = db ++ c1 ++ drest) ×
  PLift (a2 = db) × PLift (c = []) × PLift (h.length = h1.length))

noncomputable def reflect_one_two (h : PartialGrid a1 b1 c d e) : a1 = FreeGroup.invRev a → b1 = FreeGroup.invRev b →
  (h1 : PartialGrid b a (FreeGroup.invRev e) (FreeGroup.invRev d) (FreeGroup.invRev c)) × PLift (h.length = h1.length) := by
  intro a_eq b_eq
  apply congr_arg FreeGroup.invRev at a_eq
  rw [FreeGroup.invRev_invRev] at a_eq
  rw [← a_eq]
  apply congr_arg FreeGroup.invRev at b_eq
  rw [FreeGroup.invRev_invRev] at b_eq
  rw [← b_eq]
  apply reflect h

noncomputable def reflect_two_five (h : PartialGrid a b1 c d e1) : b1 = FreeGroup.invRev b → e1 = FreeGroup.invRev e →
  (h1 : PartialGrid b (FreeGroup.invRev a) e (FreeGroup.invRev d) (FreeGroup.invRev c)) × PLift (h.length = h1.length) := by
  intro b_eq e_eq
  apply congr_arg FreeGroup.invRev at b_eq
  rw [FreeGroup.invRev_invRev] at b_eq
  rw [← b_eq]
  apply congr_arg FreeGroup.invRev at e_eq
  rw [FreeGroup.invRev_invRev] at e_eq
  rw [← e_eq]
  apply reflect h

noncomputable def reflect_one_two_three (c e) (h : PartialGrid a1 b1 c1 d e) :
    a1 = FreeGroup.invRev a → b1 = FreeGroup.invRev b → c1 = FreeGroup.invRev c →
    (h1 : PartialGrid b a (FreeGroup.invRev e) (FreeGroup.invRev d) c) × PLift (h.length = h1.length) := by
  intro a_eq b_eq c_eq
  apply congr_arg FreeGroup.invRev at a_eq
  rw [FreeGroup.invRev_invRev] at a_eq
  rw [← a_eq]
  apply congr_arg FreeGroup.invRev at b_eq
  rw [FreeGroup.invRev_invRev] at b_eq
  rw [← b_eq]
  apply congr_arg FreeGroup.invRev at c_eq
  rw [FreeGroup.invRev_invRev] at c_eq
  rw [← c_eq]
  apply reflect h



noncomputable def splittable_horizontally (h : PartialGrid a b c d e) :
    split_horizontally h := by
  intro a1 a2 a_is a1_len a2_len
  have H := reflect h
  have split_a : FreeGroup.invRev a = FreeGroup.invRev a1 ++ FreeGroup.invRev a2 := by
    rw [a_is, FreeGroup.invRev_append]
  have splitter := splittable_vertically H.1 _ _ split_a
  rw [FreeGroup.invRev_length, FreeGroup.invRev_length] at splitter
  rcases splitter a1_len a2_len with ⟨mid, d1, e1, d2, e2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
  · left
    use FreeGroup.invRev mid, FreeGroup.invRev e2, FreeGroup.invRev d2, FreeGroup.invRev e1, FreeGroup.invRev d1
    use (reflect_one_two h1 rfl rfl).1, (reflect_two_five h2 rfl rfl).1
    constructor
    · constructor
      apply congr_arg FreeGroup.invRev at long
      simp only [FreeGroup.invRev_append, FreeGroup.invRev_invRev] at long
      simp only [List.append_assoc]
      exact long.symm
    constructor
    simp [H.2.1, h_len, (reflect_one_two h1 rfl rfl).2.1, (reflect_two_five h2 rfl rfl).2.1]
  rcases bad with ⟨d1, d2, h3, len, c_is, d_is, a2_is⟩
  right
  use FreeGroup.invRev d2, [], FreeGroup.invRev d1
  have c_nil : c = [] := FreeGroup.invRev_eq_nil_iff.mp c_is.1
  subst c_nil
  have H0 := reflect_one_two_three e ([] : List (Option ℕ × Bool)) h3 rfl rfl rfl
  use H0.1
  constructor
  · constructor
    have H := congr_arg FreeGroup.invRev d_is.1
    rw [FreeGroup.invRev_invRev] at H
    simp [H]
  constructor
  · have H := congr_arg FreeGroup.invRev a2_is.1
    rw [FreeGroup.invRev_invRev] at H
    exact ⟨H⟩
  constructor
  · exact ⟨rfl⟩
  constructor
  rw [H.2.1, len.1]
  exact H0.2.1
