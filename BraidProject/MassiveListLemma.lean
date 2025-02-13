import BraidProject.PartialGrids

theorem is_true_cons (h : is_true (a :: b)) : is_true [a] ∧ is_true b := by
  change is_true ([a]++b) at h
  exact is_true_append h
-- theorem helper1 (h1 : is_false up3) (h2 : is_true bot3) (h : bot3 ++ mid3 ++ up3 = [(a1, false), (b1, true)] ++ l) :
--     ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3 := by
--   have hbot3 : bot3 = [] := by
--     cases bot3 with
--     | nil => rfl
--     | cons headb tailb =>
--       exfalso
--       simp at h
--       rw [h.1] at h2
--       simp [is_true] at h2
--   induction l using List.list_reverse_induction generalizing up3 with
--   | base =>
--     rw [List.append_nil] at h
--     have h3 : up3 = [] := by
--       induction up3 using List.list_reverse_induction with
--       | base => rfl
--       | ind front caboose _ =>
--         exfalso
--         rw [← List.append_assoc] at h
--         change _ = [(a1, false)] ++ [(b1, true)] at h
--         apply List.append_singleton_eq_append_singleton at h
--         rw [h.2] at h1
--         have h3 := (is_false_append h1).2 (b1, true) (List.mem_singleton.mpr rfl)
--         simp at h3
--     have h4 : mid3 = [(a1, false), (b1, true)] := by
--       rw [hbot3, h3, List.nil_append, List.append_nil] at h
--       exact h
--     rw [h4, h3]
--     use [], []
--     exact ⟨rfl, rfl⟩
--   | ind head tail ih =>
--     induction up3 using List.list_reverse_induction with
--     | base =>
--       simp at h
--       rw [hbot3, List.nil_append] at h
--       use [], head ++ [tail]
--       rw [List.nil_append, List.append_nil]
--       exact ⟨h, rfl⟩
--     | ind front caboose _ =>
--       rw [← List.append_assoc, ← List.append_assoc] at h
--       apply List.append_singleton_eq_append_singleton at h
--       specialize @ih front (is_false_append h1).1 h.1
--       rcases ih with ⟨m3, m4, hm1, hm2⟩
--       use m3, m4
--       constructor
--       · exact hm1
--       simp [h.2, hm2]

-- theorem helper_nb3 (h : tailm2 ++ (bot3 ++ (mid3 ++ up3)) = (a1, false) :: (b1, true) :: l) :
--     (∃ m1 m2, headm2 :: tailm2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ ht = [] ++ m1) ∨
--     ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3 := by
--   induction l using List.list_reverse_induction generalizing up3 with
--   | base =>
--     have H : up3 = [] := by sorry
--     rw [H]
--     rw [H, List.append_nil] at h
--     sorry
--   | ind front caboose ih =>
--     induction up3 using List.list_reverse_induction with
--     | base => sorry
--     | ind front1 caboose1 ih1 =>
--       have H : tailm2 ++ (bot3 ++ (mid3 ++ front1)) = (a1, false) :: (b1, true) :: front := by
--         rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at h
--         change _ = [(a1, false)] ++ [(b1, true)] ++ front ++ [caboose] at h
--         apply List.append_singleton_eq_append_singleton at h
--         simp at h
--         exact h.1
--       rcases @ih front1 H with ⟨m1, m2, hm12, k_is⟩ | ⟨m3, m4, hm34, l_is⟩
--       · sorry
--       sorry

-- theorem yet_another_helper (hup3 : is_false up3) (h : mid3 ++ up3 = (a1, false) :: (b1, true) :: l) :
--     ∃ m4, mid3 = (a1, false) :: (b1, true) :: m4 ∧ l = m4 ++ up3 := by
--   induction up3 using List.list_reverse_induction generalizing l with
--   | base =>
--     use l
--     simp at h
--     constructor
--     · exact h
--     rw [List.append_nil]
--   | ind hu tu ihu =>
--     induction l using List.list_reverse_induction with
--     | base =>
--       exfalso
--       rw [← List.append_assoc] at h
--       change mid3 ++ hu ++ [tu] = [(a1, false)] ++ [(b1, true)] at h
--       apply List.append_singleton_eq_append_singleton at h
--       rw [h.2] at hup3
--       apply is_false_append at hup3
--       simp [is_false] at hup3
--     | ind hl tl _ =>
--       have H : is_false hu := by
--         apply is_false_append at hup3
--         exact hup3.1
--       rw [← List.append_assoc] at h
--       change mid3 ++ hu ++ [tu] = [(a1, false)] ++ [(b1, true)] ++ (hl ++ [tl]) at h
--       rw [← List.append_assoc] at h
--       apply List.append_singleton_eq_append_singleton at h
--       specialize @ihu hl H h.1
--       rw [h.2]
--       rcases ihu with ⟨m4, hm1, hm2⟩
--       use m4
--       constructor
--       · exact hm1
--       simp [hm2]

-- theorem another_helper (ht : is_true tail) (hup3 : is_false up3) (h : tail ++ (mid3 ++ up3) = (a1, false) :: (b1, true) :: l) :
--     ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3 := by
--   cases tail with
--   | nil =>
--     simp at h
--     use []
--     simp
--     exact yet_another_helper hup3 h
--   | cons head tail =>
--     simp at h
--     rw [h.1] at ht
--     simp [is_true] at ht

-- theorem helper_one_mid (hup3 : is_false up3) (hht : ht.length > 0) (hbot3 : is_true bot3)
--     (h : [] ++ bot3 ++ mid3 ++ up3 = ht ++ [(a1, false), (b1, true)] ++ l) :
--     ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3 := by
--   simp at h
--   induction bot3 generalizing ht with
--   | nil =>
--     simp at h
--     use ht
--     induction up3 using List.list_reverse_induction generalizing l with
--     | base =>
--       use l
--       simp at h
--       simp [h]
--     | ind hu tu ihu =>
--       induction l using List.list_reverse_induction with
--       | base =>
--         exfalso
--         have H2 : mid3 ++ hu ++ [tu] = ht ++ [(a1, false)] ++ [(b1, true)] := by simp [h]
--         apply List.append_singleton_eq_append_singleton at H2
--         rw [H2.2] at hup3
--         apply is_false_append at hup3
--         simp [is_false] at hup3
--       | ind hl tl _ =>
--         have H :  mid3 ++ hu ++ [tu] = ht ++ ((a1, false) :: [(b1, true)]) ++ hl ++ [tl] := by simp [h]
--         apply List.append_singleton_eq_append_singleton at H
--         simp at H
--         have H2 : is_false hu := by
--           apply is_false_append at hup3
--           exact hup3.1
--         specialize @ihu hl H2 H.1
--         rcases ihu with ⟨m4, hm1, hm2⟩
--         use m4
--         constructor
--         · exact hm1
--         rw [H.2, hm2]
--         simp
--   | cons head tail ih =>
--     rcases List.exists_cons_of_length_pos hht with ⟨headht, tailht, htt⟩
--     rw [htt] at h
--     simp at h
--     change is_true ([head] ++ tail) at hbot3
--     have Ht : is_true tail := by
--       apply is_true_append at hbot3
--       exact hbot3.2
--     rcases Nat.eq_zero_or_pos tailht.length with h0 | hn0
--     · have H : tailht = [] := List.length_eq_zero.mp h0
--       rw [H, List.nil_append] at h
--       apply another_helper Ht hup3 h.2
--     rcases @ih tailht hn0 Ht h.2 with ⟨m3, m4, one, two⟩
--     use m3, m4


-- theorem helper_no_bot2 (ht_len : ht.length > 0) (hup3 : is_false up3) (hbot3 : is_true bot3) (h : mid2 ++ bot3 ++ mid3 ++ up3 = ht ++ [(a1, false), (b1, true)] ++ l) :
--     (∃ m1 m2, mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ ht = [] ++ m1) ∨
--      ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3 := by
--   induction mid2 generalizing ht with
--   | nil =>
--     right
--     exact helper_one_mid hup3 ht_len hbot3 h
--   | cons headm2 tailm2 ih =>
--     simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at ih
--     rcases List.exists_cons_of_length_pos ht_len with ⟨head, tail, htt⟩
--     rw [htt] at h
--     simp at h
--     rcases Nat.eq_zero_or_pos tail.length with h0 | hn0
--     · have H : tail = [] := List.length_eq_zero.mp h0
--       rw [H, List.nil_append] at h
--       exact helper_nb3 h.2
--     · rcases @ih tail hn0 h.2 with ⟨m1, m2, hm12, k_is⟩ | ⟨m3, m4, hm34, l_is⟩
--       · left
--         use headm2 :: m1, m2
--         constructor
--         · simp [hm12]
--         rw [← k_is, List.nil_append, h.1, htt]
--       right
--       use m3, m4
--       constructor
--       · simp
--         exact hm34
--       exact l_is

-- theorem double_split_helper {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
--     (hbot2 : is_true bot2) (hbot3 : is_true bot3) (hup3 : is_false up3) (H : mid2.length ≠ 1)
--     (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l) :
--     (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = bot2 ++ m1)) ∨
--     (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3)) := by
--   induction k generalizing bot2 with
--   | nil =>
--     have hbot2 : bot2 = [] := by
--       cases bot2
--       · rfl
--       simp at h
--       rw [h.1] at hbot2
--       simp [is_true] at hbot2
--     rw [hbot2, List.nil_append, List.nil_append] at h
--     rw [hbot2]
--     cases mid2 with
--     | nil =>
--       right
--       rw [List.nil_append] at h
--       exact helper1 hup3 hbot3 h
--     | cons headm tailm =>
--       cases tailm with
--       | nil => simp at H
--       | cons headmm tailmm =>
--         simp at h
--         left
--         rw [h.1, h.2.1]
--         use [], tailmm
--         exact ⟨rfl, rfl⟩
--   | cons head tail ih =>
--     cases bot2 with
--     | nil =>
--       rw [List.nil_append] at h
--       exact helper_no_bot2 (by simp) hup3 hbot3 h
--     | cons headb2 tailb2 =>
--       simp at h
--       have H : is_true tailb2 := by
--         change is_true ([headb2] ++ tailb2) at hbot2
--         apply is_true_append at hbot2
--         exact hbot2.2
--       simp only [List.append_assoc, List.cons_append, List.singleton_append] at ih
--       specialize @ih tailb2 H h.2
--       rcases ih with ⟨m1, m2, hm12, k_is⟩ | ⟨m3, m4, hm34, l_is⟩
--       · left
--         use m1, m2
--         constructor
--         · simp at hm12
--           simp
--           exact hm12
--         simp
--         exact ⟨h.1.symm, k_is⟩
--       right
--       use m3, m4
--       constructor
--       · simp at hm34
--         simp
--         exact hm34
--       exact l_is
theorem middle_frontier_nil_or_ends_true (h : PartialGrid a b c d e) : d = [] ∨ ∃ front caboose,
    d = front ++ [(caboose, true)] := by
  induction h with
  | single_grid h =>
    left; rfl
  | empty a b ha ha1 hb hb =>
    right
    generalize hn : a ++ b = n
    induction n using List.list_reverse_induction with
    | base =>
      exfalso
      simp at hn
      rw [hn.1] at ha
      simp at ha
    | ind fn cn _ =>
      use fn
      have H : ∃ cb, cn = (cb, true) := by sorry
      rcases H with ⟨cb, hcb⟩
      rw [hcb]
      use cb
  | horizontal_append_one g1 g2 g1_ih g2_ih => assumption
  | horizontal_append h1 g1 g2 g1_ih g2_ih =>
    rename_i bot2 _ _
    rcases g1_ih with ha | hb
    · rcases g2_ih with hc | hd
      · rw [ha, hc]
        induction bot2 using List.list_reverse_induction with
        | base => left; rfl
        | ind frontb cabooseb _ =>
          have H : ∃ cb, cabooseb = (cb, true) := by sorry
          rcases H with ⟨cb, cbspec⟩
          rw [cbspec]
          right; use frontb, cb ; rw [List.nil_append, List.append_nil]
      right; rw [ha, List.nil_append]
      rcases hd with ⟨f1, c1, h1⟩
      use bot2 ++ f1, c1
      rw [h1, ← List.append_assoc]
    rcases g2_ih with hc | hd
    · right; rw [hc, List.append_nil];
      rcases hc with ⟨f1, c1, h1⟩
      induction bot2 using List.list_reverse_induction with
      | base => rw [List.append_nil]; exact hb
      | ind f2 c2 _ =>
        rcases hb with ⟨f1, c1, h1⟩
        rw [h1]
        have H : ∃ cb, c2 = (cb, true) := by sorry
        rcases H with ⟨cb, cbspec⟩
        rw [cbspec]
        use f1 ++ [(c1, true)] ++ f2, cb
        simp
    rcases hb with ⟨front1, caboose1, h1⟩
    rcases hd with ⟨front2, caboose2, h2⟩
    right
    use front1 ++ [(caboose1, true)] ++ front2, caboose2
    rw [h1, h2, ← List.append_assoc] ; sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => assumption
  | vertical_append g1 g2 h g1_ih g2_ih =>sorry

theorem double_split_helper_two_one  (h : mid2 ++ bot3 = [(a1, false), (b1, true)] ++ b)
    (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)]) (hbot3 : is_true bot3) :
    (∃ m2, mid2 = [(a1, false), (b1, true)] ++ m2) := by
  induction bot3 using List.list_reverse_induction generalizing b with
  | base =>
    rw [List.append_nil] at h
    use b
  | ind frontb cabooseb ihb =>
    induction b using List.list_reverse_induction with
    | base =>
      rw [List.append_nil, ← List.append_assoc] at h
      change _ = [(a1, false)] ++ [(b1, true)] at h
      apply List.append_singleton_eq_append_singleton at h
      rcases hm with is_nil | ⟨frontm, endm, hfe⟩
      · exfalso
        rw [is_nil, List.nil_append] at h
        rw [h.1] at hbot3
        apply is_true_append at hbot3
        simp [is_true] at hbot3
      rw [hfe] at h
      have H0 := congr_arg List.length h.1
      simp at H0
      have H1 : frontm = [] := List.length_eq_zero.mp (by omega)
      have H2 : frontb = [] := List.length_eq_zero.mp (by omega)
      rw [H1, H2] at h
      simp at h
    | ind frontbb caboosebb _ =>
      rw [← List.append_assoc, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      apply is_true_append at hbot3
      exact @ihb frontbb h.1 hbot3.1

theorem double_split_helper_two_three (h : bot3 ++ mid3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hbot3 : is_true bot3) :
    ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 := by
  induction bot3 generalizing k with
  | nil => use k, l; simp at h; simp [h]
  | cons head tail ih =>
    cases k with
    | nil =>
      rw [List.nil_append] at h
      simp at h
      rw [h.1] at hbot3
      simp [is_true] at hbot3
    | cons headk tailk =>
      simp only [List.cons_append,List.cons.injEq] at h
      have h2 : is_true tail := (is_true_cons hbot3).2
      exact @ih tailk h.2 h2

theorem double_split_helper_three_one_s (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)])
    (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)]) (hbot3 : is_true bot3) :
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
    simp [is_true] at hbot3
  have : bot3.length ≠ 1 := by
    intro h2
    have Hb : ∃ a, bot3 = [a] := List.length_eq_one.mp h2
    rcases Hb with ⟨a, ha⟩
    rw [ha] at hbot3
    simp [is_true] at hbot3
    change _ = [(a.1, a.2)] at ha
    rw [hbot3] at ha
    rw [ha] at h
    rcases hm with H1 | ⟨frontm, caboosem, hmm⟩
    · simp [H1] at h
    rw [hmm] at h
    have h_len := congr_arg List.length h
    simp at h_len
    have H : frontm = [] := List.length_eq_zero.mp (by omega)
    have H1 : mid3 = [] := List.length_eq_zero.mp (by omega)
    rw [H, H1, List.nil_append, List.append_nil] at h
    simp at h
  have H : bot3 = [] := List.length_eq_zero.mp (by omega)
  rw [H, List.append_nil] at h
  have H : mid2.length ≠ 1 := by
    intro hm_length
    rcases List.length_eq_one.mp hm_length with ⟨a, ha⟩
    rw [ha] at h
    simp only [List.singleton_append, List.cons.injEq] at h
    rw [h.1] at ha
    rw [ha] at hm
    simp only [List.cons_ne_self, false_or] at hm
    rcases hm with ⟨a2, a3, ha2⟩
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
    (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)])  (hbot3 : is_true bot3) :
    (∃ m2, mid2 = [(a1, false), (b1, true)] ++ m2) ∨ ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ [] = m4 := by
  rcases double_split_helper_three_one_s h hm hbot3 with h1 | ⟨m3, hm3⟩
  · left; exact h1
  right; use m3, []; simp [hm3]

theorem double_split_helper_three_two_s (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)] ++ l)
    (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)]) (hbot3 : is_true bot3) :
    (∃ m2, mid2 = [(a1, false), (b1, true)] ++ m2) ∨
    ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 := by
  induction l using List.list_reverse_induction generalizing mid3 with
  | base => exact double_split_helper_three_one h hm hbot3
  | ind head tail ih =>
    induction mid3 using List.list_reverse_induction with
    | base =>
      rw [List.append_nil] at h
      left
      exact double_split_helper_two_one h hm hbot3
    | ind headm tailm _ =>
      rw [← List.append_assoc, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      specialize @ih headm h.1
      rcases ih with ha | ⟨m3, m4, hm34⟩
      · left; exact ha
      right
      rw [hm34.1, hm34.2, ← h.2]
      use m3, m4 ++ [tailm]
      simp

theorem double_split_helper_three_two (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)] ++ l)
    (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)]) (hbot3 : is_true bot3) :
    (∃ m1 m2, mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ [] = m1) ∨
    ∃ m3 m4, mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 := by
  rcases double_split_helper_three_two_s h hm hbot3 with ⟨m2, hm2⟩ | h2
  · left; use [], m2
    rw [hm2]
    simp
  right; exact h2

theorem double_split_helper_three {mid2 bot3 mid3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
     (hbot3 : is_true bot3) (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)])
     (hm3 : mid3 = [] ∨ ∃ front a, mid3 = front ++ [(a, true)])
    (h : mid2 ++ bot3 ++ mid3 = k ++ [(a1, false), (b1, true)] ++ l) :
    (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = m1)) ∨
    (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4)) := by
  induction k generalizing mid2 with
  | nil => exact double_split_helper_three_two h hm hbot3 --its own lemma
  | cons head tail ih =>
    cases mid2 with
    | nil =>
      right
      exact double_split_helper_two_three h hbot3 -- its own lemma
    | cons head tail =>
      simp at h
      simp at hm
      have Ht : tail = [] ∨ ∃ front a, tail = front ++ [(a, true)] := by sorry
      simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
        List.nil_eq_append] at ih
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
     (hbot3 : is_true bot3) (hup3 : is_false up3) (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)])
    (h : (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hm3 : mid3 = [] ∨ ∃ front a, mid3 = front ++ [(a, true)]) :
    (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = m1)) ∨
    (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3)) := by
  induction up3 using List.list_reverse_induction generalizing l with
  | base =>
    rw [List.append_nil] at h
    simp
    have H2 := double_split_helper_three hbot3 hm hm3 h
    simp at H2
    exact H2
  | ind front caboose ih =>
    induction l using List.list_reverse_induction with
    | base =>
      exfalso
      have H3 : [(a1, false), (b1, true)] = [(a1, false)] ++ [(b1, true)] := rfl
      rw [List.append_nil, ← List.append_assoc, H3, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      rw [h.2] at hup3
      apply is_false_append at hup3
      simp [is_false] at hup3
    | ind headl taill =>
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
def isInfix (l₂ l : List α) : Prop := ∃ l₁ l₃, l = l₁ ++ l₂ ++ l₃

theorem final_helper (h : l ++ m = [a, b]) :
    isInfix [a, b] l ∨ isInfix [a, b] m ∨ l.getLast? = some a ∧ m.get? 0 = some b := by
  have len := congr_arg List.length h
  simp at len
  have H : (l.length = 0 ∧ m.length = 2) ∨ (l.length = 1 ∧ m.length = 1) ∨
    (l.length = 2 ∧ m.length = 0) := by omega
  rcases H with ha | hb | hc
  · right; left
    use [], []
    rw [List.nil_append, List.append_nil]
    rw [List.length_eq_zero.mp ha.1, List.nil_append] at h
    exact h
  · right ; right
    rcases List.length_eq_one.mp hb.1 with ⟨a1, ha1⟩
    rcases List.length_eq_one.mp hb.2 with ⟨b1, hb1⟩
    rw [ha1, hb1] at h
    rw [ha1, hb1]
    simp [List.getLast?_singleton]
    simp at h
    exact h
  left
  use [], []
  rw [List.nil_append, List.append_nil]
  rw [List.length_eq_zero.mp hc.2, List.append_nil] at h
  exact h

theorem list_get_zero_append {l : List α} (h : l.get? 0 = some a) : (l ++ m).get? 0 = some a := by
  cases l with
  | nil =>
    exfalso
    simp at h
  | cons head tail =>
    simp
    simp at h
    exact h

theorem infix_helper (h : l ++ m = [a, b] ++ l₂) :
    isInfix [a, b] l ∨ isInfix [a, b] m ∨ l.getLast? = some a ∧ m.get? 0 = some b := by
  induction l₂ using List.list_reverse_induction generalizing m with
  | base => exact final_helper h
  | ind frontl caboosel ih =>
    induction m using List.list_reverse_induction with
    | base =>
      left
      use [], frontl ++ [caboosel]
      rw [List.nil_append]
      rw [List.append_nil] at h
      exact h
    | ind frontm caboosem _ =>
      rw [← List.append_assoc, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      specialize @ih frontm h.1
      rcases ih with ha | hb | hc
      · left; assumption
      · right; left; sorry
      right; right;
      constructor
      · exact hc.1
      exact list_get_zero_append hc.2

theorem infix_append_length_two (h : isInfix [a, b] (l ++ m)) :
    isInfix [a, b] l ∨ isInfix [a, b] m ∨ l.getLast? = some a ∧ m.get? 0 = some b := by
  rcases h with ⟨l₁, l₂, hl⟩
  induction l₁ generalizing l with
  | nil => sorry
  | cons head tail ih =>
    cases l with
    | nil =>
      right; left
      use head :: tail, l₂
      rw [List.nil_append] at hl
      exact hl
    | cons headl taill =>
      simp only [List.cons_append, List.cons.injEq] at hl
      specialize @ih taill hl.2
      sorry
theorem double_split_helper' {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
    (hbot2 : is_true bot2) (hbot3 : is_true bot3) (hup3 : is_false up3)
    (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)])
    (hm3 : mid3 = [] ∨ ∃ front a, mid3 = front ++ [(a, true)])
    (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l) :
    (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = bot2 ++ m1)) ∨
    (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3)) := by
  induction bot2 generalizing k with
  | nil =>
    rw [List.nil_append] at h
    exact double_split_helper_four hbot3 hup3 hm h hm3
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
    (hbot2 : is_true bot2) (hbot3 : is_true bot3) (hup3 : is_false up3)
    (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)])
    (hm3 : mid3 = [] ∨ ∃ front a, mid3 = front ++ [(a, true)]):
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
  apply List.append_cancel_right at h
  apply List.append_cancel_right at h
  apply List.append_cancel_right at h
  use bot2 ++ mid2, bot3 ++ m3
  constructor
  · simp
    simp at h
    exact h.symm
  constructor
  · rfl
  simp [hm34]
  exact l_is

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
    rcases grid_style_split h2 with ⟨a1, b1, i_is⟩
    rcases ih with ⟨bot1, mid1, up1, pg1, fe⟩
    rw [i_is] at fe
    induction pg1 generalizing m k l with
    | single_grid h =>
      exfalso
      rw [List.append_nil] at fe
      exact over_up_neq_false_true fe
    | empty a b ha ha1 hb hb =>
      simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
                List.singleton_append] at fe
      rcases over_up_splits_at_i ha hb ha1 fe with ⟨a1, a2, b1, b2, a_is, b_is, i_is, k_is, l_is⟩
      cases a1 with
      | nil =>
        rw [List.nil_append] at a_is
        rw [a_is] at ha1
        rw [← k_is]
        cases b2 with
        | nil =>
          rw [← l_is]
          rw [List.append_nil] at b_is
          rw [b_is] at hb1
          rw [List.append_nil]
          rw [← a_is,← b_is] at i_is
          exact skeleton_one_one h2 (by assumption) (by assumption) (by assumption) i_is
        | cons head tail =>
          rw [← l_is]
          apply skeleton_one_cons h2 _ b_is (by assumption) (by assumption) (by assumption)
          · rw [← a_is] at i_is
            exact i_is
          assumption
          rw [a_is, b_is, i_is]
          simp
      | cons head tail =>
        cases b2 with
        | nil =>
          rw [← k_is, ← l_is,]
          rw [List.append_nil] at b_is
          exact skeleton_cons_one h2 a_is ha hb i_is (by assumption) b_is hb1
        | cons headb tailb =>
          rw [a_is] at ha
          rw [b_is] at hb
          have H3 := bool_split (is_false_append ha).2 (is_true_append hb).1 i_is
          rw [← k_is, ← l_is, a_is, b_is, H3.1, H3.2]
          exact skeleton_cons_cons h2 (is_false_append ha).1 (is_true_append hb).2 (by assumption)
    | horizontal_append_one g1 g2 ih1 ih2 =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      have hk : ∃ k₁ k₂, k = k₁ ++ k₂ ∧ bot3 ++ mid3 ++ up3 = k₂ ++ [(a1, false), (b1, true)] ++ l
        ∧ k₁ = bot2 :=  big_split_first (bottom_frontier_is_true g1) fe
      rcases big_split_first (bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
      rw [← i_is] at eq_rest
      have H1 : SemiThue grid_style' (up2 ++ b3) (k₂ ++ i ++ l) := by
        rw [← eq_rest]
        exact one_step_equiv_reg.mpr (equiv_paths g2)
      rw [i_is] at eq_rest
      specialize @ih2 (right_frontier_is_false g1) (left_length_pos g2) (top_frontier_is_true g2) (top_length_pos g2) k₂ l (up2 ++ b3)
        (one_step_equiv_reg.mp H1) rfl (H1.trans _ (SemiThue.reduction h2)) eq_rest
      rcases ih2 with ⟨bot1, mid1, up1, pg1, fe1⟩
      use bot2 ++ bot1, mid1, up1
      constructor
      · exact PartialGrid.horizontal_append_one g1 pg1
      rw [List.append_assoc, List.append_assoc, ← List.append_assoc bot1, fe1, ← k₁_is, ← List.append_assoc, ← List.append_assoc, k_is]
    | horizontal_append h g1 g2 g1_ih g2_ih =>
      rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3 ml
      have  hbot2 : is_true bot2 := bottom_frontier_is_true g1
      have hbot3 : is_true bot3 := bottom_frontier_is_true g2
      have hup3 : is_false up3 := right_frontier_is_false g2
      have H : mid2.length ≠ 1 := mid_length_neq_one g1
      rcases double_split_horiz hbot2 hbot3 hup3 fe (middle_frontier_nil_or_ends_true g1) (middle_frontier_nil_or_ends_true g2) with hl | hr
      · sorry
      sorry
    | vertical_append_one g1 g2 ih1 ih2 =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
      rw [← i_is] at eq_rest
      have H1 : SemiThue_one_step grid_style' (b3 ++ bot2) (k ++ i ++ l₁) := by
        rw [← eq_rest]
        exact equiv_paths g2
      rw [i_is] at eq_rest
      specialize @ih2 (left_frontier_is_false g2) (left_length_pos g2) (top_frontier_is_true g2)
        (top_length_pos g2) k l₁ (b3 ++ bot2) H1 rfl
        ((one_step_equiv_reg.mpr H1).trans _ (SemiThue.reduction h2)) eq_rest
      rcases ih2 with ⟨bot1, mid1, up1, pg1, fe1⟩
      use bot1, mid1, up1 ++ up2
      constructor
      · exact PartialGrid.vertical_append_one g1 pg1
      rw [← List.append_assoc, fe1, List.append_assoc, List.append_right_inj, ← l₂_is, l_is]
    | vertical_append g1 g2 h g1_ih g2_ih => sorry
