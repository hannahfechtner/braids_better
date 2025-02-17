import BraidProject.PartialGrids
import Mathlib.Data.List.Infix


theorem List.prefix_of_append {α : Type} {l1 l2 l3: List α} (h : l1 <+: l2) : l1 <+: l2 ++ l3 := by
  rcases h with ⟨rest, spec⟩
  use rest ++ l3
  rw [← spec, List.append_assoc]

theorem List.suffix_append_right (h : l1 <:+ l2) : l1 ++ l3 <:+ l2 ++ l3 := by
  rcases h with ⟨rest, spec⟩
  use rest
  rw [← spec, List.append_assoc]

theorem is_true_cons (h : is_true (a :: b)) : is_true [a] ∧ is_true b := by
  change is_true ([a]++b) at h
  exact is_true_append h

theorem is_true_singleton (h : is_true [a]) : ∃ a', a = (a', true) := by
  rcases a with ⟨c, b⟩
  use c
  simp
  specialize h (c, b) (List.mem_singleton.mpr rfl)
  exact h

def PartialGrid.extend_bottom (h : PartialGrid a b c d e) (a2) (h2 : is_false a2) : PartialGrid (a2 ++ a) b [] (a2 ++ c ++ d) e := by
  cases h with
  | single_grid h => sorry
  | empty a b ha ha1 hb hb => sorry
  | horizontal_append_one g1 g2 => sorry
  | horizontal_append h g1 g2 => sorry
  | vertical_append_one g1 g2 => sorry
  | vertical_append g1 g2 h => sorry


-- theorem yet_another_helper (hup3 : is_false up3) (h : mid3 ++ up3 = (a1, false) :: (b1, true) :: l) :
--     ∃ m4, mid3 = (a1, false) :: (b1, true) :: m4 ∧ l = m4 ++ up3 := by
--   induction up3 using List.reverseRecOn generalizing l with
--   | nil =>
--     use l
--     simp at h
--     constructor
--     · exact h
--     rw [List.append_nil]
--   | append_singleton hu tu ihu =>
--     induction l using List.reverseRecOn with
--     | nil =>
--       exfalso
--       rw [← List.append_assoc] at h
--       change mid3 ++ hu ++ [tu] = [(a1, false)] ++ [(b1, true)] at h
--       apply List.append_singleton_eq_append_singleton at h
--       rw [h.2] at hup3
--       apply is_false_append at hup3
--       simp [is_false] at hup3
--     | append_singleton hl tl _ =>
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
--     induction up3 using List.reverseRecOn generalizing l with
--     | nil =>
--       use l
--       simp at h
--       simp [h]
--     | append_singleton hu tu ihu =>
--       induction l using List.reverseRecOn with
--       | nil =>
--         exfalso
--         have H2 : mid3 ++ hu ++ [tu] = ht ++ [(a1, false)] ++ [(b1, true)] := by simp [h]
--         apply List.append_singleton_eq_append_singleton at H2
--         rw [H2.2] at hup3
--         apply is_false_append at hup3
--         simp [is_false] at hup3
--       | append_singleton hl tl _ =>
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
    induction n using List.reverseRecOn with
    | nil =>
      exfalso
      simp at hn
      rw [hn.1] at ha
      simp at ha
    | append_singleton fn cn _ =>
      use fn
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
      rcases H with ⟨cb, hcb⟩
      rw [hcb]
      use cb
  | horizontal_append_one g1 g2 g1_ih g2_ih => assumption
  | horizontal_append h1 g1 g2 g1_ih g2_ih =>
    rename_i bot2 _ _
    rcases g1_ih with ha | hb
    · rcases g2_ih with hc | hd
      · rw [ha, hc]
        induction bot2 using List.reverseRecOn with
        | nil => left; rfl
        | append_singleton frontb cabooseb _ =>
          have H := is_true_singleton (is_true_append (bottom_frontier_is_true g2)).2
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
      induction bot2 using List.reverseRecOn with
      | nil => rw [List.append_nil]; exact hb
      | append_singleton f2 c2 _ =>
        rcases hb with ⟨f1, c1, h1⟩
        rw [h1]
        have H : ∃ cb, c2 = (cb, true) := is_true_singleton <| (is_true_append (bottom_frontier_is_true g2)).2
        rcases H with ⟨cb, cbspec⟩
        rw [cbspec]
        use f1 ++ [(c1, true)] ++ f2, cb
        simp
    rcases hb with ⟨front1, caboose1, h1⟩
    rcases hd with ⟨front2, caboose2, h2⟩
    right
    use front1 ++ [(caboose1, true)] ++ bot2 ++ front2, caboose2
    rw [h1, h2, ← List.append_assoc]
  | vertical_append_one g1 g2 g1_ih g2_ih => assumption
  | vertical_append g1 g2 h g1_ih g2_ih =>
    right
    rcases g1_ih with h1 | h2
    · rw [h1] at h
      simp at h
    rcases g2_ih with h3 | h4
    · rw [h3, List.nil_append]
      rcases h2 with ⟨f1, c1, spec⟩
      rename_i up2
      use up2 ++ f1, c1
      rw [spec, ← List.append_assoc]
    rcases h2 with ⟨f1, c1, spec1⟩
    rcases h4 with ⟨f2, c2, spec2⟩
    rw [spec1, spec2]
    rename_i up2
    use f2 ++ [(c2, true)] ++ up2 ++ f1, c1
    simp

theorem double_split_helper_two_one  (h : mid2 ++ bot3 = [(a1, false), (b1, true)] ++ b)
    (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)]) (hbot3 : is_true bot3) :
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
    | append_singleton frontbb caboosebb _ =>
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
  induction l using List.reverseRecOn generalizing mid3 with
  | nil => exact double_split_helper_three_one h hm hbot3
  | append_singleton head tail ih =>
    induction mid3 using List.reverseRecOn with
    | nil =>
      rw [List.append_nil] at h
      left
      exact double_split_helper_two_one h hm hbot3
    | append_singleton headm tailm _ =>
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
      have Ht : tail = [] ∨ ∃ front a, tail = front ++ [(a, true)] := by
        sorry
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
     (hbot3 : is_true bot3) (hup3 : is_false up3) (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)])
    (h : (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hm3 : mid3 = [] ∨ ∃ front a, mid3 = front ++ [(a, true)]) :
    (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = m1)) ∨
    (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3)) := by
  induction up3 using List.reverseRecOn generalizing l with
  | nil =>
    rw [List.append_nil] at h
    simp
    have H2 := double_split_helper_three hbot3 hm hm3 h
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


-- theorem final_helper (h : l ++ m = [a, b]) :
--     [a, b] <:+: l ∨ [a, b] <:+: m ∨ l.getLast? = some a ∧ m.get? 0 = some b := by
--   have len := congr_arg List.length h
--   simp at len
--   have H : (l.length = 0 ∧ m.length = 2) ∨ (l.length = 1 ∧ m.length = 1) ∨
--     (l.length = 2 ∧ m.length = 0) := by omega
--   rcases H with ha | hb | hc
--   · right; left
--     use [], []
--     rw [List.nil_append, List.append_nil]
--     rw [List.length_eq_zero.mp ha.1, List.nil_append] at h
--     exact h.symm
--   · right ; right
--     rcases List.length_eq_one.mp hb.1 with ⟨a1, ha1⟩
--     rcases List.length_eq_one.mp hb.2 with ⟨b1, hb1⟩
--     rw [ha1, hb1] at h
--     rw [ha1, hb1]
--     simp [List.getLast?_singleton]
--     simp at h
--     exact h
--   left
--   use [], []
--   rw [List.nil_append, List.append_nil]
--   rw [List.length_eq_zero.mp hc.2, List.append_nil] at h
--   exact h.symm

-- theorem list_get_zero_append {l : List α} (h : l.get? 0 = some a) : (l ++ m).get? 0 = some a := by
--   cases l with
--   | nil =>
--     exfalso
--     simp at h
--   | cons head tail =>
--     simp
--     simp at h
--     exact h

-- theorem infix_helper (h : l ++ m = [a, b] ++ l₂) :
--     [a, b] <:+: l ∨ [a, b] <:+: m ∨ l.getLast? = some a ∧ m.get? 0 = some b := by
--   induction l₂ using List.reverseRecOn generalizing m with
--   | nil => exact final_helper h
--   | append_singleton frontl caboosel ih =>
--     induction m using List.reverseRecOn with
--     | nil =>
--       left
--       use [], frontl ++ [caboosel]
--       rw [List.nil_append]
--       rw [List.append_nil] at h
--       exact h.symm
--     | append_singleton frontm caboosem _ =>
--       rw [← List.append_assoc, ← List.append_assoc] at h
--       apply List.append_singleton_eq_append_singleton at h
--       specialize @ih frontm h.1
--       rcases ih with ha | hb | hc
--       · left; assumption
--       · right; left; refine List.infix_concat_iff.mpr ?_ ; right; assumption
--       right; right;
--       constructor
--       · exact hc.1
--       exact list_get_zero_append hc.2

-- theorem double_cons_of_length_ge_two (h : e.length ≥ 2) : ∃ c d e', e = c :: d :: e' := by
--   cases e with
--   | nil => simp at h
--   | cons head tail =>
--     cases tail with
--     | nil => simp at h
--     | cons head1 tail1 => use head, head1, tail1

-- theorem iltcch (h : l1 ++ [a, b] = c :: d :: e) : a = c ∧ b = d ∨ [a, b] <:+: d :: e := by
--   cases l1 with
--   | nil =>
--     left
--     simp at h
--     exact ⟨h.1, h.2.1⟩
--   | cons head tail =>
--     rw [List.cons_append, List.cons.injEq] at h
--     right
--     use tail, []
--     rw [List.append_nil]
--     exact h.2

-- theorem infix_length_two_cons_cons (h : [a, b] <:+: c :: d :: e) : (a = c ∧ b = d) ∨ [a, b] <:+: d :: e := by
--   rcases h with ⟨l1, l2, hl⟩
--   induction l2 using List.reverseRecOn generalizing e with
--   | nil =>
--     rw [List.append_nil] at hl
--     exact iltcch hl
--   | append_singleton head tail ih =>
--     simp at hl
--     induction e using List.reverseRecOn with
--     | nil =>
--       exfalso
--       apply congr_arg List.length at hl
--       simp at hl
--       omega
--     | append_singleton he te ihe =>
--       have H : l1 ++ [a, b] ++ head = c :: d :: he := by
--         have H2 : l1 ++ a :: b :: (head ++ [tail]) = l1 ++ a :: b :: head ++ [tail] := by simp
--         rw [H2] at hl
--         change l1 ++ a :: b :: head ++ [tail] = c :: d :: he ++ [te] at hl
--         apply List.append_singleton_eq_append_singleton at hl
--         rw [← hl.1]
--         simp
--       rcases @ih he H with h1 | h2
--       · left; exact h1
--       right
--       change [a, b] <:+: d :: he ++ [te]
--       apply List.infix_concat_iff.mpr
--       right
--       exact h2

-- you need the other nonsense to prove it. maybe this should be a helper
-- theorem infix_append_length_two (h : [a, b] <:+: (l ++ m)) :
--     [a, b] <:+: l ∨ (¬ [a, b] <:+: l ∧ [a, b] <:+: m) ∨
--     (¬ [a, b] <:+: l ∧ l.getLast? = some a ∧ m.get? 0 = some b) := by
--   rcases h with ⟨l₁, l₂, hl⟩
--   induction l₁ generalizing l with
--   | nil => sorry
--   | cons head tail ih =>
--     cases l with
--     | nil =>
--       right; left
--       constructor
--       · intro h
--         simp only [List.infix_nil, reduceCtorEq] at h
--       use head :: tail, l₂
--       rw [List.nil_append] at hl
--       exact hl
--     | cons headl taill =>
--       simp only [List.cons_append, List.cons.injEq] at hl
--       specialize @ih taill hl.2
--       rcases ih with ha | hb | hc
--       · left
--         exact List.infix_cons ha
--       · rcases eq_or_ne a headl with hd | he
--         · rw [hd]
--           cases taill with
--           | nil =>
--             right; left
--             constructor
--             · intro h
--               rcases h with ⟨t₁, t₂, ht⟩
--               apply congr_arg List.length at ht
--               simp at ht
--               omega
--             rw [hd] at hb
--             exact hb.2
--           | cons tb tailb =>
--             rcases eq_or_ne b tb with hf | hg
--             · left; use [], tailb
--               rw [hf]
--               rfl
--             right; left
--             constructor
--             · intro h1
--               cases infix_length_two_cons_cons h1 with
--               | inl h => exact hg h.2
--               | inr h =>
--                 rw [← hd] at h
--                 exact hb.1 h
--             rw [← hd]
--             exact hb.2
--         right; left
--         constructor
--         · intro h
--           sorry
--         exact hb.2
--       sorry

-- theorem is_true_infix (h : is_true l) (h2 : m <:+: l) : is_true m := by
--   rcases h2 with ⟨l1, l2, hl⟩
--   rw [← hl] at h
--   apply is_true_append at h
--   exact (is_true_append h.1).2

-- theorem is_false_infix (h : is_false l) (h2 : m <:+: l) : is_false m := by
--   rcases h2 with ⟨l1, l2, hl⟩
--   rw [← hl] at h
--   apply is_false_append at h
--   exact (is_false_append h.1).2

-- theorem is_true_getLast_some {l : List (Option ℕ × Bool)}
--     (h : l.getLast? = some (a, b)) (h1 : is_true l) : is_true [(a, b)] := by
--   unfold is_true
--   simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
--   induction l using List.reverseRecOn with
--   | nil => simp at h
--   | append_singleton c d _ =>
--     simp at h
--     rw [h] at h1
--     apply is_true_append at h1
--     simp [is_true] at h1
--     exact h1.2

-- theorem getLast?_append_some {a b : List α} (h : (a ++b).getLast? = some c) :
--     a.getLast? = some c ∨ b.getLast? = some c := by
--   induction b using List.reverseRecOn with
--   | nil =>
--     left
--     rw [List.append_nil] at h
--     exact h
--   | append_singleton =>
--     right
--     simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq]
--     simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
--       Option.some.injEq] at h
--     exact h

-- theorem List.getLast?_cons_some (h : taill.getLast? = some a) : (headl :: taill).getLast? = some a := by
--   induction taill using List.reverseRecOn with
--   | nil => simp at h
--   | append_singleton front caboose ih =>
--     simp at h
--     rw [h]
--     change ([headl] ++ (front ++ [a])).getLast? = some a
--     refine getLast?_eq_some_iff.mpr ?_
--     use headl :: front
--     rfl

-- theorem List.getlast?_append_right (h : l.get? 0 = some b) : (l ++ [a]).get? 0 = some b := by
--   cases l with
--   | nil => simp at h
--   | cons head tail =>
--     simp
--     simp at h
--     exact h

-- theorem List.infix_append_right (h : i <:+: l) : i <:+: l ++ m := by
--   rcases h with ⟨a1, a2, ha⟩
--   use a1, a2++m
--   rw [← ha]
--   simp

-- theorem basic_helper (h : [a, b] = l ++ m) : [a, b] <:+: l ∨ [a, b] <:+: m ∨ l.getLast? = some a ∧ m.get? 0 = some b := by
--   have H : (l.length = 0 ∧ m.length = 2) ∨ (l.length = 1 ∧ m.length = 1) ∨ (l.length = 2 ∧ m.length = 0) := by
--     apply congr_arg List.length at h
--     simp at h
--     omega
--   rcases H with ha | hb | hc
--   · right; left
--     use [], []
--     have H : l = [] := List.length_eq_zero.mp ha.1
--     rw [H, List.nil_append] at h
--     exact h
--   · right; right
--     rcases List.length_eq_one.mp hb.1 with ⟨a1, ha1⟩
--     rcases List.length_eq_one.mp hb.2 with ⟨b1, hb1⟩
--     rw [ha1, hb1] at h
--     rw [ha1, hb1]
--     simp [List.getLast?_singleton]
--     simp at h
--     exact ⟨h.1.symm, h.2.symm⟩
--   left
--   use [], []
--   have H : m = [] := List.length_eq_zero.mp hc.2
--   rw [H, List.append_nil] at h
--   rw [h, List.append_nil, List.nil_append]


-- theorem last_helper (h : [a, b] ++ l₂ = l ++ m) : [a, b] <:+: l ∨ [a, b] <:+: m ∨ l.getLast? = some a ∧ m.get? 0 = some b := by
--   induction l₂ using List.reverseRecOn generalizing m with
--   | nil => exact basic_helper h
--   | append_singleton front caboose ih =>
--     induction m using List.reverseRecOn with
--     | nil => left; use [], front ++ [caboose]; rw [List.nil_append]; rw [List.append_nil] at h; exact h
--     | append_singleton l a _ =>
--       rw [← List.append_assoc, ← List.append_assoc] at h
--       apply List.append_singleton_eq_append_singleton at h
--       specialize @ih l h.1
--       rcases ih with ha | hb | hc
--       · left; exact ha
--       · right; left; exact List.infix_append_right hb
--       right; right
--       constructor
--       · exact hc.1
--       exact List.getlast?_append_right hc.2

-- theorem infix_append_length_two_n_snd (h : [a, b] <:+: (l ++ m)) :
--     [a, b] <:+: l ∨ [a, b] <:+: m ∨
--     (l.getLast? = some a ∧ m.get? 0 = some b) := by
--   rcases h with ⟨l₁, l₂, hl⟩
--   induction l₁ generalizing l with
--   | nil => exact last_helper hl
--   | cons head tail ih =>
--     cases l with
--     | nil =>
--       right; left
--       use head :: tail, l₂
--       rw [List.nil_append] at hl
--       exact hl
--     | cons headl taill =>
--       simp only [List.cons_append, List.cons.injEq] at hl
--       specialize @ih taill hl.2
--       rcases ih with ha | hb | hc
--       · left
--         exact List.infix_cons ha
--       · rcases eq_or_ne a headl with hd | he
--         · rw [hd]
--           cases taill with
--           | nil =>
--             right; left
--             rw [hd] at hb
--             exact hb
--           | cons tb tailb =>
--             rcases eq_or_ne b tb with hf | hg
--             · left; use [], tailb
--               rw [hf]
--               rfl
--             right; left
--             rw [← hd]
--             exact hb
--         right; left
--         exact hb
--       right; right
--       constructor
--       · exact List.getLast?_cons_some hc.1
--       exact hc.2

-- theorem double_split_helper'' {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
--     (hbot2 : is_true bot2) (hbot3 : is_true bot3) (hup3 : is_false up3)
--     (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)])
--     (hm3 : mid3 = [] ∨ ∃ front a, mid3 = front ++ [(a, true)])
--     (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l) :
--     (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = bot2 ++ m1)) ∨
--     (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3)) := by
--   rw [← List.append_assoc, ← List.append_assoc, List.append_assoc (bot2 ++ mid2 ++ bot3)] at h
--   have hm1 : ¬ mid2.getLast? = some (a1, false) := by sorry
--   have hm2 : ¬ mid3.getLast? = some (a1, false) := by sorry
--   have h' : [(a1, false), (b1, true)] <:+: bot2 ++ mid2 ++ bot3 ++ (mid3 ++ up3) := by
--     use k, l
--     simp [h.symm]
--   rcases infix_append_length_two_n_snd h' with ha | hb | hc
--   · rcases infix_append_length_two_n_snd ha with haa | hab | hac
--     · rcases infix_append_length_two_n_snd haa with haaa | haab | haac
--       · have := is_true_infix hbot2 haaa
--         simp [is_true] at this
--       · left;
--         rcases haab with ⟨l1, l2, spec⟩
--         use l1, l2
--         constructor
--         · exact spec.symm

--       have := is_true_getLast_some haac.2.1 hbot2
--       simp [is_true] at this
--     · have := is_true_infix hbot3 hab.2
--       simp [is_true] at this
--     rcases getLast?_append_some hac.2.1 with h1 | h2
--     · have := is_true_getLast_some h1 hbot2
--       simp [is_true] at this
--     exact (hm1 h2).elim
--   · right
--     rcases infix_append_length_two hb.2 with hba | hbb | hbc
--     · exact hba
--     · have := is_false_infix hup3 hbb.2
--       simp [is_false] at this
--     exact (hm2 hbc.2.1).elim
--   right
--   exfalso

-- theorem double_split_helper {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
--     (hbot2 : is_true bot2) (hbot3 : is_true bot3) (hup3 : is_false up3)
--     (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)])
--     (hm3 : mid3 = [] ∨ ∃ front a, mid3 = front ++ [(a, true)])
--     (h : [(a1, false), (b1, true)] <:+: bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3) :
--     [(a1, false), (b1, true)] <:+: mid2 ∨ [(a1, false), (b1, true)] <:+: mid3 := by
--   rw [← List.append_assoc, ← List.append_assoc, List.append_assoc (bot2 ++ mid2 ++ bot3)] at h
--   have hm1 : ¬ mid2.getLast? = some (a1, false) := by sorry
--   have hm2 : ¬ mid3.getLast? = some (a1, false) := by sorry
--   rcases infix_append_length_two_n_snd h with ha | hb | hc
--   · rcases infix_append_length_two_n_snd ha with haa | hab | hac
--     · rcases infix_append_length_two_n_snd haa with haaa | haab | haac
--       · have := is_true_infix hbot2 haaa
--         simp [is_true] at this
--       · left; exact haab
--       have := is_true_getLast_some haac.1 hbot2
--       simp [is_true] at this
--     · have := is_true_infix hbot3 hab
--       simp [is_true] at this
--     rcases getLast?_append_some hac.1 with h1 | h2
--     · have := is_true_getLast_some h1 hbot2
--       simp [is_true] at this
--     exact (hm1 h2).elim
--   · right
--     rcases infix_append_length_two_n_snd hb with hba | hbb | hbc
--     · exact hba
--     · have := is_false_infix hup3 hbb
--       simp [is_false] at this
--     exact (hm2 hbc.1).elim
--   right
--   exfalso
--   rcases getLast?_append_some hc.1 with h1 | h2
--   · rcases getLast?_append_some h1 with h3 | h4
--     · have := is_true_getLast_some h3 hbot2
--       simp [is_true] at this
--     exact hm1 h4
--   have := is_true_getLast_some h2 hbot3
--   simp [is_true] at this

  -- · rcases infix_append_length_two (a1, false) (b1, true) (by use l1, l2) with ⟨l5, l6, ha⟩ | ⟨l3, l4, ha, hb⟩ | ⟨hc, hd, he⟩
  --   · rcases infix_append_length_two (a1, false) (b1, true) (by use l5, l6) with ⟨l7, l8, ha⟩ | ⟨l3, l4, ha, hb⟩ | ⟨hc, hd, he⟩
  --     · rw [ha] at hbot2
  --       apply is_true_append at hbot2
  --       have hd := is_true_append hbot2.1
  --       simp [is_true] at hd
  --     · left
  --       use l3, l4
  --     exfalso; sorry -- hc.1 has a contradiction -- bot3 is true, and thus cannot end in false
  --   · rw [ha] at hbot3
  --     apply is_true_append at hbot3
  --     have hd := is_true_append hbot3.1
  --     simp [is_true] at hd
  --   exfalso; sorry -- hc.1 has a contradiction - neither mid2 nor bot2 can end in false
  -- · rcases infix_append_length_two (by use l3, l4) with ⟨l1, l2, ha⟩ | ⟨l3, l4, ha⟩ | hc
  --   · right; use l1, l2
  --   · rw [ha] at hup3
  --     apply is_false_append at hup3
  --     have hd := is_false_append hup3.1
  --     simp [is_false] at hd
  --   exfalso; sorry -- hc.2 has a contradiction - up3 is false and cannot end in true
  -- exfalso; sorry --hc.1 has a contradiction - neither mid3 nor bot3 can end in false

-- theorem double_split_helper'' {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
--     (hbot2 : is_true bot2) (hbot3 : is_true bot3) (hup3 : is_false up3)
--     (hm : mid2 = [] ∨ ∃ front a, mid2 = front ++ [(a, true)])
--     (hm3 : mid3 = [] ∨ ∃ front a, mid3 = front ++ [(a, true)])
--     (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l) :
--     (∃ m1 m2,(mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = bot2 ++ m1)) ∨
--     (∃ m3 m4, (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3)) := by
--   have H := double_split_helper hbot2 hbot3 hup3 hm hm3 h
--   rcases H with ⟨m1, m2, h1⟩ | ⟨m3, m4, h2⟩
--   · left; use m1, m2
--     constructor
--     · exact h1
--     rw [h1] at h
--     sorry
--   sorry
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
    (hm3 : mid3 = [] ∨ ∃ front a, mid3 = front ++ [(a, true)]) :
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
        have H :=  skeleton_one_cons hg fe b_is ha1 (by assumption) (by assumption) (by rw [← a_is] at i_is; exact i_is) (by assumption)
        rcases H with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix, List.nil_prefix⟩⟩⟩
    | cons head tail =>
      cases b2 with
      | nil =>
        rw [← k_is, ← l_is,]
        rw [List.append_nil] at b_is
        have H := skeleton_cons_one hg a_is ha1 hb1 i_is (by assumption) b_is hb
        rcases H with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix, List.nil_prefix⟩⟩⟩
      | cons headb tailb =>
        rw [a_is] at ha1
        rw [b_is] at hb1
        have H3 := bool_split (is_false_append ha1).2 (is_true_append hb1).1 i_is
        rw [← k_is, ← l_is, a_is, b_is, H3.1, H3.2]
        have H := skeleton_cons_cons hg (is_false_append ha1).1 (is_true_append hb1).2 (by assumption)
        rcases H with ⟨b, m, u, h3, h4⟩
        use b, m, u
        exact ⟨h3, ⟨h4, ⟨List.nil_suffix, List.nil_prefix⟩⟩⟩
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
    specialize @ih2 k₂ l eq_rest
    rcases ih2 with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
    use bot2 ++ bot1, mid1, up1
    constructor
    · exact PartialGrid.horizontal_append_one g1 pg1
    constructor
    · simp [k_is, fe1, k₁_is]
    constructor
    · exact h5
    exact (List.prefix_append_right_inj bot2).mpr h6
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3
    have  hbot2 : is_true bot2 := bottom_frontier_is_true g1
    have hbot3 : is_true bot3 := bottom_frontier_is_true g2
    have hup3 : is_false up3 := right_frontier_is_false g2
    have hup2 : is_false up2 := right_frontier_is_false g1
    have H : mid2.length ≠ 1 := mid_length_neq_one g1
    rcases double_split_horiz hbot2 hbot3 hup3 fe (middle_frontier_nil_or_ends_true g1) (middle_frontier_nil_or_ends_true g2) with hl | hr
    · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
      have H : SemiThue_one_step grid_style' (up2 ++ b3) (k₂ ++ i ++ l) := by
        have H := equiv_paths g2
        rw [← k2_is, ← i_is] at H
        exact H
      have H2 : SemiThue grid_style' (up2 ++ b3) (k₂ ++ j ++ l) :=
        (one_step_equiv_reg.mpr H).trans _ _ _ (SemiThue.reduction hg)
      specialize g2_ih k2_is.symm
      rcases g2_ih with ⟨bot3, mid3, up3, hpg, hf⟩
      use bot2, mid2 ++ bot3++mid3, up3
      constructor
      · exact PartialGrid.horizontal_append h g1 hpg
      simp [k_is, k1_is, k2_is, hf]
    rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
    have H : SemiThue_one_step grid_style' (a2 ++ b2) (k ++ i ++ (l₁ ++ up2)) := by
      have := equiv_paths g1
      rw [← l2_is, ← i_is] at this
      rw [← List.append_assoc]
      exact this
    have H2 : SemiThue grid_style' (a2 ++ b2) (k ++ j ++ (l₁ ++ up2)) :=
      (one_step_equiv_reg.mpr H).trans _ _ _ (SemiThue.reduction hg)
    have H3 : bot2 ++ mid2 ++ up2 = k ++ [(a1, false), (b1, true)] ++ (l₁ ++ up2) := by
      rw [← l2_is]
      simp
    specialize @g1_ih k (l₁ ++ up2) H3
    rcases g1_ih with ⟨bot4, mid4, up4, hpg, hf, ⟨to_add, spec⟩, h6⟩
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
        constructor
        · rfl
        exact List.prefix_of_append h6
      | cons heade taile =>
        use bot4, (heade :: taile) ++ bot3 ++ mid3, up3
        constructor
        · have lf : is_false (heade :: taile) := by
            have H0 : is_false up4 := by exact right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_append H0).1
          have H := PartialGrid.extend_bottom g2 (heade::taile) lf
          rw [← spec] at hpg
          have H2 := PartialGrid.horizontal_append_one hpg H
          simp at H2
          simp
          exact H2
        constructor
        · rw [l_is, l1_is]
          rw [← spec] at hf
          rw [← List.append_assoc, ← List.append_assoc] at hf
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
          have H : bot4 ++ [head] ++ tail = k ++ j ++ l₁ := List.append_cancel_right hf
          change bot4 ++ ([head] ++ tail ++ bot3 ++ mid3) ++ up3 = _
          rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, H]
          simp [l_is, l1_is]
        constructor
        · rfl
        assumption
      | cons heade taile =>
        use bot4, head::tail ++ (heade :: taile) ++ bot3 ++ mid3, up3
        constructor
        · have lf : is_false (heade :: taile) := by
            have H0 : is_false up4 := by exact right_frontier_is_false hpg
            rw [← spec] at H0
            exact (is_false_append H0).1
          have H := PartialGrid.extend_bottom g2 (heade::taile) lf
          rw [← spec] at hpg
          have H2 := PartialGrid.horizontal_append (by simp) hpg H
          simp at H2
          simp
          exact H2
        constructor
        · rw [l_is, l1_is]
          rw [← spec] at hf
          rw [← List.append_assoc, ← List.append_assoc] at hf
          apply List.append_cancel_right at hf
          conv => rhs; rw [← List.append_assoc, ← List.append_assoc, ← hf]
          simp
        exact ⟨List.suffix_refl up3, h6⟩
  | vertical_append_one g1 g2 ih1 ih2 =>
      rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
      rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
      rw [← i_is] at eq_rest
      have H1 : SemiThue_one_step grid_style' (b3 ++ bot2) (k ++ i ++ l₁) := by
        rw [← eq_rest]
        exact equiv_paths g2
      rw [i_is] at eq_rest
      specialize @ih2 _ _ eq_rest
      rcases ih2 with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
      use bot1, mid1, up1 ++ up2
      constructor
      · exact PartialGrid.vertical_append_one g1 pg1
      constructor
      · rw [l_is, l₂_is, ← List.append_assoc, fe1, ← List.append_assoc]
      constructor
      · exact List.suffix_append_right h5
      exact h6
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a b bot mid up a2 bot2 mid2 up2
    have H : [(a1, false), (b1, true)] <:+: mid2 ∨ [(a1, false), (b1, true)] <:+: mid := by sorry
    rcases H with ⟨m1, m2, hm⟩ | hm2
    · rw [← hm] at fe
      sorry
    sorry


theorem step_two' (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b) (hb1 : b.length > 0) :
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
    rename_i i j k l m
    specialize ih ell (one_step_equiv_reg.mpr h1)
    rcases ih with ⟨bot, mid, up, h3, h4⟩
    have H := add_cell h3 h2 h4
    rcases H with ⟨b, m, u, h3, h4⟩
    use b, m, u
    exact ⟨h3, h4.1⟩

-- theorem step_two (ha : is_false a) (ha1 : a.length > 0) (hb : is_true b) (hb1 : b.length > 0) :
--     SemiThue grid_style' (a ++ b) c → (∃ bot mid up, PartialGrid a b bot mid up ∧ bot ++ mid ++ up = c) := by
--   intro h
--   generalize ell : a ++ b = el at h
--   induction one_step_equiv_reg.mp h with
--   | refl x =>
--     rw [← ell]
--     use [], a ++ b, []
--     constructor
--     · exact PartialGrid.empty _ _ ha1 ha hb1 hb
--     rw [List.append_nil, List.nil_append]
--   | one_step h1 h2 ih =>
--     rename_i i j k l m
--     specialize ih ell (one_step_equiv_reg.mpr h1)
--     rcases grid_style_split h2 with ⟨a1, b1, i_is⟩
--     rcases ih with ⟨bot1, mid1, up1, pg1, fe⟩
--     rw [i_is] at fe
--     induction pg1 generalizing m k l with
--     | single_grid h =>
--       exfalso
--       rw [List.append_nil] at fe
--       exact over_up_neq_false_true fe
--     | empty a b ha ha1 hb hb =>
--       simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
--                 List.singleton_append] at fe
--       rcases over_up_splits_at_i ha hb ha1 fe with ⟨a1, a2, b1, b2, a_is, b_is, i_is, k_is, l_is⟩
--       cases a1 with
--       | nil =>
--         rw [List.nil_append] at a_is
--         rw [a_is] at ha1
--         rw [← k_is]
--         cases b2 with
--         | nil =>
--           rw [← l_is, List.append_nil]
--           rw [List.append_nil] at b_is
--           rw [b_is] at hb1
--           rw [← a_is,← b_is] at i_is
--           exact skeleton_one_one h2 (by assumption) (by assumption) (by assumption) i_is
--         | cons head tail =>
--           rw [← l_is]
--           apply skeleton_one_cons h2 _ b_is (by assumption) (by assumption) (by assumption)
--           · rw [← a_is] at i_is
--             exact i_is
--           assumption
--           rw [a_is, b_is, i_is]
--           simp
--       | cons head tail =>
--         cases b2 with
--         | nil =>
--           rw [← k_is, ← l_is,]
--           rw [List.append_nil] at b_is
--           exact skeleton_cons_one h2 a_is ha hb i_is (by assumption) b_is hb1
--         | cons headb tailb =>
--           rw [a_is] at ha
--           rw [b_is] at hb
--           have H3 := bool_split (is_false_append ha).2 (is_true_append hb).1 i_is
--           rw [← k_is, ← l_is, a_is, b_is, H3.1, H3.2]
--           exact skeleton_cons_cons h2 (is_false_append ha).1 (is_true_append hb).2 (by assumption)
--     | horizontal_append_one g1 g2 ih1 ih2 =>
--       rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
--       have hk : ∃ k₁ k₂, k = k₁ ++ k₂ ∧ bot3 ++ mid3 ++ up3 = k₂ ++ [(a1, false), (b1, true)] ++ l
--         ∧ k₁ = bot2 :=  big_split_first (bottom_frontier_is_true g1) fe
--       rcases big_split_first (bottom_frontier_is_true g1) fe with ⟨k₁, k₂, k_is, eq_rest, k₁_is⟩
--       rw [← i_is] at eq_rest
--       have H1 : SemiThue grid_style' (up2 ++ b3) (k₂ ++ i ++ l) := by
--         rw [← eq_rest]
--         exact one_step_equiv_reg.mpr (equiv_paths g2)
--       rw [i_is] at eq_rest
--       specialize @ih2 (right_frontier_is_false g1) (left_length_pos g2) (top_frontier_is_true g2) (top_length_pos g2) k₂ l (up2 ++ b3)
--         (one_step_equiv_reg.mp H1) rfl (H1.trans _ _ _ (SemiThue.reduction h2)) eq_rest
--       rcases ih2 with ⟨bot1, mid1, up1, pg1, fe1⟩
--       use bot2 ++ bot1, mid1, up1
--       constructor
--       · exact PartialGrid.horizontal_append_one g1 pg1
--       rw [List.append_assoc, List.append_assoc, ← List.append_assoc bot1, fe1, ← k₁_is, ← List.append_assoc, ← List.append_assoc, k_is]
--     | horizontal_append h g1 g2 g1_ih g2_ih =>
--       rename_i a2 b2 bot2 mid2 up2 b3 bot3 mid3 up3 ml
--       have  hbot2 : is_true bot2 := bottom_frontier_is_true g1
--       have hbot3 : is_true bot3 := bottom_frontier_is_true g2
--       have hup3 : is_false up3 := right_frontier_is_false g2
--       have hup2 : is_false up2 := right_frontier_is_false g1
--       have H : mid2.length ≠ 1 := mid_length_neq_one g1
--       rcases double_split_horiz hbot2 hbot3 hup3 fe (middle_frontier_nil_or_ends_true g1) (middle_frontier_nil_or_ends_true g2) with hl | hr
--       · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
--         have H : SemiThue_one_step grid_style' (up2 ++ b3) (k₂ ++ i ++ l) := by
--           have H := equiv_paths g2
--           rw [← k2_is, ← i_is] at H
--           exact H
--         have H2 : SemiThue grid_style' (up2 ++ b3) (k₂ ++ j ++ l) :=
--           (one_step_equiv_reg.mpr H).trans _ _ _ (SemiThue.reduction h2)
--         specialize @g2_ih hup2 (left_length_pos g2) (top_frontier_is_true g2) (top_length_pos g2) k₂ l (up2 ++ b3) H rfl H2 (by rw [k2_is])
--         rcases g2_ih with ⟨bot3, mid3, up3, hpg, hf⟩
--         use bot2, mid2 ++ bot3++mid3, up3
--         constructor
--         · exact PartialGrid.horizontal_append ml g1 hpg
--         simp [k_is, k1_is, k2_is, hf]
--       rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
--       have H : SemiThue_one_step grid_style' (a2 ++ b2) (k ++ i ++ (l₁ ++ up2)) := by
--         have := equiv_paths g1
--         rw [← l2_is, ← i_is] at this
--         rw [← List.append_assoc]
--         exact this
--       have H2 : SemiThue grid_style' (a2 ++ b2) (k ++ j ++ (l₁ ++ up2)) :=
--         (one_step_equiv_reg.mpr H).trans _ _ _ (SemiThue.reduction h2)
--       have H3 : bot2 ++ mid2 ++ up2 = k ++ [(a1, false), (b1, true)] ++ (l₁ ++ up2) := by
--         rw [← l2_is]
--         simp
--       specialize @g1_ih ha ha1 (top_frontier_is_true g1) (top_length_pos g1) k (l₁ ++ up2) (a2 ++ b2) H rfl H2 H3
--       rcases g1_ih with ⟨bot4, mid4, up4, hpg, hf⟩
--       --hbot2 hup2 l₁ l₂ (up2 ++ b3) (one_step_equiv_reg.mp (equiv_paths g1)) rfl (SemiThue.reduction h1) l_is
--       sorry
--     | vertical_append_one g1 g2 ih1 ih2 =>
--       rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
--       rcases big_split (right_frontier_is_false g1) fe with ⟨l₁, l₂, l_is, eq_rest, l₂_is⟩
--       rw [← i_is] at eq_rest
--       have H1 : SemiThue_one_step grid_style' (b3 ++ bot2) (k ++ i ++ l₁) := by
--         rw [← eq_rest]
--         exact equiv_paths g2
--       rw [i_is] at eq_rest
--       specialize @ih2 (left_frontier_is_false g2) (left_length_pos g2) (top_frontier_is_true g2)
--         (top_length_pos g2) k l₁ (b3 ++ bot2) H1 rfl
--         ((one_step_equiv_reg.mpr H1).trans _ _ _ (SemiThue.reduction h2)) eq_rest
--       rcases ih2 with ⟨bot1, mid1, up1, pg1, fe1⟩
--       use bot1, mid1, up1 ++ up2
--       constructor
--       · exact PartialGrid.vertical_append_one g1 pg1
--       rw [← List.append_assoc, fe1, List.append_assoc, List.append_right_inj, ← l₂_is, l_is]
--     | vertical_append g1 g2 h g1_ih g2_ih => sorry
