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

def PartialGrid.extend_bottom (h : PartialGrid a b c d e) (a2) (h2 : is_false a2) (h3 : a2 ≠ []) : PartialGrid (a2 ++ a) b [] (a2 ++ c ++ d) e := by
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
    rcases double_split_horiz hbot2 (Or.inl hbot3) hup3 fe (middle_frontier_nil_or_caps g1) (middle_frontier_nil_or_caps g2) with hl | hr
    · rcases hl with ⟨k₁, k₂, k_is, k1_is, k2_is⟩
      specialize g2_ih k2_is.symm
      rcases g2_ih with ⟨bot3, mid3, up3, hpg, hf⟩
      use bot2, mid2 ++ bot3++mid3, up3
      constructor
      · exact PartialGrid.horizontal_append h g1 hpg
      simp [k_is, k1_is, k2_is, hf]
    rcases hr with ⟨l₁, l₂, l_is, l1_is, l2_is⟩
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
          have H := PartialGrid.extend_bottom g2 (heade::taile) lf (by simp)
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
          have H := PartialGrid.extend_bottom g2 (heade::taile) lf (by simp)
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
      specialize @ih2 _ _ eq_rest
      rcases ih2 with ⟨bot1, mid1, up1, pg1, fe1, h5, h6⟩
      use bot1, mid1, up1 ++ up2
      constructor
      · exact PartialGrid.vertical_append_one g1 pg1
      constructor
      · rw [l_is, l₂_is, ← List.append_assoc, fe1, ← List.append_assoc]
      exact ⟨List.suffix_append_right h5, h6⟩
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a b bot mid up a2 bot2 mid2 up2
    have := double_split_horiz (bottom_frontier_is_true g2) (Or.inr (right_frontier_is_false g2))
      (right_frontier_is_false g1) fe (middle_frontier_nil_or_caps g2) (middle_frontier_nil_or_caps g1)
    rcases this with ⟨k1, k2, k_is, k1_is, k2_is⟩ | ⟨l1, l2, l_is, l1_is, l2_is⟩
    · sorry
    sorry


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
    rename_i i j k l m
    specialize ih ell (one_step_equiv_reg.mpr h1)
    rcases ih with ⟨bot, mid, up, h3, h4⟩
    have H := add_cell h3 h2 h4
    rcases H with ⟨b, m, u, h3, h4⟩
    use b, m, u
    exact ⟨h3, h4.1⟩
