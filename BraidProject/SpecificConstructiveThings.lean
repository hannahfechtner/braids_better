import BraidProject.Additions.List
import BraidProject.PartialGrid.Basic

--This files provides data-carrying lemmas about unfinished frontiers

open SignedList

private def PrefixData.of_is_true_prefix_unfinished_frontier (h1 : is_true bot3) (h : bot3 ++ mid3 ++ up3 = k₂ ++ [(a1, false), (b1, true)] ++ l) :
    List.PrefixData bot3 k₂ := by
  induction k₂ generalizing bot3 with
  | nil =>
    cases bot3 with
    | nil => exact List.PrefixData.nil
    | cons head tail =>
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq] at h
      rw [h.1] at h1
      simp [is_true] at h1
  | cons head tail ih =>
    cases bot3 with
    | nil => exact List.PrefixData.nil
    | cons head1 tail1 =>
      simp only [List.cons_append, List.cons.injEq] at h
      specialize @ih tail1 (is_true_of_cons h1).2 h.2
      rw [h.1]
      exact (List.PrefixData.cons head) ih

private def PrefixData.false_prefix_of_unfinished_frontiers_eq (h1 : is_false t3) (h : tk ++ [(a1, false), (b1, true)] ++ l =
    t3 ++ (f, false) :: (m ++ [(c, true)]) ++ up3) : List.PrefixData t3 tk := by
  induction tk generalizing t3 with
  | nil =>
    cases t3 with
    | nil => exact List.PrefixData.nil
    | cons head tail =>
      cases tail with
      | nil =>
        simp at h
      | cons ht tt =>
        simp at h
        rw [← h.2.1] at h1
        specialize h1 (b1, true)
        simp at h1
  | cons head tail ih =>
    cases t3 with
    | nil =>
      exact List.PrefixData.nil
    | cons ht tt =>
      simp at h
      specialize @ih tt (is_false_of_cons h1).2 (by simp [h.2])
      rw [h.1]
      exact List.PrefixData.cons ht ih

def false_true_eq_unfinished_frontier_split (h1 : is_false a) (h2 : is_true b) (h3 : a.length > 0)
      (h5 : a ++ b = k ++ ([(a3, false), (b3, true)] ++ l)) : Σ a1 a2 b1 b2, PLift (a = a1 ++ a2 ∧ b = b1 ++ b2 ∧
      [(a3, false), (b3, true)] = a2 ++ b1 ∧ a1 = k ∧ b2 = l) := by
  induction k generalizing a with
  | nil =>
    use [], [(a3, false)], [(b3, true)], l
    simp only [List.cons_append, List.nil_append] at h5
    simp only [List.nil_append, List.cons_append, and_self, and_true]
    have H : a.length = 1 := by
      have : ¬ a.length > 1 := by
        intro h
        rcases List.length_geq_one_eq_cons_cons _ h5 h with ⟨f, hf⟩
        rw [hf] at h1
        specialize h1 (b3, true) (by simp)
        simp at h1
      omega
    change a.length = [(a3, false)].length at H
    exact {down := List.append_inj h5 H}
  | cons head tail ih =>
    cases a with
    | nil => simp at h3
    | cons heada taila =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h5
      cases taila with
      | nil =>
        use [], [heada]
        simp only [List.nil_append, List.cons_append, List.cons.injEq, List.nil_eq, reduceCtorEq,
          false_and, and_false]
        rw [List.nil_append] at h5
        rw [h5.2] at h2
        specialize h2 (a3, false)
        use [], []
        exact {down := (Bool.eq_not_self (a3, false).2).mp (by grind)}
      | cons headaa tailaa =>
        specialize ih (is_false_tail h1) (by simp) h5.2
        rcases ih with ⟨a1', a2', b1', b2', f1, f2, f3, f4, f5⟩
        use heada :: a1', a2', b1', b2'
        exact ⟨by rw [f1]; rfl, ⟨f2, ⟨f3, ⟨by rw [f4, h5.1], f5⟩⟩⟩⟩

def unfinished_frontier_false_suffix_split (hup2 : is_false up2)
    (h : bot3 ++ mid3 ++ (up3 ++ up2) = k ++ [(a1, false), (b1, true)] ++ l) :
    Σ l₁ l₂, PLift (l = l₁ ++ l₂ ∧ bot3 ++ mid3 ++ up3 = k ++ [(a1, false), (b1, true)] ++ l₁ ∧
    l₂ = up2) := by
  induction l using List.reverseRecOn generalizing up2 with
  | nil =>
    use [], []
    have H : up2 = [] := by
      induction up2 using List.reverseRecOn with
      | nil => rfl
      | append_singleton l e _ =>
        have h3 := congr_arg List.getLast? h
        rw [← List.append_assoc, ← List.append_assoc, List.getLast?_concat, List.append_nil,
          List.getLast?_append_cons, List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at h3
        rw [h3] at hup2
        have H := hup2 (b1, true) (List.mem_append_right l (List.mem_singleton.mpr rfl))
        simp at H
    rw [H] at h
    constructor
    constructor
    · rfl
    constructor
    · simp at h
      simp
      exact h
    exact H.symm
  | append_singleton front caboose ih =>
    induction up2 using List.reverseRecOn with
    | nil =>
      simp at h
      use front ++ [caboose], []
      constructor
      constructor
      · simp
      simp [h]
    | append_singleton up2front up2back _ =>
      specialize @ih up2front (is_false_of_append hup2).1
      rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at h
      have h1 := List.append_inj_left' h rfl
      rw [h1] at h
      simp at h1
      simp at ih
      specialize ih h1
      rcases ih with ⟨l₁, l₂, hl1, hl2⟩
      use l₁, l₂ ++ [caboose]
      constructor
      constructor
      · rw [hl1]
        exact List.append_assoc l₁ l₂ [caboose]
      constructor
      · simp [hl2]
      simp at h
      simp [h]
      exact hl2.2

def unfinished_frontier_true_prefix_split
    (hbot2 : is_true bot2) (h : bot2 ++ bot3 ++ mid3 ++ up3 = k ++ [(a1, false), (b1, true)] ++ l) :
    Σ k₁ k₂, PLift (k = k₁ ++ k₂ ∧ bot3 ++ mid3 ++ up3 = k₂ ++ [(a1, false), (b1, true)] ++ l
    ∧ k₁ = bot2)  := by
  induction k generalizing bot2 with
  | nil =>
    use [], []
    have : bot2 = [] := by
      match bot2 with
      | [] => rfl
      | head :: tail => simp_all [is_true]
    constructor
    simp_all
  | cons head tail ih =>
    cases bot2 with
    | nil =>
      use [], head:: tail
      rw [List.nil_append] at h
      exact ⟨rfl, ⟨h, rfl⟩⟩
    | cons headb tailb =>
      change is_true ([headb] ++ tailb) at hbot2
      specialize @ih tailb (is_true_of_append hbot2).2 (by simp_all)
      rcases ih with ⟨k₁, k₂, k_is, front, back⟩
      use head :: k₁, k₂
      constructor
      grind

open Braid PartialGrid

-- here we give names to the various properties of middle frontiers

def middle_spec (d : List (α × Bool)) := PLift (d = []) ⊕ Σ front mid caboose,
  PLift (d = [(front, false)] ++ mid ++ [(caboose, true)])

def middle_frontier_end_spec (d : List (α × Bool)) := PLift (d = []) ⊕
  Σ mid caboose, PLift (d = mid ++ [(caboose, true)])

def middle_frontier_start_spec (d : List (α × Bool)) := PLift (d = []) ⊕
  Σ front mid, PLift (d = [(front, false)] ++ mid)

def middle_frontier_start_spec_of_append (h : middle_frontier_start_spec (d1 ++ d2)) :
    middle_frontier_start_spec d1 := by
  cases d1 with
  | nil => left; exact {down := rfl}
  | cons head tail =>
    right
    rcases h with h1 | ⟨f, m, spec⟩
    · simp only [List.cons_append, reduceCtorEq] at h1
      apply h1.1.elim
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at spec
    use f, tail
    rw [spec.1.1]
    constructor
    simp

def middle_frontier_start_spec_from_spec (h : middle_spec d) : middle_frontier_start_spec d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use f, m ++ [(c, true)]
  exact spec

def middle_frontier_end_spec_from_spec (h : middle_spec d) : middle_frontier_end_spec d := by
  rcases h with h1 | ⟨f, m, c, spec⟩
  · left; exact h1
  right
  use [(f, false)] ++ m, c
  exact spec

--we begin our larger proof

def open_pair_in_middle_frontier_of_in_middle_right_frontier  (h : mid2 ++ bot3 = [(a1, false), (b1, true)] ++ b)
    (hm2 : middle_frontier_end_spec mid2) (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) :
    (Σ m2, PLift (mid2 = [(a1, false), (b1, true)] ++ m2)) := by
  induction bot3 using List.reverseRecOn generalizing b with
  | nil =>
    rw [List.append_nil] at h
    use b
    exact ⟨by simp [h]⟩
  | append_singleton frontb cabooseb ihb =>
    induction b using List.reverseRecOn with
    | nil =>
      rw [List.append_nil, ← List.append_assoc] at h
      change _ = [(a1, false)] ++ [(b1, true)] at h
      apply List.append_singleton_eq_append_singleton at h
      rcases hm2 with is_nil | ⟨frontm, endm, hfe⟩
      · exfalso
        rw [is_nil.1, List.nil_append] at h
        rcases hbot3 with h3 | h4
        · rw [h.1] at h3
          have h3 := is_true_of_append h3.1
          simp [is_true] at h3
        rw [h.2] at h4
        have h4 := (is_false_of_append h4.1).2 (b1, true)
        simp at h4
      rw [hfe.1] at h
      have H0 := congr_arg List.length h.1
      simp at H0
      have H1 : frontm = [] := List.length_eq_zero_iff.mp (by omega)
      have H2 : frontb = [] := List.length_eq_zero_iff.mp (by omega)
      rw [H1, H2] at h
      simp at h
    | append_singleton frontbb caboosebb _ =>
      rw [← List.append_assoc, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      rcases hbot3 with h3 | h4
      · exact @ihb frontbb h.1 (Sum.inl ⟨(is_true_of_append h3.1).1⟩)
      exact @ihb frontbb h.1 (Sum.inr ⟨(is_false_of_append h4.1).1⟩)

def open_pair_in_middle_frontier_of_in_bottom_middle_frontier
    (h : bot3 ++ mid3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) (hm3 : middle_frontier_start_spec mid3):
    Σ m3 m4, PLift (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4) := by
  induction bot3 generalizing k with
  | nil =>
    use k, l
    exact ⟨by simp_all⟩
  | cons head tail ih =>
    cases k with
    | nil =>
      rw [List.nil_append] at h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      rcases hbot3 with h3 | h4
      · rw [h.1] at h3
        simp only [is_true, List.mem_cons, forall_eq_or_imp, Bool.false_eq_true, Prod.forall,
          Bool.forall_bool, imp_false, implies_true, and_true, false_and] at h3
        exact h3.1.elim
      cases tail with
      | nil =>
        rcases hm3 with h5 | ⟨f1, m1, spec⟩
        · rw [h5.1] at h
          simp at h
        rw [spec.1] at h
        simp at h
      | cons head tail =>
        simp only [List.cons_append, List.cons.injEq] at h
        rw [h.2.1] at h4
        have := h4.1 (b1, true) (by simp)
        simp at this
    | cons headk tailk =>
      simp only [List.cons_append,List.cons.injEq] at h
      have h2 : PLift (is_true tail) ⊕ PLift (is_false tail) := by
        rcases hbot3 with h1 | h2
        · exact Sum.inl ⟨(is_true_of_cons h1.1).2⟩
        exact Sum.inr ⟨(is_false_of_cons h2.1).2⟩
      exact @ih tailk h.2 h2

theorem open_pair_neq_middle_frontier_from_appending_grids_center_length_two {b : Bool}
    (hm2 : middle_frontier_end_spec mid2) (hm3 : middle_frontier_start_spec mid3)
    (h : mid2 ++ [(a', b)] ++ mid3 = [(a1, false), (b1, true)]) : False := by
  rcases hm2 with h3 | h4
  · rcases hm3 with h5 | h6
    · rw [h3.1, h5.1] at h
      simp at h
    rcases h6 with ⟨f, m, spec2⟩
    rw [spec2.1] at h
    have := congr_arg List.length h
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.length_append,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at this
    have : m.length = 0 ∧ mid2.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp this.1, List.length_eq_zero_iff.mp this.2] at h
    simp at h
  rcases h4 with ⟨f, m, spec2⟩
  rw [spec2.1] at h
  have := congr_arg List.length h
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at this
  have : f.length = 0 ∧ mid3.length = 0 := by omega
  rw [List.length_eq_zero_iff.mp this.1, List.length_eq_zero_iff.mp this.2] at h
  simp at h

def open_pair_eq_middle_frontier_from_appending_grids
    (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)])
    (hm2 : middle_frontier_end_spec mid2)
    (hm3 : middle_frontier_start_spec mid3) (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) :
    (Σ m2, PLift (mid2 = [(a1, false), (b1, true)] ++ m2)) ⊕ Σ m3, PLift (mid3 = m3 ++ [(a1, false), (b1, true)]) := by
  have len := congr_arg List.length h
  simp only [List.append_assoc, List.length_append, List.length_cons,
    Nat.reduceAdd, List.length_nil, zero_add, Nat.reduceAdd] at len
  have : bot3.length ≠ 2 := by
    intro h1
    have H1 : mid2.length = 0 := by omega
    have H2 : mid3.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp H1, List.length_eq_zero_iff.mp H2, List.nil_append, List.append_nil] at h
    rw [h] at hbot3
    simp only [is_true, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      Bool.false_eq_true, forall_eq, and_true, is_false, Bool.true_eq_false, and_false] at hbot3
    rcases hbot3 with h1 | h2
    · exact h1.1
    exact h2.1
  have : bot3.length ≠ 1 := by
    intro h2
    have Hb : ∃ a, bot3 = [a] := List.length_eq_one_iff.mp h2
    rcases Hb with ⟨a, ha⟩
    rcases hbot3 with h_t | h_f
    · rw [ha] at h_t
      rcases is_true_singletonData h_t.1 with ⟨a', spec⟩
      rw [ha, spec.1] at h
      exact open_pair_neq_middle_frontier_from_appending_grids_center_length_two hm2 hm3 h
    rw [ha] at h_f
    rcases is_false_singletonData h_f.1 with ⟨a', spec⟩
    rw [ha, spec.1] at h
    exact open_pair_neq_middle_frontier_from_appending_grids_center_length_two hm2 hm3 h
  have H : bot3 = [] := List.length_eq_zero_iff.mp (by omega)
  rw [H, List.append_nil] at h
  have H : mid2.length ≠ 1 := by
    intro hm_length
    rcases List.length_eq_one_iff.mp hm_length with ⟨a, ha⟩
    rw [ha] at h
    simp only [List.singleton_append, List.cons.injEq] at h
    rw [h.1] at ha
    rw [ha] at hm2
    rcases hm2 with h1 | ⟨a2, a3, ha2⟩
    · simp only [List.cons_ne_self] at h1
      exact h1.1
    have h4 : a2 = [] := by
      have ha2' := ha2.1
      apply congr_arg List.length at ha2'
      simp only [List.length_singleton, List.length_append, right_eq_add,
        List.length_eq_zero_iff] at ha2'
      exact ha2'
    rw [h4, List.nil_append] at ha2
    simp only [List.cons.injEq, Prod.mk.injEq, Bool.false_eq_true, and_false, and_true] at ha2
    exact ha2.1
  match ml : mid2.length with
  | 0 =>
    rw [List.length_eq_zero_iff.mp ml, List.nil_append] at h
    right; use []; rw [h]; exact ⟨rfl⟩
  | 1 =>
    exact (H ml).elim
  | 2 =>
      have H3 : mid3.length = 0 := by omega
      rw [List.length_eq_zero_iff.mp H3, List.append_nil] at h
      left; use []; rw [h]; exact ⟨rfl⟩
  | Nat.succ (Nat.succ (Nat.succ n)) =>
    rw [ml] at len
    omega

def open_pair_eq_middle_frontier_from_appending_grids_second_middle_frontier_fully_split
    (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)])
    (hm2 : middle_frontier_end_spec mid2)
    (hm3 : middle_frontier_start_spec mid3) (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) :
    (Σ m2, PLift (mid2 = [(a1, false), (b1, true)] ++ m2)) ⊕
    Σ m3 m4, PLift (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ [] = m4) := by
  rcases open_pair_eq_middle_frontier_from_appending_grids h hm2 hm3 hbot3 with h1 | ⟨m3, hm3⟩
  · left; exact h1
  right; use m3, []; simp; exact hm3

def open_pair_prefix_middle_frontier_from_appending_grids
    (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)] ++ l)
    (hm2 : middle_frontier_end_spec mid2)
    (hm3 : middle_frontier_start_spec mid3) (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) :
    (Σ m2, PLift (mid2 = [(a1, false), (b1, true)] ++ m2)) ⊕
    Σ m3 m4,PLift (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4) := by
  induction l using List.reverseRecOn generalizing mid3 with
  | nil =>
    exact open_pair_eq_middle_frontier_from_appending_grids_second_middle_frontier_fully_split
      h hm2 hm3 hbot3
  | append_singleton head tail ih =>
    induction mid3 using List.reverseRecOn with
    | nil =>
      rw [List.append_nil] at h
      left
      exact open_pair_in_middle_frontier_of_in_middle_right_frontier h hm2 hbot3
    | append_singleton headm tailm _ =>
      rw [← List.append_assoc, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      specialize @ih headm h.1 (middle_frontier_start_spec_of_append hm3)
      rcases ih with ha | ⟨m3, m4, hm34⟩
      · left; exact ha
      right
      rw [hm34.1.1, hm34.1.2, ← h.2]
      use m3, m4 ++ [tailm]
      exact ⟨by simp⟩

def open_pair_prefix_middle_frontier_from_appending_grids_first_middle_frontier_fully_split
    (h : mid2 ++ bot3 ++ mid3 = [(a1, false), (b1, true)] ++ l)
    (hm2 : middle_frontier_end_spec mid2)
    (hm3 : middle_frontier_start_spec mid3) (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) :
    (Σ m1 m2, PLift (mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ [] = m1)) ⊕
    Σ m3 m4, PLift (mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4) := by
  rcases open_pair_prefix_middle_frontier_from_appending_grids h hm2 hm3 hbot3 with ⟨m2, hm2⟩ | h2
  · left; use [], m2
    rw [hm2.1]
    exact ⟨by simp⟩
  right; exact h2

def open_pair_lies_in_one_middle_frontier_empty_bottom_and_right_frontier {mid2 bot3 mid3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
    (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3))
    (hm2 : middle_frontier_end_spec mid2)
    (hm3 : middle_frontier_start_spec mid3)
    (h : mid2 ++ bot3 ++ mid3 = k ++ [(a1, false), (b1, true)] ++ l) :
    (Σ m1 m2, PLift ((mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = m1))) ⊕
    (Σ m3 m4, PLift ((mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4))) := by
  induction k generalizing mid2 with
  | nil =>
    exact open_pair_prefix_middle_frontier_from_appending_grids_first_middle_frontier_fully_split
      h hm2 hm3 hbot3
  | cons head tail ih =>
    cases mid2 with
    | nil =>
      right
      exact open_pair_in_middle_frontier_of_in_bottom_middle_frontier h hbot3 hm3
    | cons head tail =>
      simp at h
      have Ht : PLift (tail = []) ⊕ Σ front a, PLift (tail = front ++ [(a, true)]) := by
        rcases hm2 with h1 | h2
        · simp only [reduceCtorEq] at h1
          exact h1.1.elim
        rcases h2 with ⟨f1, a1, spec⟩
        cases f1 with
        | nil => left; simp only [List.nil_append, List.cons.injEq] at spec; exact ⟨spec.1.2⟩
        | cons head tail =>
            right
            simp only [List.cons_append, List.cons.injEq] at spec
            use tail, a1
            exact ⟨spec.1.2⟩
      specialize @ih tail Ht
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ih
      specialize ih h.2
      rcases ih with ⟨m1, m2, hm12⟩ | ⟨m3, m4, hm34⟩
      · left
        use head :: m1, m2
        rw [hm12.1.1, hm12.1.2, h.1]
        exact ⟨by simp⟩
      right
      use m3, m4
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact hm34

def open_pair_lies_in_one_middle_frontier_empty_bottom_frontier {mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
     (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) (hup3 : is_false up3)
    (h : (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
        (hm2 : middle_spec mid2)
    (hm3 : middle_spec mid3) :
    (Σ m1 m2, PLift ((mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = m1))) ⊕
    (Σ m3 m4, PLift ((mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3))) := by
  induction up3 using List.reverseRecOn generalizing l with
  | nil =>
    rw [List.append_nil] at h
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
    have H2 := open_pair_lies_in_one_middle_frontier_empty_bottom_and_right_frontier hbot3 (middle_frontier_end_spec_from_spec hm2) (middle_frontier_start_spec_from_spec hm3) h
    simp only [List.append_assoc, List.cons_append, List.nil_append] at H2
    exact H2
  | append_singleton front caboose ih =>
    induction l using List.reverseRecOn with
    | nil =>
      have H3 : [(a1, false), (b1, true)] = [(a1, false)] ++ [(b1, true)] := rfl
      rw [List.append_nil, ← List.append_assoc, H3, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      rw [h.2] at hup3
      specialize hup3 (b1, true) (by simp)
      simp at hup3
    | append_singleton headl taill =>
      have H : is_false front := (is_false_of_append hup3).1
      rw [← List.append_assoc, ← List.append_assoc] at h
      apply List.append_singleton_eq_append_singleton at h
      specialize @ih headl H h.1
      rcases ih with ⟨m1, m2, hm12, k_is⟩ | ⟨m3, m4, hm34, l_is⟩
      · left
        use m1, m2
        exact {down := ⟨hm12, k_is⟩}
      right
      use m3, m4
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hm34
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact ⟨hm34, by simp [l_is, h.2]⟩

def open_pair_lies_in_one_middle_frontier {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
    (hbot2 : is_true bot2) (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) (hup3 : is_false up3)
    (hm2 : middle_spec mid2) (hm3 : middle_spec mid3)
    (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l) :
    (Σ m1 m2, PLift ((mid2 = m1 ++ [(a1, false), (b1, true)] ++ m2 ∧ k = bot2 ++ m1))) ⊕
    (Σ m3 m4, PLift ((mid3 = m3 ++ [(a1, false), (b1, true)] ++ m4 ∧ l = m4 ++ up3))) := by
  induction bot2 generalizing k with
  | nil =>
    rw [List.nil_append] at h
    exact open_pair_lies_in_one_middle_frontier_empty_bottom_frontier hbot3 hup3 h hm2 hm3
  | cons head tail ih =>
    cases k with
    | nil =>
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq] at h
      rw [h.1] at hbot2
      simp [is_true] at hbot2
    | cons headl taill =>
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq] at h
      specialize @ih taill (is_true_of_cons hbot2).2 (by simp [h.2])
      rcases ih with ⟨m1, m2, hm12, k_is⟩ | ⟨m3, m4, hm34, l_is⟩
      · left
        use m1, m2
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hm12
        simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq]
        exact ⟨hm12, ⟨h.1.symm, k_is⟩⟩
      right
      use m3, m4
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hm34
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact ⟨hm34, l_is⟩

def open_pair_lies_in_one_middle_frontier_for_horizontal_case {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
    (hbot2 : is_true bot2) (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) (hup3 : is_false up3)
    (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hm : middle_spec mid2) (hm3 : middle_spec mid3) :
    (Σ k₁ k₂, PLift (k = k₁ ++ k₂ ∧ k₁ = bot2 ++ mid2 ∧ k₂ ++ [(a1, false), (b1, true)] ++ l = bot3 ++ mid3 ++ up3)) ⊕
    (Σ l₁ l₂, PLift (l = l₁ ++ l₂ ∧ l₂ = bot3 ++ mid3 ++ up3 ∧ k ++ [(a1, false), (b1, true)] ++ l₁ = bot2 ++ mid2)) := by
  rcases @open_pair_lies_in_one_middle_frontier bot2 mid2 bot3 mid3 up3 k l a1 b1 hbot2 hbot3 hup3 hm hm3 h with ⟨m1, m2, hm12, k_is⟩ | ⟨m3, m4, hm34, l_is⟩
  · right
    rw [hm12] at h
    rw [hm12]
    use m2, bot3 ++ mid3 ++ up3
    rw [k_is] at h
    simp at h
    simp
    exact ⟨h.symm, by simp [k_is]⟩
  left
  rw [hm34] at h
  rw [hm34]
  rw [l_is, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at h
  repeat apply List.append_cancel_right at h
  use bot2 ++ mid2, bot3 ++ m3
  rw [← List.append_assoc]
  exact ⟨h.symm, by simp [l_is]⟩


def open_pair_lies_in_one_middle_frontier_for_vertical_case {bot2 mid2 bot3 mid3 up3 k l : List (Option ℕ × Bool)} {a1 b1 : Option ℕ}
    (hbot2 : is_true bot2) (hbot3 : PLift (is_true bot3) ⊕ PLift (is_false bot3)) (hup3 : is_false up3)
    (h : bot2 ++ (mid2 ++ bot3 ++ mid3) ++ up3 = k ++ [(a1, false), (b1, true)] ++ l)
    (hm : middle_spec mid2)
    (hm3 : middle_spec mid3) :
    (Σ k₁ k₂, PLift (k = k₁ ++ k₂ ∧ k₁ = bot2 ++ mid2 ++ bot3 ∧ k₂ ++ [(a1, false), (b1, true)] ++ l =  mid3 ++ up3)) ⊕
    (Σ l₁ l₂, PLift (l = l₁ ++ l₂ ∧ l₂ = mid3 ++ up3 ∧ k ++ [(a1, false), (b1, true)] ++ l₁ = bot2 ++ mid2 ++ bot3)) := by
  have H := open_pair_lies_in_one_middle_frontier_for_horizontal_case hbot2 hbot3 hup3 h hm hm3
  rcases H with ⟨k₁, k₂, k_is, k12_is⟩ | ⟨l₁, l₂, l_is, l12_is⟩
  · left
    cases k₂
    · rw [k12_is.1, List.append_nil] at k_is
      rw [k_is]
      rcases hm3 with h1 | ⟨f, m, c, spec⟩
      · rw [h1.1, List.nil_append, List.append_nil] at k12_is
        rw [h1.1, List.nil_append]
        use k₁, []
        constructor
        constructor
        · rw [List.append_nil]
          exact k12_is.1.symm
        rcases hbot3 with h3 | h4
        · cases bot3 with
          | nil =>
            rw [List.nil_append] at k12_is
            rw [← k12_is.2] at hup3
            specialize hup3 (b1, true) (by simp)
            simp at hup3
          | cons head tail =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at k12_is
            rw [← k12_is.2.1] at h3
            simp only [is_true, List.mem_cons, forall_eq_or_imp, Bool.false_eq_true, Prod.forall,
              Bool.forall_bool, imp_false, implies_true, and_true, false_and] at h3
            exact h3.1.elim
        have H : is_false (bot3 ++ up3) := is_false_append h4.1 hup3
        rw [← k12_is.2] at H
        specialize H (b1, true) (by simp)
        simp at H
      have H : bot3 = [] := by
        cases bot3 with
        | nil => rfl
        | cons head tail =>
          cases tail with
          | nil =>
            simp [spec.1] at k12_is
          | cons head2 tail2 =>
            simp only [List.nil_append, List.cons_append, spec.1, List.append_assoc,
              List.cons.injEq] at k12_is
            rcases hbot3 with h3 | h4
            · rw [← k12_is.2.1] at h3
              simp only [is_true, List.mem_cons, forall_eq_or_imp, Bool.false_eq_true, Prod.forall,
                Bool.forall_bool, imp_false, implies_true, and_true, false_and] at h3
              apply h3.1.elim
            rw [← k12_is.2.2.1] at h4
            have := h4.1 (b1, true) (by simp)
            simp at this
      use k₁, bot3
      constructor
      grind
    rename_i hk tk
    cases bot3
    · use k₁, hk :: tk
      constructor
      grind
    rename_i h3 t3
    have : Σ ender, PLift (hk::tk = h3 :: t3 ++ ender) := by
      rcases hbot3 with h5 | h6
      · have H := PrefixData.of_is_true_prefix_unfinished_frontier h5.1 k12_is.2.symm
        rcases H with ⟨w, hw⟩
        use w; exact ⟨hw.1.symm⟩
      rcases hm3 with h5 | ⟨f, m ,c, spec⟩
      · have H := is_false_append h6.1 hup3
        rw [h5.1, List.append_nil] at k12_is
        rw [← k12_is.2] at H
        have H2 := is_false_of_append (is_false_of_append H).1
        have nonsense := H2.2 (b1, true) (by simp)
        simp at nonsense
      rw [spec.1] at k12_is
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at k12_is
      rw [k12_is.2.1]
      simp only [List.cons_append, List.cons.injEq, true_and]
      rcases PrefixData.false_prefix_of_unfinished_frontiers_eq (is_false_of_cons h6.1).2 k12_is.2.2 with ⟨f, spec⟩
      rw [← spec.1]
      use f
      exact ⟨rfl⟩
    rcases this with ⟨e, he⟩
    use k₁ ++ h3::t3, e
    constructor
    constructor
    · rw [List.append_assoc, ← he.1]
      exact k_is
    constructor
    · rw [k12_is.1]
    rw [he.1] at k12_is
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.cons.injEq,
      List.append_cancel_left_eq, true_and] at k12_is
    simp [k12_is.2]
  right
  use l₁ ++ bot3
  have : List.PrefixData bot3 l₂ := by
    use mid3 ++ up3
    rw [← List.append_assoc]
    constructor
    exact l12_is.1.symm
  rcases this with ⟨f, spec⟩
  use f
  constructor
  rw [← spec.1] at l12_is
  simp only [List.append_assoc, List.append_cancel_left_eq, List.cons_append,
    List.nil_append] at l12_is
  constructor
  · rw [List.append_assoc, spec.1]
    exact l_is
  grind
