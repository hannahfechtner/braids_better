import BraidProject.PartialGrid.FrontierPossibilities
import BraidProject.PartialGrid.ToGrid
import BraidProject.GridData_length
import BraidProject.NewListFacts

namespace Braid

namespace PartialGrid

open SignedOptionList FrontierPossibilitiesEpsilonRemovedBoolRemoved

theorem frontier_prefix_w_length (h : GridData i j k l) (h1 : PartialGrid a b c mid d) :
    (SignedOptionList.toList (FreeGroup.invRev a) = i → SignedOptionList.toList b <+: j →
      (SignedOptionList.toList c <+: k ∧ h1.length ≤ h.length)) ∧
    (SignedOptionList.toList b = j → SignedOptionList.toList (FreeGroup.invRev a) <+: i →
      (SignedOptionList.toList (FreeGroup.invRev d) <+: l) ∧ h1.length ≤ h.length) := by
  induction h generalizing a b c mid d with
  | empty =>
    constructor
    · intro a_is b_is
      change _ <+: [] at b_is
      rw [List.prefix_nil] at b_is
      have := empty_empty h1 a_is b_is
      constructor
      · change _ <+: []
        simp only [List.prefix_nil]
        aesop
      simp [this]
    intro b_is a_is
    change _ <+: [] at a_is
    simp only [toList_invRev, List.prefix_nil, List.reverse_eq_nil_iff] at a_is
    have := empty_empty h1 (toList_invRev_eq_nil_iff.mpr a_is) b_is
    aesop
  | top_bottom i =>
    constructor
    · intro a_is b_is
      rcases List.IsPrefix.of_singleton b_is with h3 | h4
      · have := empty_empty h1 a_is h3
        aesop
      have := empty_generator h1 a_is h4
      aesop
    intro b_is a_is
    change _ <+: [] at a_is
    simp only [toList_invRev, List.prefix_nil, List.reverse_eq_nil_iff] at a_is
    have := empty_generator h1 (toList_invRev_eq_nil_iff.mpr a_is) b_is
    aesop
  | sides i =>
    constructor
    · intro a_is b_is
      change _ <+: [] at b_is
      rw [List.prefix_nil] at b_is
      have := generator_empty h1 a_is (toList_invRev_eq_nil_iff.mpr b_is)
      aesop
    intro b_is a_is
    rcases List.IsPrefix.of_singleton a_is with h3 | h4
    · have := empty_empty h1 h3 b_is
      aesop
    have := generator_empty h1 h4 (toList_invRev_eq_nil_iff.mpr b_is)
    aesop
  | top_left i =>
    constructor
    · intro a_is b_is
      rcases List.IsPrefix.of_singleton b_is with h3 | h4
      · have := generator_empty h1 a_is
        aesop
      have := generator_generator_same h1 a_is h4
      aesop
    intro b_is a_is
    rcases List.IsPrefix.of_singleton a_is with h3 | h4
    · have := empty_generator h1 h3 b_is
      aesop
    have := generator_generator_same h1 h4 b_is
    aesop
  | adjacent i k h =>
    constructor
    · intro a_is b_is
      rcases List.IsPrefix.of_singleton b_is with h3 | h4
      · have := generator_empty h1 a_is
        aesop
      have H := generator_generator_close h1 (toList_invRev_eq_singleton_iff.mp a_is) h4 h
      constructor
      · change _ <+: [k, i]
        aesop
      aesop
    intro b_is a_is
    rcases List.IsPrefix.of_singleton a_is with h3 | h4
    · have := empty_generator h1 h3 b_is
      aesop
    have := generator_generator_close h1 (toList_invRev_eq_singleton_iff.mp h4) b_is h
    have : toList d = [] ∨ toList d = [i] ∨ toList d = [k, i] := by aesop
    constructor
    · change _ <+: [i, k]
      aesop
    aesop
  | separated i j h =>
    constructor
    · intro a_is b_is
      rcases List.IsPrefix.of_singleton b_is with h3 | h4
      · have := generator_empty h1 a_is (toList_invRev_eq_nil_iff.mpr h3)
        aesop
      have := generator_generator_apart h1 (toList_invRev_eq_singleton_iff.mp a_is) h4 h
      aesop
    intro b_is a_is
    rcases List.IsPrefix.of_singleton a_is with h3 | h4
    · have := empty_generator h1 h3 b_is
      aesop
    have := generator_generator_apart h1 (toList_invRev_eq_singleton_iff.mp h4) b_is h
    aesop
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    rw [GridData.length]
    constructor
    · intro ha hb
      rcases SignedOptionList.toList_invRev_eq_append_cases ha with m_nil | q_nil | ⟨a1, a2, a1_len, a2_len, ha1, a1q, a2m⟩
      · have H : toList (FreeGroup.invRev a) = q := by
          have : m = 1 :=
            BraidMonoidInf.one_of_eq_mk_one (congrArg (⇑BraidMonoidInf.mk) m_nil)
          rw [this, one_mul] at ha
          exact ha
        have on := GridData.DeterminativeSpine.one_word t m_nil
        specialize h2_ih h1
        have new_h2_ih := h2_ih.1 H
        rw [← on.1] at hb
        specialize new_h2_ih hb
        constructor
        · exact new_h2_ih.1
        linarith
      · have H : toList (FreeGroup.invRev a) = m := by
          have : q = 1 := by exact
            BraidMonoidInf.one_of_eq_mk_one (congrArg (⇑BraidMonoidInf.mk) q_nil)
          rw [this] at ha
          rw [ha]
          exact mul_one m
        have rs := GridData.DeterminativeSpine.one_word h2 q_nil
        specialize h1_ih h1
        have new_h2_ih := h1_ih.1 H hb
        have hr := rs.1
        subst hr
        constructor
        · exact new_h2_ih.1
        linarith
      apply congr_arg FreeGroup.invRev at ha1
      simp only [FreeGroup.invRev_invRev, FreeGroup.invRev_append] at ha1
      rcases PartialGrid.splittable_horizontally h1 _ _ ha1 a1_len a2_len
        with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
      · specialize h1_ih i1
        have new_h1_ih := h1_ih.1 a1q hb
        have := (h2_ih i2).1 a2m new_h1_ih.1
        constructor
        · exact this.1
        linarith
      rcases baaad with ⟨_, _, _, _, ⟨mid_nil⟩, _⟩
      constructor
      · aesop
      rename_i g1 g2 g3
      have := (h1_ih g1).1 a1q hb
      rw [g3.1]
      linarith
    intro hb ha
    have ha1 : toList (FreeGroup.invRev a) <+: m.toList ++ q.toList := by
      convert ha
    match m with
    | [] =>
      have on := GridData.DeterminativeSpine.one_word t rfl
      rw [← on.1] at hb
      have hn := on.2
      subst hn
      rw [one_mul]
      have := (h2_ih h1).2 hb ha1
      constructor
      · exact this.1
      linarith
    | m1 :: m2 =>
      have H : toList (FreeGroup.invRev a) <+: (m1 :: m2) ∨
          ∃ a1 a2, a1.length > 0 ∧ a = a1 ++ a2 ∧
          toList (FreeGroup.invRev a2) =  (m1 :: m2) ∧ toList (FreeGroup.invRev a1) <+: q :=
        toList_invRev_prefix_append_cases ha1
      rcases H with ha1 | ⟨a1, a2, a1_len, a1_is, ha11⟩
      · have H2 := (h1_ih h1).2 hb ha1
        constructor
        · exact List.prefix_of_append H2.1
        linarith
      have a2_len : a2.length > 0 := by
        have H := SignedOptionList.toList_len a2
        rw [← toList_invRev_length, ha11.1, List.length_cons] at H
        omega
      rcases PartialGrid.splittable_horizontally h1 _ _ a1_is a2_len a1_len
          with ⟨mid4, d4, e4, e5, d5, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
      · have H := frontier_options_from_vertical h1 i1 i2 hf
        rcases H with bb | fb
        · have one := (h1_ih i1).1 ha11.1 (by rw [hb])
          have two := (h1_ih i1).2 hb (by rw [ha11.1])
          have := bb.2.symm
          subst this
          refine ⟨List.prefix_of_append two.1, ?_⟩
          rw [hl]
          have i2_bound : i2.length ≤ h2.length := by
            rcases one.1 with ⟨r, hr⟩
            cases r with
            | nil =>
              rw [List.append_nil] at hr
              exact ((h2_ih i2).2 hr ha11.2).2
            | cons r1 r2 =>
              have i3 := PartialGrid.extend_top_side_w_length i2
                (to_horizontal_edge (r1 :: r2))
                is_true_to_horizontal_edge (by simp [to_horizontal_edge])
              rw [i3.2.1]
              have htop : toList (mid4 ++ to_horizontal_edge (r1 :: r2)) = o := by
                rw [toList_append, toList_to_horizontal_edge]
                exact hr
              exact ((h2_ih i3.1).2 htop ha11.2).2
          linarith [two.2]
        have H1 := (h1_ih i1).1 ha11.1 (by rw [hb])
        rw [fb.2.1] at i1
        have H := empty_middle_frontier_matches_grid i1 ha11.1.symm hb.symm t
        have H2 := (h2_ih i2).2 H.2.symm ha11.2
        constructor
        · rw [fb.2.2, FreeGroup.invRev_append, SignedOptionList.toList_append, H.1]
          apply (List.prefix_append_right_inj _).mpr
          exact H2.1
        rw [hl]
        linarith [H1.2, H2.2]
      rcases baaad with ⟨c11, drest, h3, ⟨d2_is⟩, ⟨mid_nil⟩, len3⟩
      specialize h1_ih h3
      have H2 := h1_ih.2 hb (by rw [ha11.1])
      constructor
      · exact List.prefix_of_append H2.1
      rw [len3.1]
      linarith
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    rw [GridData.length]
    constructor
    · intro a_is b_is
      match n with
      | [] =>
        have H := GridData.DeterminativeSpine.word_one t rfl
        specialize h2_ih h1
        change _ <+: q at b_is
        constructor
        · simp_all
        have ht : t.length = 0 := GridData.DeterminativeSpineLength.word_one t rfl
        rw [← H.2] at a_is
        have := h2_ih.1 a_is b_is
        omega
      | n1 :: n2 =>
        rcases toList_prefix_append_cases b_is (by simp) with one | two
        · specialize h1_ih h1
          have new_ih := h1_ih.1 a_is one
          constructor
          · exact List.prefix_of_append new_ih.1
          linarith
        rcases two with ⟨b1, b2, b1_len, b2_len, b_is, b1_n, b2_q⟩
        rcases PartialGrid.splittable_vertically h1 _ _ b_is b1_len b2_len
          with ⟨mid1, d3, e3, d4, e4, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
        · specialize h1_ih i1
          rw [List.append_assoc, List.append_assoc] at hf
          have nonsense :=
            frontier_options_from_horizontal h1 i1 i2 hf
          rcases nonsense with h_one | h_two
          · rw [h_one.2] at i1
            have H := empty_middle_frontier_matches_grid i1 a_is.symm b1_n.symm t
            have h1_res := h1_ih.1 a_is (by rw [b1_n]; rfl)
            constructor
            · rw [h_one.1, h_one.2, List.append_nil, SignedOptionList.toList_append, H.2]
              exact (List.prefix_append_right_inj (SignedOptionList.toList d3)).mpr
                ((h2_ih i2).1 H.1.symm b2_q).1
            have := ((h2_ih i2).1 H.1.symm b2_q).2
            linarith [h1_res.2]
          have h1_res := h1_ih.1 a_is (by rw [b1_n]; rfl)
          have h1_right := (h1_ih.2 b1_n (by rw [a_is])).1
          have i2_bound : i2.length ≤ h2.length := by
            rcases b2_q with ⟨r, hr⟩
            cases r with
            | nil =>
              rw [List.append_nil] at hr
              exact ((h2_ih i2).2 hr h1_right).2
            | cons r1 r2 =>
              have i3 := PartialGrid.extend_top_side_w_length i2
                (to_horizontal_edge (r1 :: r2))
                is_true_to_horizontal_edge (by simp [to_horizontal_edge])
              rw [i3.2.1]
              have htop : toList (b2 ++ to_horizontal_edge (r1 :: r2)) = q := by
                rw [toList_append, toList_to_horizontal_edge]
                exact hr
              exact ((h2_ih i3.1).2 htop h1_right).2
          constructor
          · rw [h_two.1]
            exact List.prefix_of_append h1_res.1
          linarith [h1_res.2]
        rcases baaad with ⟨drest, h3, ⟨d2_is⟩, ⟨mid_nil⟩, len3⟩
        specialize h1_ih h3
        have H2 := h1_ih.1 a_is (by rw [b1_n]; rfl)
        constructor
        · exact List.prefix_of_append H2.1
        rw [d2_is]
        linarith [H2.2]
    intro b_is a_is
    have hb1 : n = [] ∨ q = [] ∨ ∃ b1 b2, b1.length > 0 ∧ b2.length > 0 ∧
        b = b1 ++ b2 ∧ toList b1 = n ∧ toList b2 = q :=
      SignedOptionList.toList_eq_append_cases b_is
    rcases hb1 with n_nil | q_nil | ⟨b1, b2, b1_len, b2_len, b1_is, b1n, b2q⟩
    · have H : toList b = q := by
        rw [n_nil] at b_is
        convert b_is
      have op := GridData.DeterminativeSpine.word_one t n_nil
      specialize h2_ih h1
      have new_h2_ih := h2_ih.2 H
      have hp := op.2
      subst hp
      have := (new_h2_ih a_is)
      constructor
      · exact this.1
      linarith
    · have H : toList b = n := by
        rw [q_nil] at b_is
        convert b_is
        change n = n.toList ++ []
        erw [List.append_nil]; rfl
      have rs := GridData.DeterminativeSpine.word_one h2 q_nil
      specialize h1_ih h1
      have new_h2_ih := h1_ih.2 H a_is
      have := rs.2
      subst this
      constructor
      · exact new_h2_ih.1
      linarith
    rcases PartialGrid.splittable_vertically h1 _ _ b1_is b1_len b2_len
        with ⟨mid4, d4, e4, e5, d5, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · specialize h1_ih i1
      specialize h2_ih i2
      have h1 := h2_ih.2 (by simp_all) (by simp_all)
      have := h1_ih.2 b1n a_is
      constructor
      · exact h1.1
      linarith
    rcases baaad with ⟨d6, i3, hlen , ⟨e2_nil⟩, ⟨d2_is⟩, ⟨b2_is⟩⟩
    constructor
    · aesop
    rw [hlen.1]
    have := (h1_ih i3).2 b1n a_is
    linarith

theorem frontier_prefix (h : GridData i j k l) (h1 : PartialGrid a b c mid d) :
    (SignedOptionList.toList (FreeGroup.invRev a) = i → SignedOptionList.toList b <+: j →
      SignedOptionList.toList c <+: k) ∧
    (SignedOptionList.toList b = j → SignedOptionList.toList (FreeGroup.invRev a) <+: i →
      SignedOptionList.toList (FreeGroup.invRev d) <+: l) := by
  have := frontier_prefix_w_length h h1
  aesop

noncomputable def FrontierPrefixData (h : GridData i j l k) (h1 : PartialGrid a b mid d2 e2)
  : (toList (FreeGroup.invRev a) = i → List.PrefixData (toList b) j → List.PrefixData (toList mid) l)
  × (toList b = j → List.PrefixData (toList (FreeGroup.invRev a)) i → List.PrefixData (toList (FreeGroup.invRev e2)) k) := by
  constructor
  · intro ha hb
    have H := (frontier_prefix h h1).1 ha (List.PrefixData.to_IsPrefix hb)
    exact List.PrefixData.from_IsPrefix H
  intro hb ha
  have H := (frontier_prefix h h1).2 hb (List.PrefixData.to_IsPrefix ha)
  exact List.PrefixData.from_IsPrefix ((frontier_prefix h h1).2 hb (List.PrefixData.to_IsPrefix ha))
