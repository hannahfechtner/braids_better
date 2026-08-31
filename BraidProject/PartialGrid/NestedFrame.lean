import BraidProject.PartialGrid.FrontierPossibilities
import BraidProject.PartialGrid.ToGrid
import BraidProject.GridData_length
import BraidProject.NewListFacts

namespace Braid

namespace PartialGrid

open SignedOptionList FrontierPossibilitiesEpsilonRemovedLength

theorem frontier_prefix (h : GridData i j k l)
    (h1 : PartialGrid a b c mid d)
    (ha : SignedOptionList.toSignedList a = to_vertical_edge_no_epsilon i)
    (hb : SignedOptionList.toSignedList b = to_horizontal_edge_no_epsilon j) :
    SignedOptionList.toSignedList c <+: to_horizontal_edge_no_epsilon k ∧
    SignedOptionList.toSignedList d <:+ to_vertical_edge_no_epsilon l ∧
    h1.length ≤ h.length := by
  induction h generalizing a b c mid d with
  | empty =>
    have := empty_empty h1 ha hb
    aesop
  | top_bottom i =>
    have := empty_generator h1 ha hb
    aesop
  | sides i =>
    have := generator_empty h1 hb ha
    aesop
  | top_left i =>
    have := generator_generator_same h1 ha hb
    aesop
  | adjacent i k h =>
    have := generator_generator_close h1 ha hb h
    change ( _ <+: [(k, true), (i, true)]) ∧ (_ <:+ [(k, false), (i, false)]) ∧ _
    aesop
  | separated i j h =>
    have := generator_generator_apart h1 ha hb h
    aesop
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    rw [GridData.length]
    rw [to_vertical_edge_no_epsilon_mul] at ha
    rcases toSignedList_eq_append ha with ⟨a₁, a₂, ha, ha₁, ha₂⟩
    subst ha
    match hla₁ : a₁.length with
    | 0 =>
      specialize h1_ih h1
      rw [List.length_eq_zero_iff] at hla₁
      subst hla₁
      simp only [toSignedList_nil, List.nil_eq] at ha₁
      rw [GridData.DeterminativeSpineLength.one_word h2 (to_vertical_edge_no_epsilon_eq_nil ha₁)]
      apply GridData.to_grid at h2
      rw [to_vertical_edge_no_epsilon_eq_nil ha₁] at h2
      have := Grid.DeterminativeSpine.one_word h2
      aesop
    | n + 1 =>
      match hla₂ : a₂.length with
      | 0 =>
        rw [List.length_eq_zero_iff] at hla₂
        subst hla₂
        simp only [toSignedList_nil, List.nil_eq] at ha₂
        rw [GridData.DeterminativeSpineLength.one_word t (to_vertical_edge_no_epsilon_eq_nil ha₂)]
        apply GridData.to_grid at t
        rw [to_vertical_edge_no_epsilon_eq_nil ha₂] at t
        have := Grid.DeterminativeSpine.one_word t
        specialize h2_ih h1
        aesop
      | n + 1 =>
        rcases PartialGrid.splittable_horizontally h1 a₂ a₁ rfl (by aesop) (by aesop) with
          ⟨center, m₁, d₁, m₂, d₂, p1, p2, ⟨hf⟩, ⟨hl⟩⟩ | ⟨drest, _, h3, ⟨d2_is⟩, ⟨mid_nil⟩, ⟨len3⟩⟩
        · rw [hl]
          specialize h1_ih p1 ha₂ hb
          rcases h1_ih.1 with ⟨rest, hr⟩
          have rest_true : SignedList.is_true rest := by
            have : SignedList.is_true (toSignedList center ++ rest) := by
              rw [hr]
              exact is_true_to_horizontal_edge_no_epsilon
            apply (SignedList.is_true_of_append this).2
          match hlr : rest with
          | [] =>
            specialize h2_ih p2 ha₁ (by simp [← hr])
            constructor
            · exact h2_ih.1
            constructor
            · rcases middle_frontier_spec p1 with ⟨⟨rfl⟩⟩ | ⟨d_head, d_body, d_tail, ⟨d_spec⟩⟩
              · have ⟨hh, ho, hl⟩ := PartialGrid.empty_middle_frontier_matches_grid_with_length p1
                  ((toSignedList_eq_to_vertical_edge_no_epsilon_iff (left_side_is_false p1)).mp ha₂)
                  ((toSignedList_eq_to_horizontal_edge_no_epsilon_iff (top_side_is_true h1)).mp hb) t
                have : d = d₁ ++ d₂ := by
                  have := right_frontier_spec_from_split_horizontally h1 p1 p2 rfl hf
                  aesop
                subst ho
                rw [this, to_vertical_edge_no_epsilon_mul, toSignedList_append, hh,
                  to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList (right_frontier_is_false p1)]
                exact List.suffix_append_right h2_ih.2.1
              have : d = d₂ := by
                have := right_frontier_spec_from_split_horizontally h1 p1 p2 rfl hf
                aesop
              rw [to_vertical_edge_no_epsilon_mul, this]
              exact List.suffix_of_append h1_ih.2.1
            linarith
          | rfirst :: rrest =>
            rcases middle_frontier_spec p1 with ⟨⟨rfl⟩⟩ | ⟨d_head, d_body, d_tail, ⟨d_spec⟩⟩
            · have ⟨hh, ho, hl⟩ := PartialGrid.empty_middle_frontier_matches_grid_with_length p1
                  ((toSignedList_eq_to_vertical_edge_no_epsilon_iff (left_side_is_false p1)).mp ha₂)
                  ((toSignedList_eq_to_horizontal_edge_no_epsilon_iff (top_side_is_true h1)).mp hb) t
              have : d = d₁ ++ d₂ := by
                  have := right_frontier_spec_from_split_horizontally h1 p1 p2 rfl hf
                  aesop
              subst this ho hh
              rw [to_vertical_edge_no_epsilon_mul, toSignedList_append,
                  to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList (right_frontier_is_false p1)]
              specialize h2_ih p2 ha₁ (by rw [to_horizontal_edge_no_epsilon_toList_eq_toSignedList
                (bottom_frontier_is_true p1)])
              constructor
              · exact h2_ih.1
              constructor
              · exact List.suffix_append_right h2_ih.2.1
              linarith
            have : d = d₂ := by
                have := right_frontier_spec_from_split_horizontally h1 p1 p2 rfl hf
                aesop
            rw [to_vertical_edge_no_epsilon_mul, this]
            have p3 := PartialGrid.extend_top_side_w_length p2 (SignedList.to_SignedOptionList (rfirst::rrest)) (
              SignedList.is_true_to_SignedOptionList rest_true) (by simp [SignedList.to_SignedOptionList])
            rw [p3.2.1]
            specialize h2_ih p3.1 ha₁
            simp only [toSignedList_append, toSignedList_toSignedOptionList, ← hr, toSignedList_nil,
              List.nil_suffix, true_and, forall_const] at h2_ih
            exact ⟨h2_ih.1, List.suffix_of_append h1_ih.2.1,by linarith⟩
        specialize h1_ih h3 ha₂ hb
        constructor
        · aesop
        rw [to_vertical_edge_no_epsilon_mul]
        constructor
        · exact List.suffix_of_append h1_ih.2.1
        linarith
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    rw [GridData.length]
    rw [to_horizontal_edge_no_epsilon_mul] at hb
    rcases toSignedList_eq_append hb with ⟨b₁, b₂, hb, hb₁, hb₂⟩
    subst hb
    match hlb₁ : b₁.length with
    | 0 =>
      rw [List.length_eq_zero_iff] at hlb₁
      subst hlb₁
      simp only [toSignedList_nil, List.nil_eq] at hb₁
      rw [GridData.DeterminativeSpineLength.word_one t (to_horizontal_edge_no_epsilon_eq_nil hb₁)]
      apply GridData.to_grid at t
      rw [to_horizontal_edge_no_epsilon_eq_nil hb₁] at t
      have : o = [] ∧ p = m := Grid.DeterminativeSpine.word_one t
      specialize h2_ih h1
      aesop
    | n + 1 =>
      match hlb₂ : b₂.length with
      | 0 =>
        specialize h1_ih h1
        rw [List.length_eq_zero_iff] at hlb₂
        subst hlb₂
        simp only [toSignedList_nil, List.nil_eq] at hb₂
        rw [GridData.DeterminativeSpineLength.word_one h2 (to_horizontal_edge_no_epsilon_eq_nil hb₂)]
        apply GridData.to_grid at h2
        rw [to_horizontal_edge_no_epsilon_eq_nil hb₂] at h2
        have : r = [] ∧ s = p := Grid.DeterminativeSpine.word_one h2
        aesop
      | n + 1 =>
        rcases PartialGrid.splittable_vertically h1 b₁ b₂ rfl (by aesop) (by aesop) with
          ⟨center, c₁, m₁, c₂, m₂, p1, p2, ⟨hf⟩, ⟨hl⟩⟩ | ⟨drest, h3, ⟨d2_is⟩, ⟨mid_nil⟩, len3⟩
        · rw [hl]
          specialize h1_ih p1 ha hb₁
          rcases h1_ih.2.1 with ⟨rest, hr⟩
          have rest_false : SignedList.is_false rest := by
            have : SignedList.is_false (rest ++ toSignedList center) := by
              rw [hr]
              exact is_false_to_vertical_edge_no_epsilon
            apply (SignedList.is_false_of_append this).1
          match hlr : rest with
          | [] =>
            specialize h2_ih p2 (by simp [← hr]) hb₂
            constructor
            · rcases middle_frontier_spec p1 with ⟨⟨rfl⟩⟩ | ⟨c_head, c_body, c_tail, ⟨c_spec⟩⟩
              · have ⟨hh, ho, hl⟩ := PartialGrid.empty_middle_frontier_matches_grid_with_length p1
                  ((toSignedList_eq_to_vertical_edge_no_epsilon_iff (left_side_is_false h1)).mp ha)
                  ((toSignedList_eq_to_horizontal_edge_no_epsilon_iff (top_side_is_true p1)).mp hb₁) t
                have : c = c₁ ++ c₂ := by
                  have := bottom_frontier_spec_from_split_vertically h1 p1 p2 rfl hf
                  aesop
                subst ho
                rw [this, to_horizontal_edge_no_epsilon_mul,
                  to_horizontal_edge_no_epsilon_toList_eq_toSignedList (bottom_frontier_is_true p1)]
                aesop
              have : c = c₁ := by
                have := bottom_frontier_spec_from_split_vertically h1 p1 p2 rfl hf
                aesop
              rw [to_horizontal_edge_no_epsilon_mul, this]
              exact List.prefix_of_append h1_ih.1
            constructor
            · exact h2_ih.2.1
            linarith
          | rfirst :: rrest =>
            rcases middle_frontier_spec p1 with ⟨⟨rfl⟩⟩ | ⟨c_head, c_body, c_tail, ⟨c_spec⟩⟩
            · have ⟨hh, ho, hl⟩ := PartialGrid.empty_middle_frontier_matches_grid_with_length p1
                  ((toSignedList_eq_to_vertical_edge_no_epsilon_iff (left_side_is_false h1)).mp ha)
                  ((toSignedList_eq_to_horizontal_edge_no_epsilon_iff (top_side_is_true p1)).mp hb₁) t
              have : c = c₁ ++ c₂ := by
                have := bottom_frontier_spec_from_split_vertically h1 p1 p2 rfl hf
                aesop
              subst ho
              rw [this, hl, to_horizontal_edge_no_epsilon_mul,
                to_horizontal_edge_no_epsilon_toList_eq_toSignedList (bottom_frontier_is_true p1)]
              specialize h2_ih p2 ((toSignedList_eq_to_vertical_edge_no_epsilon_iff (
                right_frontier_is_false p1)).mpr hh) hb₂
              aesop
            have : c = c₁ := by
              have := bottom_frontier_spec_from_split_vertically h1 p1 p2 rfl hf
              aesop
            rw [to_horizontal_edge_no_epsilon_mul, this]
            constructor
            · exact List.prefix_of_append h1_ih.1
            have p3 := PartialGrid.extend_left_side_w_length p2 (SignedList.to_SignedOptionList (rfirst::rrest)) (
              SignedList.is_false_to_SignedOptionList rest_false) (by simp [SignedList.to_SignedOptionList])
            rw [p3.2.1]
            specialize h2_ih p3.1
            simp only [toSignedList_append, toSignedList_toSignedOptionList, List.cons_append, ← hr,
              hb₂, toSignedList_nil, List.nil_prefix, true_and, forall_const] at h2_ih
            exact ⟨h2_ih.1, by linarith⟩
        specialize h1_ih h3 ha hb₁
        constructor
        · rw [to_horizontal_edge_no_epsilon_mul]
          exact List.prefix_of_append h1_ih.1
        constructor
        · aesop
        linarith

theorem frontier_prefix_generalized (h : GridData i j k l) (h1 : PartialGrid a b c mid d) :
    (SignedOptionList.toList (FreeGroup.invRev a) = i → SignedOptionList.toList b <+: j →
      (SignedOptionList.toList c <+: k ∧ h1.length ≤ h.length)) ∧
    (SignedOptionList.toList b = j → SignedOptionList.toList (FreeGroup.invRev a) <+: i →
      (SignedOptionList.toList (FreeGroup.invRev d) <+: l) ∧ h1.length ≤ h.length) := by
  constructor
  · intro ha hb
    rcases hb with ⟨rest, hrest⟩
    match rest with
    | [] =>
      rw [List.append_nil] at hrest
      have := frontier_prefix h h1 (((toSignedList_eq_to_vertical_edge_no_epsilon_iff (left_side_is_false h1)).mpr ha.symm))
        ((toSignedList_eq_to_horizontal_edge_no_epsilon_iff (top_side_is_true h1)).mpr hrest.symm)
      constructor
      · exact (toSignedList_prefix_to_horizontal_edge_no_epsilon_iff (bottom_frontier_is_true h1)).mp this.1
      aesop
    | rf :: rt =>
      have p1 := PartialGrid.extend_top_side_w_length h1 (to_horizontal_edge (rf :: rt))
        is_true_to_horizontal_edge (by refine List.ne_nil_of_length_pos to_horizontal_edge_length_pos)
      have := frontier_prefix h p1.1
        ((toSignedList_eq_to_vertical_edge_no_epsilon_iff (left_side_is_false h1)).mpr ha.symm)
        (by rw [← hrest, to_horizontal_edge_no_epsilon_append, to_horizontal_edge_no_epsilon_toList_eq_toSignedList (
          top_side_is_true h1), toSignedList_append, toSignedList_to_horizontal_edge])
      constructor
      · exact (toSignedList_prefix_to_horizontal_edge_no_epsilon_iff (bottom_frontier_is_true h1)).mp this.1
      rw [p1.2.1]
      exact this.2.2
  intro hb ha
  rcases ha with ⟨rest, hrest⟩
  match rest with
  | [] =>
    rw [List.append_nil] at hrest
    have := frontier_prefix h h1 (((toSignedList_eq_to_vertical_edge_no_epsilon_iff (left_side_is_false h1)).mpr hrest.symm))
      ((toSignedList_eq_to_horizontal_edge_no_epsilon_iff (top_side_is_true h1)).mpr hb.symm)
    constructor
    · exact (toSignedList_suffix_to_vertical_edge_no_epsilon_iff (right_frontier_is_false h1)).mp this.2.1
    aesop
  | rf :: rt =>
    have p1 := PartialGrid.extend_left_side_w_length h1 (to_vertical_edge (rf :: rt))
      is_false_to_vertical_edge (by refine List.ne_nil_of_length_pos to_vertical_edge_length_pos)
    have := frontier_prefix h p1.1
      (by rw [← hrest, to_vertical_edge_no_epsilon_append,
        to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList (left_side_is_false h1),
        toSignedList_append, toSignedList_to_vertical_edge]) (
        (toSignedList_eq_to_horizontal_edge_no_epsilon_iff (top_side_is_true h1)).mpr hb.symm)
    constructor
    · exact (toSignedList_suffix_to_vertical_edge_no_epsilon_iff (right_frontier_is_false h1)).mp this.2.1
    rw [p1.2.1]
    exact this.2.2

noncomputable def FrontierPrefixData (h : GridData i j l k) (h1 : PartialGrid a b mid d2 e2)
  : (toList (FreeGroup.invRev a) = i → List.PrefixData (toList b) j → List.PrefixData (toList mid) l)
  × (toList b = j → List.PrefixData (toList (FreeGroup.invRev a)) i → List.PrefixData (toList (FreeGroup.invRev e2)) k) := by
  constructor
  · intro ha hb
    have H := (frontier_prefix_generalized h h1).1 ha (List.PrefixData.to_IsPrefix hb)
    exact List.PrefixData.from_IsPrefix H.1
  intro hb ha
  have H := (frontier_prefix_generalized h h1).2 hb (List.PrefixData.to_IsPrefix ha)
  exact List.PrefixData.from_IsPrefix ((frontier_prefix_generalized h h1).2 hb (List.PrefixData.to_IsPrefix ha)).1
