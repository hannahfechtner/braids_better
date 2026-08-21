import BraidProject.PartialGrid.ToGrid
import BraidProject.PartialGrid.FrontierPossibilities
import BraidProject.PartialGrid.NestedFrame

namespace Braid

open SignedOptionList PartialGrid PartialGrid.FrontierPossibilitiesEpsilonRemovedBoolRemoved

theorem PartialGrid.length_le_GridData_length
    (h : PartialGrid a b c d e) (h1 : GridData a1 b1 g f) :
    toList (FreeGroup.invRev a) = a1 → toList b = b1 →
    h.length ≤ GridData.length h1 := by
  induction h1 generalizing a b c d e with
  | empty =>
    intro ha hb
    simp [empty_empty h ha hb]
  | top_bottom i =>
    intro ha hb
    simp [empty_generator h ha hb]
  | sides i =>
    intro ha hb
    simp [generator_empty h ha (toList_invRev_eq_nil_iff.mpr hb)]
  | top_left i =>
    intro ha hb
    have := generator_generator_same h ha hb
    rw [GridData.length]
    aesop
  | adjacent i k hd =>
    intro ha hb
    have := generator_generator_close h (toList_invRev_eq_singleton_iff.mp ha) hb hd
    rw [GridData.length]
    aesop
  | separated i j hd =>
    intro ha hb
    have := generator_generator_apart h (toList_invRev_eq_singleton_iff.mp ha) hb hd
    rw [GridData.length]
    aesop
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i i j k l m n o
    intro a_is b_is
    rcases toList_invRev_eq_append_cases a_is with one | two | splits
    · have i_one : i = 1 := by
        convert one
      rw [i_one, one_mul] at a_is
      specialize h2_ih h a_is
      have H := GridData.DeterminativeSpine.one_word h1 i_one
      have H : GridData.length h1 = 0 := GridData.DeterminativeSpineLength.one_word h1 one
      simp [H, GridData.length]
      apply h2_ih
      convert b_is
      aesop
    · have i_one : m = 1 := by
        convert two
      rw [i_one, mul_one] at a_is
      specialize h1_ih h a_is
      have H := GridData.DeterminativeSpine.one_word h2 i_one
      have H : GridData.length h2 = 0 := GridData.DeterminativeSpineLength.one_word h2 two
      simp [H, GridData.length]
      apply h1_ih
      exact b_is
    rcases splits with ⟨a1, a2, a1_len, a2_len, H, a1m, a2i⟩
    have H' := congr_arg FreeGroup.invRev H
    simp at H'
    rcases splittable_horizontally h _ _ H' a1_len a2_len
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl]
      have hi1 := h1_ih i1 a1m b_is
      have hi2 : i2.length ≤ GridData.length h2 := by
        have H : toList mid <+: k :=
          by sorry --(PartialGrid.frontier_prefix h1 i1).1 a1m (by rw [b_is])
        rcases H with ⟨r, hr⟩
        match r_is : r with
        | [] =>
          rw [List.append_nil] at hr
          exact h2_ih i2 (a2i) hr
        | r1 :: r2 =>
          have i3 := PartialGrid.extend_top_side_w_length i2 (to_horizontal_edge (r1 :: r2))
            is_true_to_horizontal_edge (by simp [to_horizontal_edge])
          specialize h2_ih i3.1 (a2i)
          subst hr
          simp only [toList_append, toList_to_horizontal_edge, forall_const] at h2_ih
          rw [i3.2.1]
          exact h2_ih
      simp [GridData.length]
      omega
    rcases baaad with ⟨c1, drest, i1, ⟨long⟩, ⟨c_nil⟩, ⟨len⟩⟩
    specialize h1_ih i1 a1m b_is
    simp [GridData.length]
    omega
  | horizontal h1 h2 h1_ih h2_ih =>
    intro a_is b_is
    rename_i i j k l m n o
    rcases SignedOptionList.toList_eq_append_cases b_is with one | two | splits
    · have i_one : j = 1 := by
        convert one
      rw [i_one, one_mul] at b_is
      have H := GridData.DeterminativeSpine.word_one h1 i_one
      rw [← H.2] at a_is
      specialize h2_ih h a_is b_is
      have H : GridData.length h1 = 0 := GridData.DeterminativeSpineLength.word_one h1 one
      simp [H, GridData.length, h2_ih]
    · have m_one : m = 1 := by
        convert two
      rw [m_one, mul_one] at b_is
      have H := GridData.DeterminativeSpine.word_one h2 m_one
      specialize h1_ih h a_is b_is
      have H : GridData.length h2 = 0 := GridData.DeterminativeSpineLength.word_one h2 two
      simp [H, GridData.length, h1_ih]
    rcases splits with ⟨b1, b2, b1_len, b2_len, bb1b2, b1j, b2m⟩
    rcases splittable_vertically h _ _ bb1b2 b1_len b2_len
      with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · rw [hl, GridData.length]
      have hone := h1_ih i1 a_is b1j
      have two : i2.length ≤ GridData.length h2 := by sorry
        -- have H2 := by so(frontier_prefix h1 i1).2 (by rw [b1j]; rfl) (by rw [a_is])
        -- rcases H2 with ⟨r, hr⟩
        -- match r with
        -- | [] =>
        --   rw [List.append_nil] at hr
        --   exact h2_ih i2 hr b2m
        -- | r1 :: r2 =>
        --   have H := PartialGrid.extend_left_side_w_length i2 (to_vertical_edge (r1::r2))
        --     is_false_to_vertical_edge (by simp [to_vertical_edge])
        --   rcases H with ⟨h3, ⟨len⟩⟩
        --   rw [len]
        --   have hk : toList (FreeGroup.invRev (to_vertical_edge (r1 :: r2) ++ mid)) = l := by
        --     rw [FreeGroup.invRev_append, SignedOptionList.toList_append]
        --     rw [← hr]
        --     simp
        --   exact h2_ih h3 hk b2m
      omega
    rcases baaad with ⟨drest, i1, ⟨len⟩, ⟨e_nil⟩, ⟨b2_is⟩⟩
    specialize h1_ih i1 a_is b1j
    simp [GridData.length]
    omega

theorem straight_pg_sm_g (h : PartialGrid a b c d e) (h1 : GridData a1 b1 f g)
    : a = to_vertical_edge a1 → b = to_horizontal_edge b1 → h.length ≤ GridData.length h1 := by
  intro ha hb
  apply PartialGrid.length_le_GridData_length h h1
  · rw [ha, toList_invRev_to_vertical_edge]
  rw [hb, toList_to_horizontal_edge]
