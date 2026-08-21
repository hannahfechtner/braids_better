import BraidProject.PartialGrid.NestedFrame
import BraidProject.SemiThue
import BraidProject.Relations
import BraidProject.PartialGrid.FrontierPossibilities

namespace Braid
namespace PartialGrid

noncomputable def pg_mid_frontier_reverses_to_grid_helper
    (h : PartialGrid a1 b1 c1 m1 d1)
    (ha : SignedOptionList.toSignedList a1 = to_vertical_edge_no_epsilon a)
    (hb : SignedOptionList.toSignedList b1 = to_horizontal_edge_no_epsilon b)
    (hc : SignedOptionList.toSignedList c1 ++ c2 = to_horizontal_edge_no_epsilon g)
    (hd : d2 ++ SignedOptionList.toSignedList d1 = to_vertical_edge_no_epsilon f)
    (h2 : GridData a b g f) :
    SemiThue reversing_prop (SignedOptionList.toSignedList m1)
      (c2 ++ d2) := by
  induction h2 generalizing a1 b1 c1 m1 d1 c2 d2 with
  | empty =>
    change _ = [] at hc
    change _ = [] at hd
    rw [List.append_eq_nil_iff] at hc hd
    rw [hc.2, hd.1]
    have := PartialGrid.FrontierPossibilitiesEpsilonRemoved.empty_empty h ha hb
    simp_all
    exact SemiThue.refl
  | top_bottom i =>
    change _ = [(i, true)] at hc
    have := PartialGrid.FrontierPossibilitiesEpsilonRemoved.empty_generator h ha hb
    convert SemiThue.refl
    aesop
  | sides i =>
    change _ = [(i, false)] at hd
    have := PartialGrid.FrontierPossibilitiesEpsilonRemoved.generator_empty h hb ha
    convert SemiThue.refl
    aesop
  | top_left i =>
    rw [(FreeMonoid.prod_eq_one hc).2, (FreeMonoid.prod_eq_one hd).1]
    have := PartialGrid.FrontierPossibilitiesEpsilonRemoved.generator_generator_same h ha hb
    have : SignedOptionList.toSignedList m1 = [] ∨ SignedOptionList.toSignedList m1 = [(i, false), (i, true)] := by aesop
    rcases this with h1 | h2
    · rw [h1]
      exact SemiThue.refl
    apply SemiThue.of_rel
    rw [h2]
    exact reversing_prop.basic
  | adjacent i k hd =>
    have := PartialGrid.FrontierPossibilitiesEpsilonRemoved.generator_generator_close h ha hb (by assumption)
    change _ = [(k, true), (i, true)] at hc
    change _ = [(k, false), (i, false)] at hd
    rcases this with ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩
    any_goals
      rw [hm1]
      rw [hc1] at hc
      rw [hd1] at hd
      simp at hc
    any_goals simp at hd
    any_goals change _ = [(k, false)] ++ [(i , false)] at hd; rw [List.append_left_inj] at hd
    any_goals
      rw [hc, hd]
    any_goals
      apply SemiThue.of_rel
      exact reversing_prop.close (by assumption)
    any_goals
      apply SemiThue.refl
  | separated i j h =>
    have := PartialGrid.FrontierPossibilitiesEpsilonRemoved.generator_generator_apart h ha hb (by assumption)
    change _ = [(j, true)] at hc
    change _ = [(i, false)] at hd
    rcases this with ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩ | ⟨hc1, hm1, hd1⟩| ⟨hc1, hm1, hd1⟩
    any_goals
      rw [hm1]
      rw [hc1] at hc
      rw [hd1] at hd
      simp at hc hd
      rw [hc, hd]
    any_goals
      apply SemiThue.of_rel
      apply reversing_prop.apart (by assumption)
    all_goals
      apply SemiThue.refl
  | vertical h1 h2 h1_ih h2_ih =>
    sorry
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i k l m n o p q
    change _ = to_horizontal_edge_no_epsilon (l.toList ++ o.toList) at hb
    rw [to_horizontal_edge_no_epsilon_append] at hb
    rcases SignedOptionList.toSignedList_eq_append hb with ⟨b₃, b₄, hb, hb₃, hb₄⟩
    match b₃ with
    | [] => sorry
    | x :: xs =>
      match b₄ with
      | [] => sorry
      | y :: ys =>
      rcases PartialGrid.splittable_vertically h _ _ hb (by simp) (by simp) with ⟨center, r, s, t, u, v, w, ⟨⟨z⟩, ⟨_⟩⟩⟩ | ⟨⟩
      · have hl : SignedOptionList.toList (x :: xs) = l := by
          apply to_horizontal_edge_no_epsilon_injective
          change _ = to_horizontal_edge_no_epsilon l at hb₃
          rw [← hb₃]
          refine to_horizontal_edge_no_epsilon_toList_eq_toSignedList ?_
          exact top_side_is_true v
        have hk : SignedOptionList.toList (FreeGroup.invRev a1) <+: k := by
          have : SignedOptionList.toList (FreeGroup.invRev a1) = k := by
            apply to_vertical_edge_no_epsilon_inj
            change _ = to_vertical_edge_no_epsilon k at ha
            rw [← ha]
            exact to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList (left_side_is_false v)
          rw [this]
        have := (PartialGrid.frontier_prefix' h1 v).2 hl hk
        rcases this with ⟨rest, hrest⟩
        specialize h1_ih v ha hb₃ _ hrest


        have := PartialGrid.extend_left_side w (to_vertical_edge m₁)
          is_false_to_vertical_edge (List.ne_nil_of_length_pos
            to_vertical_edge_length_pos)
        specialize h2_ih this
        rw [← hm] at h2_ih
        have hmc : SignedOptionList.toSignedList (to_vertical_edge m₁ ++ center) =
          to_vertical_edge_no_epsilon (SignedOptionList.toList (FreeGroup.invRev center) ++ m₁) := by
          simp only [SignedOptionList.toSignedList_append, SignedOptionList.toList_invRev,
            to_vertical_edge_no_epsilon_append]
          congr
          · refine toSignedList_to_vertical_edge ?_
            sorry
          rw [← SignedOptionList.toList_reverse, to_vertical_edge_no_epsilon_toList_rev_eq_toSignedList]
          exact right_frontier_is_false v
        specialize h2_ih hmc (List.reverse_inj.mp (congrArg List.reverse hb₄))
        refine SemiThue.trans ?_ (h2_ih ?_ ?_)


def frontier_reverses_to_grid (h : PartialGrid a1 b1 c1 d1 e1) :=
  ∀ {a b f g},
  (SignedOptionList.toSignedList a1 = to_vertical_edge_no_epsilon a) →
  SignedOptionList.toSignedList b1 = to_horizontal_edge_no_epsilon b →
  GridData a b g f →
  SemiThue reversing_prop (SignedOptionList.toSignedList (c1 ++ d1 ++ e1))
  (to_horizontal_edge_no_epsilon g ++ to_vertical_edge_no_epsilon f)

noncomputable def frontier_reverses_to_grid_holds (h : PartialGrid a b c d e) : frontier_reverses_to_grid h := by
  intros a1 b1 f g ha hb h2
  have ⟨H2, H3⟩ := PartialGrid.frontier_prefix' h2 h
  have ha' : SignedOptionList.toList (FreeGroup.invRev a) = a1 := by
    refine to_vertical_edge_no_epsilon_inj ?_
    rw [← ha]
    refine to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList (left_side_is_false h)
  have hb' : SignedOptionList.toList b = b1 := by
    refine to_horizontal_edge_no_epsilon_injective ?_
    rw [← hb]
    refine to_horizontal_edge_no_epsilon_toList_eq_toSignedList (top_side_is_true h)
  specialize H2 ha' (by rw [hb'])
  specialize H3 hb' (by rw [ha'])
  rcases H2 with ⟨c1, hc1⟩
  rcases H3 with ⟨e1, he1⟩
  have hc2 := congr_arg to_horizontal_edge_no_epsilon hc1
  rw [to_horizontal_edge_no_epsilon_append, to_horizontal_edge_no_epsilon_toList_eq_toSignedList
    (bottom_frontier_is_true h)] at hc2
  have he2 := congr_arg to_vertical_edge_no_epsilon he1
  rw [to_vertical_edge_no_epsilon_append, to_vertical_edge_no_epsilon_toList_invRev_eq_toSignedList
    (right_frontier_is_false h)] at he2
  have H := pg_mid_frontier_reverses_to_grid_helper h ha hb hc2 he2 h2
  rw [← he1, ← hc1]
  simp [SignedOptionList.toSignedList_append, to_horizontal_edge_no_epsilon_append,
    to_horizontal_edge_no_epsilon_toList_eq_toSignedList (bottom_frontier_is_true h)]
  apply SemiThue.append_left
  sorry
  -- rw [← List.append_assoc]
  -- apply SemiThue.append_right
  -- exact H

noncomputable def pg_mid_frontier_reverses_to_grid
    (h : PartialGrid a1 b1 c1 d1 e1)
    (ha : a1 = to_vertical_edge a) (hb : b1 = to_horizontal_edge b)
    (h2 : GridData a b g f) :
    SemiThue reversing_prop (SignedOptionList.toSignedList (c1 ++ d1 ++ e1))
      (to_horizontal_edge_no_epsilon g ++ to_vertical_edge_no_epsilon f) := by
  have ⟨H2, H3⟩ := PartialGrid.FrontierPrefixData h2 h
  rw [ha, hb] at H2 H3
  rw [toList_invRev_to_vertical_edge] at H3
  rw [toList_to_horizontal_edge] at H2
  specialize H3 toList_to_horizontal_edge List.PrefixData.refl
  specialize H2 toList_invRev_to_vertical_edge List.PrefixData.refl
  rcases H2 with ⟨c2, ⟨hc2⟩⟩
  rcases H3 with ⟨e2, ⟨he2⟩⟩
  have ha1 : SignedOptionList.toSignedList a1 = to_vertical_edge_no_epsilon a := by
    rw [ha]
    sorry --exact remove_up_is_no_epsilon
  have hb1 : SignedOptionList.toSignedList b1 = to_horizontal_edge_no_epsilon b := by
    rw [hb]
    refine toSignedList_to_horizontal_edge ?_
    sorry --exact remove_over_is_no_epsilon
  have H := frontier_reverses_to_grid_holds h ha1 hb1 h2
  rw [← he2, ← hc2]
  simp [SignedOptionList.toSignedList_append, to_horizontal_edge_no_epsilon_append]
  sorry
  -- apply SemiThue.append_left
  -- rw [← List.append_assoc]
  -- apply SemiThue.append_right
  -- exact H h2
