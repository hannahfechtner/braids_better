import BraidProject.PartialGrid.NestedFrame
import BraidProject.SemiThue
import BraidProject.Relations
import BraidProject.PartialGrid.FrontierPossibilities

namespace Braid
namespace PartialGrid

theorem SemiThue_reversing_nil (h : SemiThue reversing_prop a b) (ha : a = []) : b = [] := by
  induction h with
  | refl => exact ha
  | step c d h => cases h ; all_goals simp at ha
  | trans _ _ _ _ => aesop

noncomputable def grid_to_rev (h : GridData a b c d) : SemiThue reversing_prop
  (to_vertical_edge_no_epsilon a ++ to_horizontal_edge_no_epsilon b) (to_horizontal_edge_no_epsilon c ++ to_vertical_edge_no_epsilon d) := by
  induction h with
  | empty => exact SemiThue.refl
  | top_bottom i => exact SemiThue.refl
  | sides i => exact SemiThue.refl
  | top_left i => exact SemiThue.of_rel (reversing_prop.basic)
  | adjacent i k h => exact SemiThue.of_rel (reversing_prop.close h)
  | separated i j h => exact SemiThue.of_rel (reversing_prop.apart h)
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [to_vertical_edge_no_epsilon_mul, to_vertical_edge_no_epsilon_mul, List.append_assoc]
    apply (SemiThue.append_left h1_ih).trans
    rw [← List.append_assoc, ← List.append_assoc]
    exact SemiThue.append_right h2_ih
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [to_horizontal_edge_no_epsilon_mul, to_horizontal_edge_no_epsilon_mul, ← List.append_assoc]
    apply (SemiThue.append_right h1_ih).trans
    rw [List.append_assoc, List.append_assoc]
    exact SemiThue.append_left h2_ih

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
    rename_i k l m n o p q
    change _ = to_vertical_edge_no_epsilon (k.toList ++ o.toList) at ha
    rw [to_vertical_edge_no_epsilon_append] at ha
    rcases SignedOptionList.toSignedList_eq_append ha with ⟨a₃, a₄, ha, ha₃, ha₄⟩
    match a₄ with
    | [] =>
      simp only [SignedOptionList.toSignedList_nil, List.nil_eq] at ha₄
      have ⟨hm, hn⟩:= GridData.DeterminativeSpine.one_word h1 (to_vertical_edge_no_epsilon_eq_nil ha₄)
      exact @h2_ih _ _ _ _ _ c2 d2 h (by aesop) (by aesop) (by assumption) (by rw [hd, hn]; rfl)
    | x :: xs =>
      match a₃ with
      | [] =>
        simp only [SignedOptionList.toSignedList_nil, List.nil_eq] at ha₃
        have ⟨hp, hn⟩:= GridData.DeterminativeSpine.one_word h2 (to_vertical_edge_no_epsilon_eq_nil ha₃)
        exact @h1_ih _ _ _ _ _ c2 d2 h (by aesop) (by aesop) (by aesop) (by rw [hd, hn, mul_one])
      | y :: ys =>
      rcases PartialGrid.splittable_horizontally h _ _ ha (by simp) (by simp) with
          ⟨center, r, s, t, u, v, w, ⟨⟨z⟩, ⟨_⟩⟩⟩ | ⟨r, s, _, ⟨u⟩, ⟨v⟩⟩
      · have := PartialGrid.frontier_prefix h1 v ha₄ hb
        rcases this with ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩, hl⟩
        have r₁t : SignedList.is_true r₁ := by
          have : SignedList.is_true (to_horizontal_edge_no_epsilon m) :=
            is_true_to_horizontal_edge_no_epsilon
          rw [← hr₁] at this
          exact (SignedList.is_true_of_append this).2
        specialize h1_ih v ha₄ hb hr₁ hr₂
        rcases right_frontier_spec_from_split_horizontally h v w ha z with ⟨rfl, h3⟩ | h4
        · have := SemiThue_reversing_nil h1_ih (by simp)
          rw [List.append_eq_nil_iff] at this
          rw [h3] at z
          simp only [List.append_nil, List.append_assoc, List.append_cancel_right_eq] at z
          rw [← z]
          rw [this.1, List.append_nil] at hr₁
          simp only [h3, SignedOptionList.toSignedList_append, ← List.append_assoc,
            to_vertical_edge_no_epsilon_mul, ← hr₂, this.2, List.nil_append,
            List.append_cancel_right_eq] at hd
          exact @h2_ih _ _ _ _ _ c2 d2 w ha₃ hr₁ hc hd
        simp only [h4.2, List.append_cancel_right_eq] at z
        simp only [h4.2, to_vertical_edge_no_epsilon_mul, ← hr₂, ← List.append_assoc,
          List.append_cancel_right_eq] at hd
        rw [← z, hd]
        match r₁ with
        | [] =>
          rw [List.append_nil] at hr₁
          rcases (PartialGrid.frontier_prefix h2 w ha₃ hr₁).2.1 with ⟨rest, hrest⟩
          specialize @h2_ih _ _ _ _ _ c2 rest w ha₃ (by assumption) (by assumption) hrest
          rw [← hrest, List.append_assoc, SignedOptionList.toSignedList_append, ← List.append_assoc,
            SignedOptionList.toSignedList_append, ← List.append_assoc, ← List.append_assoc,
            List.append_assoc (c2 ++ rest), List.append_assoc (SignedOptionList.toSignedList r)]
          rw [List.nil_append] at h1_ih
          exact SemiThue.append h2_ih (SemiThue.append_left h1_ih)
        | r₁h :: r₁ta =>
        have := PartialGrid.extend_top_side w (SignedList.to_SignedOptionList (r₁h :: r₁ta))
          (SignedList.is_true_to_SignedOptionList r₁t) (List.ne_nil_of_length_pos
          (by rw [SignedList.to_SignedOptionList_length]; simp))
        have new_ih₂ :=
          h2_ih this ha₃ (by rw [← hr₁, SignedOptionList.toSignedList_append,
          SignedOptionList.toSignedList_toSignedOptionList]) hc
          (by simp only [SignedOptionList.toSignedList_nil, List.append_nil]; rfl)
        rw [SignedOptionList.toSignedList_append]
        apply (SemiThue.append_left h1_ih).trans
        simp only [← List.append_assoc]
        apply SemiThue.append_right
        convert new_ih₂
        simp
      rw [v.1, SignedOptionList.toSignedList_nil, List.nil_append] at hc
      rename_i pg _
      rcases (PartialGrid.frontier_prefix h1 pg ha₄ hb).2.1 with ⟨rest, hrest⟩
      simp only [to_vertical_edge_no_epsilon_mul, ← hrest, ← List.append_assoc,
        List.append_cancel_right_eq] at hd
      rw [u, hd, hc, SignedOptionList.toSignedList_append]
      rcases (PartialGrid.frontier_prefix h1 pg ha₄ hb).1 with ⟨rest2, hrest2⟩
      specialize h1_ih pg (by assumption) (by assumption) hrest2 hrest
      apply (SemiThue.append_left h1_ih).trans
      simp only [← List.append_assoc]
      apply SemiThue.append_right
      rw [SignedOptionList.toSignedList_append, List.append_assoc, hrest2]
      convert grid_to_rev h2
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i k l m n o p q
    change _ = to_horizontal_edge_no_epsilon (l.toList ++ o.toList) at hb
    rw [to_horizontal_edge_no_epsilon_append] at hb
    rcases SignedOptionList.toSignedList_eq_append hb with ⟨b₃, b₄, hb, hb₃, hb₄⟩
    match b₃ with
    | [] =>
      simp only [SignedOptionList.toSignedList_nil, List.nil_eq] at hb₃
      have ⟨hm, rfl⟩:= GridData.DeterminativeSpine.word_one h1 (to_horizontal_edge_no_epsilon_eq_nil hb₃)
      exact @h2_ih _ _ _ _ _ c2 d2 h (by assumption) (by aesop) (by rw [hc, hm]; rfl) (by assumption)
    | x :: xs =>
      match b₄ with
      | [] =>
        simp only [SignedOptionList.toSignedList_nil, List.nil_eq] at hb₄
        have ⟨hp, rfl⟩:= GridData.DeterminativeSpine.word_one h2 (to_horizontal_edge_no_epsilon_eq_nil hb₄)
        exact @h1_ih _ _ _ _ _ c2 d2 h (by assumption) (by aesop) (by rw [hc, hp, mul_one]) (by assumption)
      | y :: ys =>
      rcases PartialGrid.splittable_vertically h _ _ hb (by simp) (by simp) with
          ⟨center, r, s, t, u, v, w, ⟨⟨z⟩, ⟨_⟩⟩⟩ | ⟨r, s, _, ⟨u⟩, ⟨v⟩⟩
      · have := PartialGrid.frontier_prefix h1 v ha hb₃
        rcases this with ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩, hl⟩
        have r₂f : SignedList.is_false r₂ := by
          have : SignedList.is_false (to_vertical_edge_no_epsilon n) :=
            is_false_to_vertical_edge_no_epsilon
          rw [← hr₂] at this
          exact (SignedList.is_false_of_append this).1
        specialize h1_ih v ha hb₃ hr₁ hr₂
        rcases bottom_frontier_spec_from_split_vertically h v w hb z with ⟨rfl, h3⟩ | h4
        · have := SemiThue_reversing_nil h1_ih (by simp)
          rw [List.append_eq_nil_iff] at this
          rw [h3] at z
          simp only [List.append_assoc, List.append_nil, List.append_cancel_left_eq] at z
          rw [z]
          simp only [h3, SignedOptionList.toSignedList_append, List.append_assoc,
            to_horizontal_edge_no_epsilon_mul, ← hr₁, List.append_cancel_left_eq, this.1, List.nil_append] at hc
          exact h2_ih w (by simp_all) (by assumption) hc (by assumption)
        simp only [h4.2, List.append_assoc, List.append_cancel_left_eq] at z
        simp only [h4.2, to_horizontal_edge_no_epsilon_mul, ← hr₁, List.append_assoc,
          List.append_cancel_left_eq] at hc
        rw [z, hc]
        match r₂ with
        | [] =>
          rcases (PartialGrid.frontier_prefix h2 w (by assumption) hb₄).1 with ⟨rest, hrest⟩
          specialize @h2_ih _ _ _ _ _ rest d2 w (by simp_all) (by assumption) hrest (by assumption)
          rw [← hrest, List.append_assoc, SignedOptionList.toSignedList_append, List.append_assoc,
            SignedOptionList.toSignedList_append]
          rw [List.append_nil] at h1_ih
          exact SemiThue.append h1_ih (SemiThue.append_left h2_ih)
        | r₂h :: r₂t =>
        have := PartialGrid.extend_left_side w (SignedList.to_SignedOptionList (r₂h :: r₂t))
          (SignedList.is_false_to_SignedOptionList r₂f) (List.ne_nil_of_length_pos
          (by rw [SignedList.to_SignedOptionList_length]; simp))
        have new_ih₂ : SemiThue reversing_prop (SignedOptionList.toSignedList
            (SignedList.to_SignedOptionList (r₂h :: r₂t) ++ t ++ u))
            (to_horizontal_edge_no_epsilon p ++ d2) :=
          h2_ih this (by rw [← hr₂, SignedOptionList.toSignedList_append,
          SignedOptionList.toSignedList_toSignedOptionList]) hb₄ (by simp) hd
        rw [SignedOptionList.toSignedList_append]
        apply (SemiThue.append_right h1_ih).trans
        simp only [List.append_assoc]
        apply SemiThue.append_left
        convert new_ih₂
        simp
      rw [u, SignedOptionList.toSignedList_nil, List.append_nil] at hd
      rcases (PartialGrid.frontier_prefix h1 s ha hb₃).1 with ⟨rest, hrest⟩
      simp only [to_horizontal_edge_no_epsilon_mul, ← hrest, List.append_assoc,
        List.append_cancel_left_eq] at hc
      rw [v, hd, hc, SignedOptionList.toSignedList_append]
      specialize h1_ih s (by assumption) (by assumption) hrest (by rw [SignedOptionList.toSignedList_nil, List.append_nil])
      apply (SemiThue.append_right h1_ih).trans
      simp only [List.append_assoc]
      apply SemiThue.append_left
      rw [hb₄]
      exact grid_to_rev h2

def frontier_reverses_to_grid_def (h : PartialGrid a1 b1 c1 d1 e1) :=
  ∀ {a b f g},
  (SignedOptionList.toSignedList a1 = to_vertical_edge_no_epsilon a) →
  SignedOptionList.toSignedList b1 = to_horizontal_edge_no_epsilon b →
  GridData a b g f →
  SemiThue reversing_prop (SignedOptionList.toSignedList (c1 ++ d1 ++ e1))
  (to_horizontal_edge_no_epsilon g ++ to_vertical_edge_no_epsilon f)

noncomputable def frontier_reverses_to_grid (h : PartialGrid a b c d e) : frontier_reverses_to_grid_def h := by
  intros a1 b1 f g ha hb h2
  have ⟨⟨c1, hc1⟩, ⟨e1, he1⟩, _⟩ := PartialGrid.frontier_prefix h2 h ha hb
  rw [← he1, ← hc1]
  simp only [List.append_assoc, SignedOptionList.toSignedList_append]
  apply SemiThue.append_left
  simp only [← List.append_assoc]
  exact SemiThue.append_right (pg_mid_frontier_reverses_to_grid_helper h ha hb hc1 he1 h2)
