import BraidProject.PartialGrid.Basic

namespace Braid

namespace PartialGrid

namespace DeterminativeFrameLength

theorem none_none (h : PartialGrid a b c d e) :
    a = [(none, false)] → b = [(none, true)] → h.length = 0 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i =>
      intro h1
      simp [to_vertical_edge] at h1
    | adjacent i k h =>
      intro h1
      simp [to_vertical_edge] at h1
    | separated i j h =>
      intro h1
      simp [to_vertical_edge] at h1
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H

theorem none_some (h : PartialGrid a b c d e) : a = [(none, false)] → b = [(some i, true)] → h.length = 0 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i =>  simp [PartialGrid.length]
    | sides i =>  simp [PartialGrid.length]
    | top_left i =>
      intro ha
      simp [to_vertical_edge] at ha
    | adjacent i k h =>
      intro ha
      simp [to_vertical_edge] at ha
    | separated i j h =>
      intro ha
      simp [to_vertical_edge] at ha
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H

theorem some_none {a b c d e i} (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(none, true)] → h.length = 0 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i =>  simp [PartialGrid.length]
    | sides i =>  simp [PartialGrid.length]
    | top_left i =>
      intro ha hb
      simp [to_horizontal_edge] at hb
    | adjacent i k h =>
      intro ha hb
      simp [to_horizontal_edge] at hb
    | separated i j h =>
      intro ha hb
      simp [to_horizontal_edge] at hb
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H

open SignedOptionList
theorem some_some_same {a b c d e i} (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some i, true)] →
  toSignedList (c ++ d ++ e) = [] → h.length = 1 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h =>simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro ha hb rm
    rw [ha, hb] at rm
    simp [toSignedList] at rm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H

theorem some_some_close (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some j, true)] →
    toSignedList (c ++ d ++ e) = [(j, true), (i, true), (j, false), (i, false)] → i.dist j = 1 → h.length = 1 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h => simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro a_is b_is rm
    simp [a_is, b_is, toSignedList] at rm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H

theorem some_some_apart (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some k, true)] →
    toSignedList (c ++ d ++ e) = [(k, true), (i, false)] → i.dist k > 1 → h.length = 1 := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h => simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro a_is b_is rm
    simp [a_is, b_is, toSignedList] at rm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_side_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    rw [hb.2] at H
    simp at H

end DeterminativeFrameLength

namespace DeterminativeSpineEmptyMiddleFrontier

theorem none_none {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(none, false)]) (hb : b = [(none, true)]) (hd : d = []) :
  c = [(none, true)] ∧ e = [(none, false)] := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [to_horizontal_edge, to_vertical_edge]
    | top_bottom i => simp [to_horizontal_edge] at hb
    | sides i => simp [to_vertical_edge] at ha
    | top_left i => simp [to_horizontal_edge] at hb
    | adjacent i k h => simp [to_horizontal_edge] at hb
    | separated i j h => simp [to_horizontal_edge] at hb
  | empty a b ha ha1 hb hb1 => simp [ha] at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H

theorem none_some {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(none, false)]) (hb : b = [(some i, true)]) (hd : d = []) :
  c = [(some i, true)] ∧ e = [(none, false)] := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [to_horizontal_edge] at hb
    | top_bottom i => simp [ha, hb]
    | sides i => simp [to_horizontal_edge] at hb
    | top_left i => simp [to_vertical_edge] at ha
    | adjacent i k h => simp [to_vertical_edge] at ha
    | separated i j h => simp [to_vertical_edge] at ha
  | empty a b ha ha1 hb hb => simp [ha] at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H

theorem some_none {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(some i, false)]) (hb : b = [(none, true)]) (hd : d = []) :
  c = [(none, true)] ∧ e = [(some i, false)] := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [to_vertical_edge] at ha
    | top_bottom i => simp [ha, hb]
    | sides i => simp [ha, hb]
    | top_left i => simp [to_horizontal_edge] at hb
    | adjacent i k h => simp [to_horizontal_edge] at hb
    | separated i j h => simp [to_horizontal_edge] at hb
  | empty a b ha ha1 hb hb => simp [ha] at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H

theorem some_some_same {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(some i, false)]) (hb : b = [(some i, true)]) (hd : d = []) :
  c = [(none, true)] ∧ e = [(none, false)] := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [to_vertical_edge] at ha
    | top_bottom i => simp [to_vertical_edge] at ha
    | sides i => simp [to_horizontal_edge] at hb
    | top_left i => simp
    | adjacent i k h => grind [to_vertical_edge, to_horizontal_edge, Nat.dist]
    | separated i j h => grind [to_vertical_edge, to_horizontal_edge, Nat.dist]
  | empty a b ha ha1 hb hb => simp [ha] at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H

theorem some_some_close {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(some i, false)]) (hb : b = [(some j, true)]) (hd : d = []) (hij : i.dist j = 1):
  c = [(some j, true), (some i, true)] ∧ e = [(some j, false), (some i, false)] := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [to_vertical_edge] at ha
    | top_bottom i => simp [to_vertical_edge] at ha
    | sides i => simp [to_horizontal_edge] at hb
    | top_left i => grind [to_vertical_edge, to_horizontal_edge, Nat.dist]
    | adjacent i k h => grind [to_vertical_edge, to_horizontal_edge]
    | separated i j h => grind [to_vertical_edge, to_horizontal_edge]
  | empty a b ha ha1 hb hb => simp [ha] at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H

theorem some_some_apart {a b c d e} (h : PartialGrid a b c d e)
  (ha : a = [(some i, false)]) (hb : b = [(some j, true)]) (hd : d = []) (hij : i.dist j > 1):
  c = [(some j, true)] ∧ e = [(some i, false)] := by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp [to_vertical_edge] at ha
    | top_bottom i => simp [to_vertical_edge] at ha
    | sides i => simp [to_horizontal_edge] at hb
    | top_left i => grind [to_vertical_edge, to_horizontal_edge, Nat.dist]
    | adjacent i k h => grind [to_vertical_edge, to_horizontal_edge]
    | separated i j h => grind [to_vertical_edge, to_horizontal_edge]
  | empty a b ha ha1 hb hb1 => simp [ha] at hd
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp hb with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.top_length_pos g1
      simp at H
    have H := PartialGrid.top_length_pos g2
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rcases List.append_eq_singleton_iff.mp ha with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · have H := PartialGrid.left_side_length_pos g2
      simp at H
    have H := PartialGrid.left_side_length_pos g1
    simp at H

end DeterminativeSpineEmptyMiddleFrontier

end PartialGrid

end Braid
