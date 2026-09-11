import BraidProject.PartialGrid.Splittability

namespace Braid
namespace PartialGrid
namespace FrontierPossibilitiesEpsilonRemovedBoolRemoved

open SignedOptionList

theorem empty_empty (h : PartialGrid a b c d e)
    (ha : SignedOptionList.toList (FreeGroup.invRev a) = [])
    (hb : SignedOptionList.toList b = []) :
    SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [] ∧
    SignedOptionList.toList (FreeGroup.invRev e) = [] ∧ h.length = 0:= by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp_all [PartialGrid.length]
    | top_bottom i => simp_all
    | sides i => simp_all [SignedOptionList.toList, FreeGroup.invRev]
    | top_left i => simp_all [to_vertical_edge, SignedOptionList.toList]
    | adjacent i k h => simp_all [to_vertical_edge, SignedOptionList.toList]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all [toList_invRev, PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all [toList_invRev, PartialGrid.length]
  | horizontal_append g1 g2 h g1_ih g2_ih => simp_all [toList_invRev, PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih => simp_all [toList_invRev, PartialGrid.length]

theorem empty_generator (h : PartialGrid a b c d e)
    (ha : SignedOptionList.toList (FreeGroup.invRev a) = [])
    (hb : SignedOptionList.toList b = [i]) :
    ((SignedOptionList.toList c = [i] ∧ SignedOptionList.toList d = [] ∧
    SignedOptionList.toList (FreeGroup.invRev e) = []) ∨
    (SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [i] ∧
    SignedOptionList.toList (FreeGroup.invRev e) = [])) ∧ h.length = 0:= by
  induction h with
  | single_cell h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all [PartialGrid.length]
    | sides i => simp_all
    | top_left i => simp_all [to_vertical_edge, SignedOptionList.toList, toList_invRev]
    | adjacent i k h => simp_all [to_vertical_edge, SignedOptionList.toList, toList_invRev]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all [toList_invRev, PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [SignedOptionList.toList_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := empty_empty g1 ha k_is
      simp_all [PartialGrid.length]
    simp_all only [SignedOptionList.toList_nil, true_and, List.ne_cons_self, false_and,
      and_false, or_false, forall_const, IsEmpty.forall_iff, List.append_nil,
      SignedOptionList.toList_append, List.cons_append, List.nil_append, List.cons.injEq]
    have H := empty_empty g2 g1_ih.1.2 n_is
    simp_all [PartialGrid.length]
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [SignedOptionList.toList_append] at hb
    rcases List.append_eq_singleton_iff.mp hb with
      ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := empty_empty g1 ha k_is
      have := g2_ih H.2.2.1 o_is
      rcases this.1 with h1 | h2
      · simp_all [PartialGrid.length]
      simp_all [PartialGrid.length]
    have hn : SignedOptionList.toList (FreeGroup.invRev n) = [] := by aesop
    have := empty_empty g2 hn o_is
    simp_all [PartialGrid.length]
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all [PartialGrid.length]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [FreeGroup.invRev_append, SignedOptionList.toList_append] at ha
    simp at ha
    rw [← toList_invRev_eq_nil_iff] at ha
    specialize g1_ih ha.1 hb
    nth_rewrite 2 [← toList_invRev_eq_nil_iff] at ha
    rcases g1_ih with h1 | h2
    · specialize g2_ih ha.2 h1.1
      rcases g2_ih with h3 | h4
      · simp_all [PartialGrid.length]
      simp_all [PartialGrid.length]
    have H := empty_empty g2 ha.2 h2.1
    simp_all [PartialGrid.length]

theorem empty_generator_pair (h : PartialGrid a b c d e)
    (h1 : SignedOptionList.toList (FreeGroup.invRev a) = [])
    (h2 : SignedOptionList.toList b = [i, j]) :
    ((SignedOptionList.toList c = [] ∧
      SignedOptionList.toList d = [i, j] ∧
      SignedOptionList.toList (FreeGroup.invRev e) = []) ∨
    (SignedOptionList.toList c = [i] ∧
      SignedOptionList.toList d = [j] ∧
      SignedOptionList.toList (FreeGroup.invRev e) = []) ∨
    (SignedOptionList.toList c = [i, j] ∧
      SignedOptionList.toList d = [] ∧ SignedOptionList.toList (FreeGroup.invRev e) = [])) ∧
    h.length = 0 := by
  change _ = [i] ++ [j] at h2
  rcases SignedOptionList.toList_eq_append h2 with ⟨a1, a2, ha⟩
  have ha1 : a1.length > 0 := by
    have H := SignedOptionList.toList_len a1
    aesop
  have ha2 : a2.length > 0 := by
    have H := SignedOptionList.toList_len a2
    aesop
  rcases PartialGrid.splittable_vertically h _ _ ha.1 ha1 ha2 with
    ⟨mid, d1, e1, d2, e2, i1, i2, ⟨long⟩, ⟨len⟩⟩ | H
  · have H := empty_generator i1 h1 ha.2.1
    have hmid : SignedOptionList.toList mid = [] := by aesop
    rw [← toList_invRev_eq_nil_iff] at hmid
    have H2 := empty_generator i2 hmid ha.2.2
    have hc : SignedOptionList.toList e = [] := by aesop
    simp [hc, and_true]
    have H : [i, j] = SignedOptionList.toList c ++ SignedOptionList.toList d := by
      apply congr_arg SignedOptionList.toList at long
      simp only [SignedOptionList.toList_append, List.append_assoc] at long
      rcases H with h3 | h4
      · rcases H2 with h5 | h6
        · simp only [h3, h5, List.append_nil, List.nil_append, List.cons_append] at long
          exact long.symm
        simp only [h3, h6, List.nil_append, List.cons_append] at long
        exact long.symm
      rcases H2 with h7 | h8
      · simp only [h4, h7, List.append_nil, List.cons_append, List.nil_append] at long
        exact long.symm
      simp only [h4, h8, List.nil_append, List.cons_append] at long
      exact long.symm
    match hc : SignedOptionList.toList c with
    | [] =>
      match hd : SignedOptionList.toList d with
      | [] => simp [hc, hd] at H
      | d1 :: d2 => aesop
    | c1 :: c2 =>
      match hd : SignedOptionList.toList d with
      | [] =>
        simp_all
      | d1 :: d2 =>
        constructor
        · right; left
          have hl := congr_arg List.length H
          rw [hc, hd] at hl
          simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.cons_append,
            List.length_append, Nat.reduceEqDiff] at hl
          have hc2 : c2.length = 0 := by omega
          aesop
        simp_all
  rcases H with ⟨c1, i1, ⟨d_is⟩, ⟨db_is⟩, ⟨d_is'⟩, ⟨a_is⟩⟩
  have := empty_generator i1 h1 ha.2.1
  aesop

theorem generator_empty (h : PartialGrid a b c d e)
    (h1 : SignedOptionList.toList (FreeGroup.invRev a) = [i])
    (h2 : SignedOptionList.toList (FreeGroup.invRev b) = []) :
    ((SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [i] ∧
      SignedOptionList.toList e = []) ∨
    (SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [] ∧
      SignedOptionList.toList e = [i])) ∧ h.length = 0 := by
  have h3 : SignedOptionList.toList (FreeGroup.invRev (FreeGroup.invRev b)) = [] := by
    rw [FreeGroup.invRev_invRev]
    exact toList_invRev_eq_nil_iff.mp h2
  have := empty_generator (reflect h).1 h3 h1
  simp [← (reflect h).2.1] at this
  aesop

theorem generator_pair_empty (h : PartialGrid a b c d e)
    (h1 : SignedOptionList.toList (FreeGroup.invRev a) = [j, i])
    (h2 : SignedOptionList.toList b = []) :
    ((SignedOptionList.toList c = [] ∧
      SignedOptionList.toList d = [i, j] ∧
      SignedOptionList.toList (FreeGroup.invRev e) = []) ∨
    (SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [i] ∧
      SignedOptionList.toList (FreeGroup.invRev e) = [j]) ∨
    (SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [] ∧
      SignedOptionList.toList (FreeGroup.invRev e)= [j, i])) ∧
    h.length = 0 := by
  have h3 : SignedOptionList.toList (FreeGroup.invRev (FreeGroup.invRev b)) = [] := by
    rw [FreeGroup.invRev_invRev]
    exact h2
  have := empty_generator_pair (reflect h).1 h3 h1
  simp [← (reflect h).2.1] at this
  aesop

theorem generator_generator_same (h : PartialGrid a b c d e)
  (h1 : SignedOptionList.toList (FreeGroup.invRev a) = [i])
  (h2 : SignedOptionList.toList b = [i]) :
  (SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [] ∧
    SignedOptionList.toList (FreeGroup.invRev e) = [] ∧ h.length = 1) ∨
  (SignedOptionList.toList c = [] ∧
    SignedOptionList.toList d = [i, i] ∧
    SignedOptionList.toList (FreeGroup.invRev e) = [] ∧ h.length = 0) := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [SignedOptionList.toList, PartialGrid.length]
    all_goals grind [Nat.dist]
  | empty a b ha ha1 hb hb => simp_all [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    simp only [PartialGrid.length]
    rw [SignedOptionList.toList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, _⟩ | ⟨k_is, n_is⟩
    · have H := generator_empty g1 h1 (toList_invRev_eq_nil_iff.mpr k_is)
      simp_all
    simp_all only [SignedOptionList.toList_nil, true_and, List.nil_eq, reduceCtorEq,
      false_and, and_false, or_false, forall_const, List.ne_cons_self, IsEmpty.forall_iff,
      List.append_nil, SignedOptionList.toList_append, List.nil_append]
    have H := empty_empty g2 g1_ih.2.1 n_is
    simp_all
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [SignedOptionList.toList_append] at h2
    simp only [PartialGrid.length]
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · rcases generator_empty g1 h1 (toList_invRev_eq_nil_iff.mpr k_is) with h3 | h4
      · have H2 := empty_generator g2 (toList_invRev_eq_nil_iff.mpr h3.2.2) o_is
        aesop
      aesop
    have n_is : SignedOptionList.toList n = [] := by aesop
    have H := empty_empty g2 (toList_invRev_eq_nil_iff.mpr n_is) o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    simp only [PartialGrid.length]
    rw [FreeGroup.invRev_append, SignedOptionList.toList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨j_is, n_is⟩ | ⟨j_is, n_is⟩
    · have H := empty_generator g1 j_is h2
      simp_all
    specialize g1_ih j_is h2
    have l_nil : SignedOptionList.toList l = [] := by aesop
    have H := empty_empty g2 n_is l_nil
    aesop
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    simp only [PartialGrid.length]
    rw [FreeGroup.invRev_append, SignedOptionList.toList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨j_is, o_is⟩ | ⟨j_is, o_is⟩
    · have H := empty_generator g1 j_is h2
      simp_all only [gt_iff_lt, List.ne_cons_self, forall_const, IsEmpty.forall_iff,
        List.append_assoc, SignedOptionList.toList_append, List.append_eq_nil_iff]
      rcases H with h3 | h4
      · aesop
      have := generator_empty g2 o_is (toList_invRev_eq_nil_iff.mpr h4.1)
      simp_all only [List.ne_cons_self, toList_invRev, List.reverse_eq_nil_iff, zero_ne_one, and_true,
        IsEmpty.forall_iff, List.nil_append, List.reverse_eq_cons_iff, List.reverse_nil, List.cons_ne_self, and_false,
        add_zero, and_self, false_or]
      obtain ⟨left, right_1⟩ := h4
      obtain ⟨left_1, right_2⟩ := this
      obtain ⟨left_2, right_1⟩ := right_1
      cases left_1 with
      | inl h_1 => simp_all only [List.nil_append, List.cons_append, and_self]
      | inr h_2 => simp_all only [List.cons_append, List.nil_append, and_self]
    specialize g1_ih j_is h2
    have l_nil : SignedOptionList.toList l = [] := by aesop
    have := empty_empty g2 o_is l_nil
    simp_all

theorem generator_generator_apart (h : PartialGrid a b c d e)
    (h1 : SignedOptionList.toList a = [i])
    (h2 : SignedOptionList.toList b = [j]) (hij : i.dist j > 1) :
    (SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [i, j] ∧
      SignedOptionList.toList e = [] ∧ h.length = 0) ∨
    (SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [j, i] ∧
      SignedOptionList.toList e = [] ∧ h.length = 1)  ∨
    (SignedOptionList.toList c = [] ∧ SignedOptionList.toList d = [j] ∧
      SignedOptionList.toList e = [i] ∧ h.length = 1) ∨
    (SignedOptionList.toList c = [j] ∧ SignedOptionList.toList d = [i] ∧
      SignedOptionList.toList e = [] ∧ h.length = 1) ∨
    (SignedOptionList.toList c = [j] ∧ SignedOptionList.toList d = [] ∧
      SignedOptionList.toList e = [i] ∧ h.length = 1) := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [SignedOptionList.toList, PartialGrid.length]
    all_goals grind [Nat.dist]
  | empty a b ha ha1 hb hb => simp_all [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [PartialGrid.length]
    rw [SignedOptionList.toList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := generator_empty g1 (toList_invRev_eq_singleton_iff.mpr h1)
        (toList_invRev_eq_nil_iff.mpr k_is)
      simp_all
    simp_all only [gt_iff_lt, SignedOptionList.toList_nil, List.nil_eq, reduceCtorEq,
      false_and, and_false, List.ne_cons_self, true_and, false_or, forall_const, IsEmpty.forall_iff,
      List.append_nil, SignedOptionList.toList_append, List.cons_append,
      List.nil_append, List.cons.injEq]
    have H := generator_empty g2 (toList_invRev_eq_singleton_iff.mpr g1_ih.2.1)
      (toList_invRev_eq_nil_iff.mpr n_is)
    simp_all
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [PartialGrid.length]
    rw [SignedOptionList.toList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := generator_empty g1 (toList_invRev_eq_singleton_iff.mpr h1)
        (toList_invRev_eq_nil_iff.mpr k_is)
      rcases H with h3 | h4
      · have H2 := empty_generator g2 (toList_invRev_eq_nil_iff.mpr h3.2.2) o_is
        aesop
      aesop
    simp_all only [gt_iff_lt, forall_const, List.ne_cons_self, IsEmpty.forall_iff, implies_true,
      List.append_nil, List.append_assoc, SignedOptionList.toList_append,
      List.append_eq_nil_iff]
    have n_is : SignedOptionList.toList n = [] ∨
      SignedOptionList.toList n = [i] := by aesop
    rcases n_is with hn | hn
    · have H := empty_empty g2 (toList_invRev_eq_nil_iff.mpr hn) o_is
      aesop
    have H := generator_empty g2 (toList_invRev_eq_singleton_iff.mpr hn)
      (toList_invRev_eq_nil_iff.mpr o_is)
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [PartialGrid.length]
    rw [SignedOptionList.toList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      rename_i j'
      have l_nil : SignedOptionList.toList l = [] ∨ SignedOptionList.toList l = [j']:= by aesop
      rcases l_nil with hl | hl
      · have H := empty_empty g2 (toList_invRev_eq_nil_iff.mpr n_is) hl
        aesop
      have H := empty_generator g2 (toList_invRev_eq_nil_iff.mpr n_is) hl
      aesop
    have H := empty_generator g1 (toList_invRev_eq_nil_iff.mpr j_is) h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [PartialGrid.length]
    rw [SignedOptionList.toList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · specialize g1_ih j_is h2
      rename_i j'
      have l_nil : SignedOptionList.toList l = [] ∨ SignedOptionList.toList l = [j']:= by aesop
      rcases l_nil with hl | hl
      · have H := empty_empty g2 (toList_invRev_eq_nil_iff.mpr o_is) hl
        aesop
      have H := empty_generator g2 (toList_invRev_eq_nil_iff.mpr o_is) hl
      aesop
    have H := empty_generator g1 (toList_invRev_eq_nil_iff.mpr j_is) h2
    simp_all only [gt_iff_lt, List.ne_cons_self, forall_const, IsEmpty.forall_iff, List.append_nil,
      List.append_assoc, SignedOptionList.toList_append, List.append_eq_nil_iff]
    rcases H with h3 | h4
    · aesop
    have H := generator_empty g2 (toList_invRev_eq_singleton_iff.mpr o_is)
      (toList_invRev_eq_nil_iff.mpr h4.1)
    aesop

theorem generator_generator_close
  (h : PartialGrid a b c d e) (h1 : SignedOptionList.toList a = [i])
  (h2 : SignedOptionList.toList b = [j]) (hij : i.dist j = 1) :
  (SignedOptionList.toList c = [] ∧
    SignedOptionList.toList d = [i, j] ∧
    SignedOptionList.toList e = [] ∧ h.length = 0) ∨
  (SignedOptionList.toList c = [] ∧
    SignedOptionList.toList d = [j, i, j, i] ∧
    SignedOptionList.toList e = [] ∧ h.length = 1)  ∨
  (SignedOptionList.toList c = [] ∧
    SignedOptionList.toList d = [j, i, j] ∧
    SignedOptionList.toList e = [i] ∧ h.length = 1) ∨
  (SignedOptionList.toList c = [] ∧
    SignedOptionList.toList d = [j, i] ∧
    SignedOptionList.toList e = [j, i] ∧ h.length = 1) ∨
  (SignedOptionList.toList c = [j] ∧
    SignedOptionList.toList d = [i, j, i] ∧
    SignedOptionList.toList e = [] ∧ h.length = 1) ∨
  (SignedOptionList.toList c = [j] ∧
    SignedOptionList.toList d = [i, j] ∧
    SignedOptionList.toList e = [i] ∧ h.length = 1) ∨
  (SignedOptionList.toList c = [j] ∧
    SignedOptionList.toList d = [i] ∧
    SignedOptionList.toList e = [j, i] ∧ h.length = 1) ∨
  (SignedOptionList.toList c = [j, i] ∧
    SignedOptionList.toList d = [j, i] ∧
    SignedOptionList.toList e = [] ∧ h.length = 1) ∨
  (SignedOptionList.toList c = [j, i] ∧
    SignedOptionList.toList d = [j] ∧
    SignedOptionList.toList e = [i] ∧ h.length = 1) ∨
  (SignedOptionList.toList c = [j, i] ∧
    SignedOptionList.toList d = [] ∧
    SignedOptionList.toList e = [j, i] ∧ h.length = 1) := by
  induction h with
  | single_cell h =>
    cases h
    all_goals simp_all [SignedOptionList.toList, PartialGrid.length]
    all_goals grind [Nat.dist]
  | empty a b ha ha1 hb hb => simp_all [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [PartialGrid.length]
    rw [SignedOptionList.toList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := generator_empty g1 (toList_invRev_eq_singleton_iff.mpr h1)
        (toList_invRev_eq_nil_iff.mpr k_is)
      simp_all
    simp_all only [SignedOptionList.toList_nil, List.nil_eq, reduceCtorEq, false_and,
      and_false, List.ne_cons_self, true_and, false_or, forall_const, List.cons_ne_self,
      IsEmpty.forall_iff, List.append_nil, SignedOptionList.toList_append, List.cons_append,
      List.nil_append, List.cons.injEq]
    have H := generator_pair_empty g2 (toList_invRev_eq_pair_iff.mpr g1_ih.2.1) n_is
    rcases H with h1 | h2 | h3
    · aesop
    · simp_all
    aesop
  | horizontal_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [PartialGrid.length]
    rw [SignedOptionList.toList_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := generator_empty g1 (toList_invRev_eq_singleton_iff.mpr h1)
        (toList_invRev_eq_nil_iff.mpr k_is)
      rcases H with h3 | h4
      · have H2 := empty_generator g2 (toList_invRev_eq_nil_iff.mpr h3.2.2) o_is
        aesop
      aesop
    simp_all only [gt_iff_lt, forall_const, List.ne_cons_self, IsEmpty.forall_iff, implies_true,
      List.append_nil, List.append_assoc, SignedOptionList.toList_append,
      List.append_eq_nil_iff]
    rename_i j'
    have H : SignedOptionList.toList n = [] ∨ SignedOptionList.toList n = [i] ∨
      SignedOptionList.toList n = [j', i] := by aesop
    rcases H with h3 | h4 | h5
    · have H := empty_empty g2 (toList_invRev_eq_nil_iff.mpr h3) o_is
      aesop
    · have H := generator_empty g2 (toList_invRev_eq_singleton_iff.mpr h4)
        (toList_invRev_eq_nil_iff.mpr o_is)
      aesop
    have H := generator_pair_empty g2 (toList_invRev_eq_pair_iff.mpr h5) o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [PartialGrid.length]
    rw [SignedOptionList.toList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      simp_all only [List.ne_cons_self, IsEmpty.forall_iff, List.nil_append,
        SignedOptionList.toList_nil, List.nil_eq, reduceCtorEq, false_and, and_false,
        true_and, false_or, SignedOptionList.toList_append, List.append_eq_nil_iff,
        List.append_left_eq_self]
      have H := empty_generator_pair g2 (toList_invRev_eq_nil_iff.mpr n_is) g1_ih.1
      aesop
    have H := empty_generator g1 (toList_invRev_eq_nil_iff.mpr j_is) h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i k l m n o p q r s
    rw [PartialGrid.length]
    rw [SignedOptionList.toList_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨p_is, k_is⟩ | ⟨p_is, k_is⟩
    · specialize g1_ih k_is h2
      have H : SignedOptionList.toList m = [] ∨
          SignedOptionList.toList m = [j] ∨
          SignedOptionList.toList m = [j, i] := by grind
      rcases H with h1 | h1 | h1
      · have H := empty_empty g2 (toList_invRev_eq_nil_iff.mpr p_is) h1
        simp only [H.1, true_and, SignedOptionList.toList_append, H.2.1, List.nil_append]
        simp only [h1, true_and] at g1_ih
        aesop
      · have H := empty_generator g2 (toList_invRev_eq_nil_iff.mpr p_is) h1
        aesop
      have H := empty_generator_pair g2 (toList_invRev_eq_nil_iff.mpr p_is) h1
      aesop
    have H := empty_generator g1 (toList_invRev_eq_nil_iff.mpr k_is) h2
    simp_all only [gt_iff_lt, List.ne_cons_self, forall_const, IsEmpty.forall_iff, List.append_nil,
      List.append_assoc, SignedOptionList.toList_append, List.append_eq_nil_iff]
    rcases H with h1 | h1
    · simp_all only [forall_const, List.append_nil, and_true]
      aesop
    simp_all only [List.ne_cons_self, IsEmpty.forall_iff,  and_false, List.cons_ne_self]
    have H := generator_empty g2 (toList_invRev_eq_singleton_iff.mpr p_is)
      (toList_invRev_eq_nil_iff.mpr h1.1)
    aesop

end FrontierPossibilitiesEpsilonRemovedBoolRemoved

end PartialGrid

end Braid
