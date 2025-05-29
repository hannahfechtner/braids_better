import BraidProject.PartialGrid_split
set_option maxHeartbeats 1000000

def to_up_plain (a : List ℕ) : List (ℕ × Bool) := List.map (fun x => (x, false)) a.reverse

def to_over_plain (a : List ℕ) : List (ℕ × Bool) := List.map (fun x => (x, true)) a

theorem remove_up_is_plain : remove_ones (to_up i) = to_up_plain i := by
  induction i with
  | nil => rfl
  | cons head tail ih =>
    match tail with
    | [] =>
      simp [remove_ones, to_up_plain]
    | t1 :: t2 =>
      have H1 : (to_up (head :: t1 :: t2)) = (to_up (t1 :: t2)) ++ [(some head, false)] := by
        simp [to_up]
      rw [H1, remove_ones_append, ih]
      simp [to_up_plain, remove_ones]

theorem eq_remover_of_remove_ones_eq_to_over_plain (h : remove_ones b = to_over_plain j) : j = remover b := by
  induction b generalizing j with
  | nil =>
    simp [remove_ones, to_over_plain] at h
    simp [h, remover]
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [remove_ones] at h
      simp [remover]
      exact ih h
    | (some a, _) =>
      simp [remove_ones] at h
      simp [remover]
      match j with
      | [] => simp [to_over_plain] at h
      | j1 :: j2 =>
        simp [to_over_plain] at h
        unfold to_over_plain at ih
        specialize ih h.2
        aesop

theorem remove_ones_eq_to_over_plain_of_eq_remover (h  : j = remover b) (hb : is_true b) :
    remove_ones b = to_over_plain j := by
  induction b generalizing j with
  | nil =>
    simp [remover] at h
    simp [remove_ones, to_over_plain]
    exact h
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [remove_ones]
      simp [remover] at h
      apply ih h
      exact (is_true_split hb).2
    | (some a, true) =>
      simp [remove_ones]
      simp [remover] at h
      match j with
      | [] => simp [to_over_plain] at h
      | j1 :: j2 =>
        simp [to_over_plain] at h
        unfold to_over_plain at ih
        specialize ih h.2
        rw [ih]
        simp [to_over_plain]
        aesop
        exact (is_true_split hb).2
    | (some a, false) =>
      specialize hb (some a, false) ⟨by simp⟩
      simp at hb
      exact hb.1.elim

theorem to_over_plain_remover_eq_remove_ones(h : is_true b) : to_over_plain (remover b) = remove_ones b := by
  induction b with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [to_over_plain, remove_ones, ← ih (is_true_split h).2, remover]
    | (some a, true) =>
      simp [to_over_plain, remove_ones, ← ih (is_true_split h).2, remover]
    | (some a, false) =>
      have H := (is_true_split h).1 (some a, false) ⟨by simp⟩
      simp at H
      exact H.1.elim

theorem to_up_plain_remover_rev_eq_remove_ones (h : is_false a) : to_up_plain (remover a.reverse) = remove_ones a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [to_up_plain, remove_ones, ← ih (is_false_split h).2, remover_append, remover]
    | (some a, true) =>
      have H := (is_false_split h).1 (some a, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    | (some a, false) =>
      simp [to_up_plain, remove_ones, ← ih (is_false_split h).2, remover_append, remover]

theorem to_up_plain_inj (h : to_up_plain a = to_up_plain b) : a = b := by
  simp [to_up_plain] at h
  exact (List.map_inj_right (by simp)).mp h

theorem to_over_plain_inj (h : to_over_plain a = to_over_plain b) : a = b := by
  simp [to_over_plain] at h
  exact (List.map_inj_right (by simp)).mp h

theorem helper_pg_empty (h : PartialGrid a b c d e) : remove_ones a = [] → remove_ones b =  [] →
    remove_ones c = [] ∧ remove_ones e = [] ∧ h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length, remove_ones]
    | top_bottom i => simp [PartialGrid.length, remove_ones]
    | sides i => simp [PartialGrid.length, remove_ones]
    | top_left i =>
      intro ha
      simp [remove_ones, to_up] at ha
    | adjacent i k h =>
      intro ha
      simp [remove_ones, to_up] at ha
    | separated i j h =>
      intro ha
      simp [remove_ones, to_up] at ha
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i f g h i j k l m
    intro f_is gj_is
    rw [remove_ones_append] at gj_is
    apply List.append_eq_nil_iff.mp at gj_is
    specialize g1_ih f_is gj_is.1
    specialize g2_ih g1_ih.2.1 gj_is.2
    rw [remove_ones_append, PartialGrid.length]
    aesop
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i f g i j k l m n o
    intro f_is gl_is
    rw [remove_ones_append] at gl_is
    apply List.append_eq_nil_iff.mp at gl_is
    specialize g1_ih f_is gl_is.1
    specialize g2_ih g1_ih.2.1 gl_is.2
    rw [PartialGrid.length]
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i f g h i j k l m
    intro jf_is g_is
    rw [remove_ones_append] at jf_is
    apply List.append_eq_nil_iff.mp at jf_is
    specialize g1_ih jf_is.2 g_is
    specialize g2_ih jf_is.1 g1_ih.1
    rw [remove_ones_append, PartialGrid.length]
    aesop
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i f g i j k l m n o
    intro lf_is g_is
    rw [remove_ones_append] at lf_is
    apply List.append_eq_nil_iff.mp at lf_is
    specialize g1_ih lf_is.2 g_is
    specialize g2_ih lf_is.1 g1_ih.1
    rw [PartialGrid.length]
    aesop

theorem empty_rm_pg_len (h : PartialGrid a b c d e) : remove_ones a = [] → remove_ones b =  [] →
    h.length = 0 := by
  have H := helper_pg_empty h
  aesop

theorem to_up_len : (to_up a).length > 0 := by
  match a with
  | [] => simp [to_up]
  | a1 :: a2 => simp [to_up]

theorem to_over_len : (to_over b).length > 0 := by
  match b with
  | [] => simp [to_over]
  | b1 :: b2 => simp [to_over]

theorem to_up_plain_append : to_up_plain (a ++ b) = to_up_plain b ++ to_up_plain a := by simp [to_up_plain]
theorem to_over_plain_append : to_over_plain (a ++ b) = to_over_plain a ++ to_over_plain b := by simp [to_over_plain]
theorem remove_ones_len(a : List (Option α × Bool))  : (remove_ones a).length ≤ a.length := by
  induction a with
  | nil => simp [remove_ones]
  | cons head tail ih =>
    match head with
    | (none, _) =>
      simp [remove_ones] at ih
      simp [remove_ones, ih]
      omega
    | (some a, true) =>
      simp [remove_ones] at ih
      simp [remove_ones, ih]
    | (some a, false) =>
      simp [remove_ones] at ih
      simp [remove_ones, ih]

theorem remove_ones_eq_append (h : remove_ones a = b ++ c) :
    ∃ a1 a2, a=a1++a2 ∧ remove_ones a1 = b ∧ remove_ones a2 = c := by
  induction a generalizing b c with
  | nil =>
    simp [remove_ones] at h
    aesop
  | cons head tail ih =>
    match head with
    | (none, b) =>
      simp [remove_ones] at h
      specialize ih h
      rcases ih with ⟨a1, a2, a_is, b_is, c_is⟩
      use (none, b) :: a1, a2
      simp_all [remove_ones]
    | (some d, e) =>
      match b with
      | [] =>
        match c with
        | [] => aesop
        | c1 :: c2 =>
          simp [remove_ones] at h
          use [], (some d, e) :: tail
          aesop
      | b1 :: b2 =>
        simp [remove_ones] at h
        match b2 with
        | [] =>
          use [(some d, e)], tail
          simp_all [remove_ones]
        | b21 :: b22 =>
          specialize ih h.2
          rcases ih with ⟨a1, a2, a_is, b_is, c_is⟩
          use (some d, e) :: a1, a2
          simp_all [remove_ones]

theorem remove_ones_eq_to_up_plain_prod (h : remove_ones a = to_up_plain (m ++ q)) :
   m = [] ∨ q = [] ∨ ∃ a1 a2, a1.length > 0 ∧ a2.length > 0 ∧
        a = a1 ++ a2 ∧ remove_ones a1 = to_up_plain q ∧ remove_ones a2 = to_up_plain m  := by
  induction m generalizing a q with
  | nil => exact Or.inl rfl
  | cons m1 m2 ih =>
    right
    match q with
    | [] => exact Or.inl rfl
    | q1 :: q2 =>
      right
      rw [to_up_plain_append] at h
      rcases remove_ones_eq_append h with ⟨a1, a2, a_is, a1s, a2s⟩
      use a1, a2
      have a1l := remove_ones_len a1
      have a2l := remove_ones_len a2
      have a1le := congr_arg List.length a1s
      have a2le := congr_arg List.length a2s
      simp [to_up_plain] at a1le
      simp [to_up_plain] at a2le
      have a1_len : a1.length > 0 := by
        omega
      have a2_len : a2.length > 0 := by omega
      aesop

theorem List.suffix_of_append {a b c : List α} (h : a <:+ b ++ c) : a <:+ c ∨ ∃ a1, a1.length > 0 ∧
     a = a1 ++ c ∧ a1 <:+ b := by
  rcases h with ⟨r, hr⟩
  rcases List.append_eq_append_iff.mp hr with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · match tm with
    | [] => aesop
    | t1 :: t2 =>
      right
      use t1 :: t2
      constructor
      · simp
      constructor
      · exact s2
      simp [s1]
  match fm with
  | [] => aesop
  | f1 :: f2 =>
    left
    rw [s2]
    exact suffix_append ([f1] ++ f2) a

theorem helper_bajillion (ha : remove_ones a <:+ to_up_plain q ++ to_up_plain (m1 :: m2)) :
    remove_ones a <:+ to_up_plain (m1 :: m2) ∨
    ∃ a1 a2, a1.length > 0 ∧ a = a1 ++ a2 ∧ remove_ones a2 = to_up_plain (m1 :: m2) ∧ remove_ones a1 <:+ to_up_plain q := by
  rcases List.suffix_of_append ha with one | two
  · left
    exact one
  rcases two with ⟨a1, a1_len, a_is, a1_suff⟩
  right
  rcases remove_ones_eq_append a_is with ⟨a3, a4, a_is, a3a1, m4⟩
  use a3, a4
  constructor
  · have H := remove_ones_len a3
    rw [a3a1] at H
    omega
  constructor
  · assumption
  constructor
  · exact m4
  rw [a3a1]
  assumption

theorem frontier_options_from_vertical (h1 : PartialGrid a b mid d2 e2)
    (i1 : PartialGrid a2 b mid4 e5 d5) (i2 : PartialGrid a1 mid4 mid d4 e4)
    (hf : d4 ++ e4 ++ e5 ++ d5 = d2 ++ e2) :
    (d2 = d4 ++ e4 ++ e5 ∧ d5 = e2) ∨ (d2 = d4 ∧ e5 = [] ∧ e2 = e4 ++ d5) := by
  rcases middle_frontier_nil_or_caps i1 with ⟨⟨e5_nil⟩⟩ | ⟨fronte5, mide5, caboosee5, ⟨spece5⟩⟩
  · right
    rw [e5_nil, List.append_nil] at hf
    rcases middle_frontier_nil_or_caps h1 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, middled2, caboosed2, ⟨specd2⟩⟩
    · rw [d2_nil, List.nil_append] at hf
      rcases middle_frontier_nil_or_caps i2 with ⟨⟨d4_nil⟩⟩ | ⟨frontd4, middled4, caboosed4, ⟨specd4⟩⟩
      · rw [d4_nil, List.nil_append] at hf
        aesop
      rw [specd4] at hf
      have H : is_false e2 := h1.right_frontier_is_false
      rw [← hf] at H
      specialize H (caboosed4, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    rw [specd2] at hf
    have H : is_false (e4 ++ d5) := by
        apply is_false_of_false_false
        · exact i2.right_frontier_is_false
        exact i1.right_frontier_is_false
    rcases middle_frontier_nil_or_caps i2 with ⟨⟨d4_nil⟩⟩ | ⟨frontd4, middled4, caboosed4, ⟨specd4⟩⟩
    · rw [d4_nil, List.nil_append] at hf
      rw [hf] at H
      specialize H (caboosed2, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
    rw [specd4] at hf
    simp at hf
    have to_split : (middled4 ++ [(caboosed4, true)]) ++ (e4 ++ d5) =
        (middled2 ++ [(caboosed2, true)]) ++ e2 := by
      simp [hf.2]
    rcases List.append_eq_append_iff.mp to_split with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
    · cases tm using List.reverseRecOn with
      | nil => aesop
      | append_singleton t1 t2 =>
        exfalso
        rw [← List.append_assoc] at s1
        have t2_is : t2 = (caboosed2, true) := by
          apply congr_arg List.getLast? at s1
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
          exact s1.symm
        rw [s2, t2_is] at H
        specialize H (caboosed2, true) ⟨by simp⟩
        simp at H
        exact H.1.elim
    cases fm using List.reverseRecOn with
    | nil => aesop
    | append_singleton f1 f2 =>
      exfalso
      have H : is_false e2 := h1.right_frontier_is_false
      rw [s2] at H
      have f2_is : f2 = (caboosed4, true) := by
        apply congr_arg List.getLast? at s1
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
        exact s1.symm
      rw [f2_is] at H
      specialize H (caboosed4, true) ⟨by simp⟩
      simp at H
      exact H.1.elim
  left
  rw [spece5] at hf
  rcases List.append_eq_append_iff.mp hf with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · cases tm using List.reverseRecOn with
    | nil => aesop
    | append_singleton t1 t2 =>
      exfalso
      rcases middle_frontier_nil_or_caps h1 with ⟨⟨d2_nil⟩⟩ | ⟨frontd2, midd2, caboosed2, ⟨specd2⟩⟩
      · simp [d2_nil] at s1
      rw [specd2] at s1
      have H : t2 = (caboosed2, true) := by
        apply congr_arg List.getLast? at s1
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
        exact s1.symm
      have H1 : is_false d5 := i1.right_frontier_is_false
      rw [s2, H] at H1
      specialize H1 (caboosed2, true) ⟨by simp⟩
      simp at H1
      exact H1.1.elim
  cases fm using List.reverseRecOn with
  | nil => aesop
  | append_singleton f1 f2 =>
    have H : f2 = (caboosee5, true) := by
      apply congr_arg List.getLast? at s1
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at s1
      exact s1.symm
    have H1 : is_false e2 := by exact h1.right_frontier_is_false
    rw [s2, H] at H1
    specialize H1 (caboosee5, true) ⟨by simp⟩
    simp at H1
    exact H1.1.elim

theorem partial_grid_rm_empty_helper (h : PartialGrid a b c d e) : remove_ones a = [] → remove_ones b = [] →
    (remove_ones c = [] ∧ remove_ones d = [] ∧ remove_ones e = []) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all
    | sides i => simp_all
    | top_left i => simp_all [to_up, remove_ones]
    | adjacent i k h => simp_all [to_up, remove_ones]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih => simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all
  | vertical_append g1 g2 h g1_ih g2_ih => simp_all

theorem partial_grid_rm_top_helper (h : PartialGrid a b c d e) : remove_ones a = [] → remove_ones b = [(i, true)] →
    (remove_ones c = [(i, true)] ∧ remove_ones d = [] ∧ remove_ones e = []) ∨
    (remove_ones c = [] ∧ remove_ones d = [(i, true)] ∧ remove_ones e = []) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp_all
    | top_bottom i => simp_all
    | sides i => simp_all
    | top_left i => simp_all [to_up, remove_ones]
    | adjacent i k h => simp_all [to_up, remove_ones]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    intro j_is kn_is
    rw [remove_ones_append] at kn_is
    rcases List.append_eq_singleton_iff.mp kn_is with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_empty_helper g1 j_is k_is
      simp_all
    simp_all only [remove_ones_nil, true_and, List.ne_cons_self, false_and, and_false, or_false,
      forall_const, IsEmpty.forall_iff, imp_self, List.append_nil, remove_ones_append,
      List.cons_append, List.nil_append, List.cons.injEq]
    have H := partial_grid_rm_empty_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    intro j_is ko_is
    rw [remove_ones_append] at ko_is
    rcases List.append_eq_singleton_iff.mp ko_is with
      ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_empty_helper g1 j_is k_is
      simp_all
      rcases g2_ih with h1 | h2
      · simp_all
      simp_all
    have hn : remove_ones n = [] := by aesop
    have H := partial_grid_rm_empty_helper g2 hn o_is
    simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih => simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    intro oj_is k_is
    rw [remove_ones_append] at oj_is
    simp at oj_is
    specialize g1_ih oj_is.2 k_is
    rcases g1_ih with h1 | h2
    · specialize g2_ih oj_is.1 h1.1
      rcases g2_ih with h3 | h4
      · simp_all
      simp_all
    have H := partial_grid_rm_empty_helper g2 oj_is.1 h2.1
    simp_all

theorem partial_grid_rm_top_helper_w (h : PartialGrid a b c d e)
    (h1 : remove_ones b = [(i, true), (j, true)]) (h2 : remove_ones a = []) :
    (remove_ones c = [] ∧ remove_ones d = [(i, true), (j, true)] ∧ remove_ones e = []) ∨
    (remove_ones c = [(i, true)] ∧ remove_ones d = [(j, true)] ∧ remove_ones e = []) ∨
    (remove_ones c = [(i, true), (j, true)] ∧ remove_ones d = [] ∧ remove_ones e = []) := by
  change _ = [(i, true)] ++ [(j, true)] at h1
  rcases remove_ones_eq_append h1 with ⟨a1, a2, ha⟩
  have ha1 : a1.length > 0 := by
    have H := remove_ones_len a1
    aesop
  have ha2 : a2.length > 0 := by
    have H := remove_ones_len a2
    aesop
  rcases splittable_vertically_of_pg' h _ _ ha.1 ha1 ha2 with
    ⟨mid, d1, e1, d2, e2, i1, i2, ⟨long⟩, len⟩ | baaad
  · have H := partial_grid_rm_top_helper i1 h2 ha.2.1
    have hmid : remove_ones mid = [] := by aesop
    have H2 := partial_grid_rm_top_helper i2 hmid ha.2.2
    have hc : remove_ones e = [] := by aesop
    simp [hc]
    have H : [(i, true), (j, true)] = remove_ones c ++ remove_ones d := by
      apply congr_arg remove_ones at long
      simp at long
      rcases H with h3 | h4
      · rcases H2 with h5 | h6
        · simp [h3, h5] at long
          exact long.symm
        simp [h3, h6] at long
        exact long.symm
      rcases H2 with h7 | h8
      · simp [h4, h7] at long
        exact long.symm
      simp [h4, h8] at long
      exact long.symm
    match hc : remove_ones c with
    | [] =>
      match hd : remove_ones d with
      | [] => simp [hc, hd] at H
      | d1 :: d2 => aesop
    | c1 :: c2 =>
      match hd : remove_ones d with
      | [] =>
        simp_all
      | d1 :: d2 =>
        right; left
        have hl := congr_arg List.length H
        rw [hc, hd] at hl
        simp at hl
        have hc2 : c2.length = 0 := by omega
        aesop
  rcases baaad with ⟨db, c1, i1, ⟨d_is⟩, ⟨db_is⟩, ⟨d_is'⟩, ⟨a_is⟩⟩
  have H := partial_grid_rm_top_helper i1 h2 ha.2.1
  aesop

theorem partial_grid_rm_side_helper (h : PartialGrid a b c d e)
    (h1 : remove_ones a = [(i, false)]) (h2 : remove_ones b = []) :
    (remove_ones c = [] ∧ remove_ones d = [(i, false)] ∧ remove_ones e = []) ∨
    (remove_ones c = [] ∧ remove_ones d = [] ∧ remove_ones e = [(i, false)]) := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp_all [remove_ones]
    | top_bottom i => simp_all [remove_ones]
    | sides i => simp_all [remove_ones]
    | top_left i => simp_all [to_up, remove_ones]
    | adjacent i k h => simp_all [to_up, remove_ones]
    | separated i j h => simp_all
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih => simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    simp [remove_ones_append] at h2
    simp_all
    rcases g1_ih with h3 | h4
    · simp_all
      have H := partial_grid_rm_empty_helper g2 h3.2.2 h2.2
      simp_all
    simp_all
    rcases g2_ih with h5 | h6
    · simp_all
    simp_all
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · simp_all
      have H := partial_grid_rm_empty_helper g2 n_is g1_ih.1
      simp_all
    have H := partial_grid_rm_empty_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · simp_all
      have l_is : remove_ones l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 o_is l_is
      simp_all
    have H := partial_grid_rm_empty_helper g1 j_is h2
    simp_all
    rcases g2_ih with h3 | h4
    · simp_all
    simp_all

theorem partial_grid_rm_side_helper_w (h : PartialGrid a b c d e)
    (h1 : remove_ones a = [(i, false), (j, false)]) (h2 : remove_ones b = []) :
    (remove_ones c = [] ∧ remove_ones d = [(i, false), (j, false)] ∧ remove_ones e = []) ∨
    (remove_ones c = [] ∧ remove_ones d = [(i, false)] ∧ remove_ones e = [(j, false)]) ∨
    (remove_ones c = [] ∧ remove_ones d = [] ∧ remove_ones e = [(i, false), (j, false)]) := by
  change _ = [(i, false)] ++ [(j, false)] at h1
  rcases remove_ones_eq_append h1 with ⟨a1, a2, ha⟩
  have ha1 : a1.length > 0 := by
    have H := remove_ones_len a1
    aesop
  have ha2 : a2.length > 0 := by
    have H := remove_ones_len a2
    aesop
  rcases splittable_horizontally_of_pg h _ _ ha.1 ha2 ha1 with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨long⟩, len⟩ | baaad
  · have H := partial_grid_rm_side_helper i1 ha.2.2 h2
    have hmid : remove_ones mid = [] := by aesop
    have H2 := partial_grid_rm_side_helper i2 ha.2.1 hmid
    have hc : remove_ones c = [] := by aesop
    simp [hc]
    have H : [(i, false), (j, false)] = remove_ones d ++ remove_ones e := by
      apply congr_arg remove_ones at long
      simp at long
      rcases H with h3 | h4
      · rcases H2 with h5 | h6
        · simp [h3, h5] at long
          exact long
        simp [h3, h6] at long
        exact long
      rcases H2 with h7 | h8
      · simp [h4, h7] at long
        exact long
      simp [h4, h8] at long
      exact long
    match hd : remove_ones d with
    | [] => aesop
    | d1 :: d2 =>
      match he :remove_ones e with
      | [] => aesop
      | e1 :: e2 =>
        rcases List.append_eq_len_two (by simp [hd]) (by simp [he]) H.symm
        aesop
  rcases baaad with ⟨db, c1, drest, i1, ⟨d_is⟩, ⟨db_is⟩, ⟨c_nil⟩, len⟩
  have H := partial_grid_rm_side_helper i1 ha.2.2 h2
  aesop

theorem partial_grid_rm_top_left_helper (h : PartialGrid a b c d e) (h1 : remove_ones a = [(i, false)])
  (h2 : remove_ones b = [(i, true)]) : (remove_ones c = [] ∧ remove_ones d = [] ∧ remove_ones e = []) ∨
  (remove_ones c = [] ∧ remove_ones d = [(i, false), (i, true)] ∧ remove_ones e = []) := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [remove_ones]
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_empty_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    have n_is : remove_ones n = [] := by aesop
    have H := partial_grid_rm_empty_helper g2 n_is o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : remove_ones l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 n_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · specialize g1_ih j_is h2
      have l_nil : remove_ones l = [] := by aesop
      have H := partial_grid_rm_empty_helper g2 o_is l_nil
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
    rcases H with h3 | h4
    · aesop
    have H := partial_grid_rm_side_helper g2 o_is h4.1
    aesop

theorem partial_grid_rm_adjacent_helper (h : PartialGrid a b c d e) (h1 : remove_ones a = [(i, false)])
  (h2 : remove_ones b = [(j, true)]) (hij : i.dist j = 1): (remove_ones c = [] ∧ remove_ones d = [(i, false), (j, true)] ∧ remove_ones e = []) ∨
  (remove_ones c = [] ∧ remove_ones d = [(j, true), (i, true), (j, false), (i, false)] ∧ remove_ones e = [])  ∨
  (remove_ones c = [] ∧ remove_ones d = [(j, true), (i, true), (j, false)] ∧ remove_ones e = [(i, false)]) ∨
  (remove_ones c = [] ∧ remove_ones d = [(j, true), (i, true)] ∧ remove_ones e = [(j, false), (i, false)]) ∨
  (remove_ones c = [(j, true)] ∧ remove_ones d = [(i, true), (j, false), (i, false)] ∧ remove_ones e = []) ∨
  (remove_ones c = [(j, true)] ∧ remove_ones d = [(i, true), (j, false)] ∧ remove_ones e = [(i, false)]) ∨
  (remove_ones c = [(j, true)] ∧ remove_ones d = [(i, true)] ∧ remove_ones e = [(j, false), (i, false)]) ∨
  (remove_ones c = [(j, true), (i, true)] ∧ remove_ones d = [(j, false), (i, false)] ∧ remove_ones e = []) ∨
  (remove_ones c = [(j, true), (i, true)] ∧ remove_ones d = [(j, false)] ∧ remove_ones e = [(i, false)]) ∨
  (remove_ones c = [(j, true), (i, true)] ∧ remove_ones d = [] ∧ remove_ones e = [(j, false), (i, false)]) := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [remove_ones]
    rename_i h
    apply or_dist_iff.mpr at h
    aesop
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_side_helper_w g2 g1_ih.2 n_is
    rcases H with h1 | h2 | h3
    · aesop
    · simp_all
    aesop
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    simp_all
    rename_i j'
    have H : remove_ones n = [] ∨ remove_ones n = [(i, false)] ∨
      remove_ones n = [(j', false), (i, false)] := by aesop
    rcases H with h3 | h4 | h5
    · have H := partial_grid_rm_empty_helper g2 h3 o_is
      aesop
    · have H := partial_grid_rm_side_helper g2 h4 o_is
      aesop
    have H := partial_grid_rm_side_helper_w g2 h5 o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      simp_all
      have H := partial_grid_rm_top_helper_w g2 g1_ih.1 n_is
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i k l m n o p q r s
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨p_is, k_is⟩ | ⟨p_is, k_is⟩
    · specialize g1_ih k_is h2
      have H : remove_ones m = [] ∨ remove_ones m = [(j, true)] ∨ remove_ones m = [(j, true), (i, true)] := by
        rcases g1_ih with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
        any_goals apply Or.inl h1.1
        any_goals apply Or.inr (Or.inl h1.1)
        any_goals apply Or.inr (Or.inr h1.1)
      rcases H with h1 | h1 | h1
      · have H := partial_grid_rm_empty_helper g2 p_is h1
        simp only [H.1, true_and, remove_ones_append, H.2.1, H.2.2, List.nil_append]
        simp only [h1, true_and] at g1_ih
        aesop
      · have H := partial_grid_rm_top_helper g2 p_is h1
        aesop
      have H := partial_grid_rm_top_helper_w g2 h1 p_is
      aesop
    have H := partial_grid_rm_top_helper g1 k_is h2
    simp_all
    rcases H with h1 | h1
    · simp_all
      aesop
    simp_all
    have H := partial_grid_rm_side_helper g2 p_is h1.1
    aesop

theorem partial_grid_rm_separated_helper (h : PartialGrid a b c d e) (h1 : remove_ones a = [(i, false)])
    (h2 : remove_ones b = [(j, true)]) (hij : i.dist j > 1): (remove_ones c = [] ∧ remove_ones d = [(i, false), (j, true)] ∧ remove_ones e = []) ∨
    (remove_ones c = [] ∧ remove_ones d = [(j, true), (i, false)] ∧ remove_ones e = [])  ∨
    (remove_ones c = [] ∧ remove_ones d = [(j, true)] ∧ remove_ones e = [(i, false)]) ∨
    (remove_ones c = [(j, true)] ∧ remove_ones d = [(i, false)] ∧ remove_ones e = []) ∨
    (remove_ones c = [(j, true)] ∧ remove_ones d = [] ∧ remove_ones e = [(i, false)]) := by
  induction h with
  | single_gridt h =>
    cases h
    all_goals simp_all [remove_ones]
  | empty a b ha ha1 hb hb => simp_all
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, n_is⟩ | ⟨k_is, n_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      simp_all
    simp_all
    have H := partial_grid_rm_side_helper g2 g1_ih.2 n_is
    simp_all
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h2
    rcases List.append_eq_singleton_iff.mp h2 with ⟨k_is, o_is⟩ | ⟨k_is, o_is⟩
    · have H := partial_grid_rm_side_helper g1 h1 k_is
      rcases H with h3 | h4
      · have H2 := partial_grid_rm_top_helper g2 h3.2.2 o_is
        aesop
      aesop
    simp_all
    have n_is : remove_ones n = [] ∨ remove_ones n = [(i, false)] := by aesop
    rcases n_is with hn | hn
    · have H := partial_grid_rm_empty_helper g2 hn o_is
      aesop
    have H := partial_grid_rm_side_helper g2 hn o_is
    aesop
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i j k l m n o p q
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨n_is, j_is⟩ | ⟨n_is, j_is⟩
    · specialize g1_ih j_is h2
      rename_i j'
      have l_nil : remove_ones l = [] ∨ remove_ones l = [(j', true)]:= by aesop
      rcases l_nil with hl | hl
      · have H := partial_grid_rm_empty_helper g2 n_is hl
        aesop
      have H := partial_grid_rm_top_helper g2 n_is hl
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i j k l m n o p q r
    rw [remove_ones_append] at h1
    rcases List.append_eq_singleton_iff.mp h1 with ⟨o_is, j_is⟩ | ⟨o_is, j_is⟩
    · specialize g1_ih j_is h2
      rename_i j'
      have l_nil : remove_ones l = [] ∨ remove_ones l = [(j', true)]:= by aesop
      rcases l_nil with hl | hl
      · have H := partial_grid_rm_empty_helper g2 o_is hl
        aesop
      have H := partial_grid_rm_top_helper g2 o_is hl
      aesop
    have H := partial_grid_rm_top_helper g1 j_is h2
    simp_all
    rcases H with h3 | h4
    · aesop
    have H := partial_grid_rm_side_helper g2 o_is h4.1
    aesop

theorem suffix_of_singleton (h : l <:+ [a]) : l = [] ∨ l = [a] := by
  rcases h with ⟨r, hr⟩
  match r with
  | [] => aesop
  | r1 :: r2 => aesop

theorem prefix_of_singleton (h : l <+: [a]) : l = [] ∨ l = [a] := by
  rcases h with ⟨r, hr⟩
  match r with
  | [] => aesop
  | r1 :: r2 =>
    apply congr_arg List.length at hr
    simp at hr
    have H : l.length = 0 := by omega
    aesop

theorem unique_g_pg_c
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_up a1 = a2)
    (b4_is : to_over b4 = b2)
    (b9 : gridt a1 b4 b6 b7) : to_up_plain b6 = remove_ones up2 ∧ to_over_plain b7 = remove_ones bot2 := by
    have H := gridt_of_PartialGrid g1
    unfold gridt_option at H
    have H3 := unicity_c b9 H
    rw [← ha, ← b4_is] at H3
    specialize H3 remover_up_rev.symm remover_over.symm
    rw [← H3.1.1, ← H3.2.1]
    constructor
    · apply to_up_plain_remover_rev_eq_remove_ones
      exact g1.right_frontier_is_false
    apply to_over_plain_remover_eq_remove_ones
    exact g1.bottom_frontier_is_true

theorem unique_g_pg_c_ones_okay
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_up_plain a1 = remove_ones a2)
    (b4_is : to_over_plain b4 = remove_ones b2)
    (b9 : gridt a1 b4 b6 b7) : to_up_plain b6 = remove_ones up2 ∧ to_over_plain b7 = remove_ones bot2 := by
    have ha1 : a1 = remover a2.reverse := by
      rw [← to_up_plain_remover_rev_eq_remove_ones] at ha
      · exact to_up_plain_inj ha
      exact g1.left_frontier_is_false
    have hb4 : b4 = remover b2 := by
      rw [← to_over_plain_remover_eq_remove_ones] at b4_is
      · exact to_over_plain_inj b4_is
      exact g1.top_frontier_is_true
    have H := gridt_of_PartialGrid g1
    unfold gridt_option at H
    have H3 := unicity_c b9 H
    specialize H3 ha1 hb4
    rw [← H3.1.1, ← H3.2.1]
    constructor
    · apply to_up_plain_remover_rev_eq_remove_ones
      exact g1.right_frontier_is_false
    apply to_over_plain_remover_eq_remove_ones
    exact g1.bottom_frontier_is_true

--theorem foo (ha : is_false a) (h : remover a = to_over_plain (m ++ q)) : False := by sorry
theorem same_time (h : gridt i j k l) (h1 : PartialGrid a b mid d2 e2)
  : (remove_ones a = to_up_plain i → remove_ones b <+: to_over_plain j → remove_ones mid <+: to_over_plain l)
  ∧ (remove_ones b = to_over_plain j → remove_ones a <:+ to_up_plain i → remove_ones e2 <:+ to_up_plain k) := by
  induction h generalizing a b mid d2 e2 with
  | empty =>
    constructor
    · intro a_is b_is
      change _ <+: [] at b_is
      simp at b_is
      have H := partial_grid_rm_empty_helper h1 a_is b_is
      aesop
    intro b_is a_is
    change _ <:+ [] at a_is
    simp at a_is
    have H := partial_grid_rm_empty_helper h1 a_is b_is
    aesop
  | top_bottom i =>
    constructor
    · intro a_is b_is
      rcases prefix_of_singleton b_is with h3 | h4
      · have H2 := partial_grid_rm_empty_helper h1 a_is h3
        aesop
      have H := partial_grid_rm_top_helper h1 a_is h4
      aesop
    intro b_is a_is
    change _ <:+ [] at a_is
    simp at a_is
    have H := partial_grid_rm_top_helper h1 a_is b_is
    aesop
  | sides i =>
    constructor
    · intro a_is b_is
      change _ <+: [] at b_is
      simp at b_is
      have H := partial_grid_rm_side_helper h1 a_is b_is
      aesop
    intro b_is a_is
    rcases suffix_of_singleton a_is with h3 | h4
    · have H := partial_grid_rm_empty_helper h1 h3 b_is
      aesop
    have H := partial_grid_rm_side_helper h1 h4 b_is
    aesop
  | top_left i =>
    constructor
    · intro a_is b_is
      rcases prefix_of_singleton b_is with h3 | h4
      · have H := partial_grid_rm_side_helper h1 a_is h3
        aesop
      have H := partial_grid_rm_top_left_helper h1 a_is h4
      aesop
    intro b_is a_is
    rcases suffix_of_singleton a_is with h3 | h4
    · have H := partial_grid_rm_top_helper h1 h3 b_is
      aesop
    have H := partial_grid_rm_top_left_helper h1 h4 b_is
    aesop
  | adjacent i k h =>
    constructor
    · intro a_is b_is
      rcases prefix_of_singleton b_is with h3 | h4
      · have H := partial_grid_rm_side_helper h1 a_is h3
        aesop
      have H := partial_grid_rm_adjacent_helper h1 a_is h4 h
      have H : remove_ones mid = [] ∨ remove_ones mid = [(k, true)] ∨
        remove_ones mid = [(k, true), (i, true)] := by aesop
      change _ <+: [(k, true), (i, true)]
      aesop
    intro b_is a_is
    rcases suffix_of_singleton a_is with h3 | h4
    · have H := partial_grid_rm_top_helper h1 h3 b_is
      aesop
    have H := partial_grid_rm_adjacent_helper h1 h4 b_is h
    have H : remove_ones mid = [] ∨ remove_ones mid = [(k, true)] ∨
        remove_ones mid = [(k, true), (i, true)] := by aesop
    change _ <:+ [(k, false), (i, false)]
    aesop
  | separated i j h =>
    constructor
    · intro a_is b_is
      rcases prefix_of_singleton b_is with h3 | h4
      · have H := partial_grid_rm_side_helper h1 a_is h3
        aesop
      have H := partial_grid_rm_separated_helper h1 a_is h4 h
      aesop
    intro b_is a_is
    rcases suffix_of_singleton a_is with h3 | h4
    · have H := partial_grid_rm_top_helper h1 h3 b_is
      aesop
    have H := partial_grid_rm_separated_helper h1 h4 b_is h
    aesop
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    constructor
    · intro ha hb
      have ha1 : m = [] ∨ q = [] ∨ ∃ a1 a2, a1.length > 0 ∧ a2.length > 0 ∧
          a = a1 ++ a2 ∧ remove_ones a1 = to_up_plain q ∧ remove_ones a2 = to_up_plain m :=
        remove_ones_eq_to_up_plain_prod ha
      rcases ha1 with m_nil | q_nil | ⟨a1, a2, a1_len, a2_len, ha1, a1q, a2m⟩
      · have H : remove_ones a = to_up_plain q := by
          rw [m_nil] at ha
          convert ha
        have on : o = [] ∧ p = n := word_side_side_t _ _ _ t m_nil
        specialize h2_ih h1
        have new_h2_ih := h2_ih.1 H
        rw [on.2] at new_h2_ih
        exact new_h2_ih hb
      · have H : remove_ones a = to_up_plain m := by
          rw [q_nil] at ha
          convert ha
          simp; rfl
        have rs : r = [] ∧ s = p := word_side_side_t _ _ _ h2 q_nil
        specialize h1_ih h1
        have new_h2_ih := h1_ih.1 H hb
        rw [rs.2]
        exact new_h2_ih
      rcases splittable_horizontally_of_pg h1 _ _ ha1 a2_len a1_len
        with ⟨mid, d1, e1, d2, e2, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
      · specialize h1_ih i1
        have new_h1_ih := h1_ih.1 a2m hb
        exact (h2_ih i2).1 a1q new_h1_ih
      rcases baaad with ⟨_, _, _, _, _, _, ⟨mid_nil⟩, _⟩
      aesop
    intro hb ha
    have ha1 : remove_ones a <:+ to_up_plain q ++ to_up_plain m := by
      have H : to_up_plain q ++ to_up_plain m = to_up_plain (m.toList ++ q.toList) := by
        simp [to_up_plain_append]
        congr
      rw [H]
      convert ha
    have H : to_up_plain (o * r) = to_up_plain r ++ to_up_plain o := by
      have H1 : to_up_plain (o.toList ++ r.toList) = to_up_plain r ++ to_up_plain o := by
        simp [to_up_plain]
        rfl
      rw [← H1]
      congr
    rw [H]
    match m with
    | [] =>
      nth_rewrite 2 [to_up_plain] at ha1
      simp at ha1
      specialize h2_ih h1
      have on : o = [] ∧ p = n := word_side_side_t _ _ _ t rfl
      rw [← on.2] at hb
      have h_new := h2_ih.2 hb ha1
      rw [on.1]
      nth_rewrite 2 [to_up_plain]
      simp
      exact h_new
    | m1 :: m2 =>
      have H : remove_ones a <:+ to_up_plain (m1 :: m2) ∨
        ∃ a1 a2, a1.length > 0 ∧ a = a1 ++ a2 ∧
        remove_ones a2 = to_up_plain  (m1 :: m2) ∧ remove_ones a1 <:+ to_up_plain q := by
        exact helper_bajillion ha1
      rcases H with ha1 | ⟨a1, a2, a1_len, a1_is, ha11⟩
      · have H2 : remove_ones e2 <:+ to_up_plain o := (h1_ih h1).2 hb ha1
        exact suffix_of_append H2
      have a2_len : a2.length > 0 := by
        have H := remove_ones_len a2
        rw [ha11.1] at H
        simp [to_up_plain] at H
        omega
      rcases splittable_horizontally_of_pg h1 _ _ a1_is a2_len a1_len
          with ⟨mid4, d4, e4, e5, d5, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
      · have H : (d2 = d4 ++ e4 ++ e5 ∧ d5 = e2) ∨ (d2 = d4 ∧ e5 = [] ∧ e2 = e4 ++ d5) := by
          exact frontier_options_from_vertical h1 i1 i2 hf
        rcases H with bb | fb
        · specialize h1_ih i1
          have one := h1_ih.1 ha11.1 (by rw [hb])
          have two := h1_ih.2 hb (by rw [ha11.1])
          rw [← bb.2]
          exact suffix_of_append two
        rw [fb.2.1] at i1
        have H := unique_g_pg_c_ones_okay i1 ha11.1.symm hb.symm t
        rw [fb.2.2, remove_ones_append, H.1]
        refine List.suffix_append_right ?_
        exact (h2_ih i2).2 H.2.symm ha11.2
      rcases baaad with ⟨db, c11, drest, h3, ⟨d2_is⟩, ⟨a1_is⟩, ⟨mid_nil⟩, len3⟩
      specialize h1_ih h3
      have H2 := h1_ih.2 hb (by rw [ha11.1])
      exact suffix_of_append H2
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i m n o p q r s t
    constructor
    intro ha hb
    have H : to_over_plain (n * q) = to_over_plain n ++ to_over_plain q := by
      simp [to_over_plain]
      sorry
    rw [H] at hb
    have H : ∃ b1 b2, b = b1 ++ b2 ∧
      remove_ones b1 = to_over_plain n ∧ remove_ones b2 = to_over_plain q := by sorry
    rcases H with ⟨b1, b2, b_is, b1_is, b2_is⟩
    rcases splittable_vertically_of_pg' h1 _ _ b_is (by sorry) (by sorry)
      with ⟨d4, e4, d5, e3, mid4, i1, i2, ⟨hf⟩, ⟨hl⟩⟩ | baaad
    · specialize h1_ih i1
      have new_h1_ih := h1_ih.1 ha (by rw [b1_is])
      specialize h2_ih i2
      have new_h2_ih := h2_ih.2
      match d4 with
      | [] => sorry
      | d41 :: d42 =>
        sorry
    sorry
    sorry
