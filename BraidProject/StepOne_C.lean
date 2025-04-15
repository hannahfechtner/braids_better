import BraidProject.SemiThue_C
import BraidProject.AlphabetRel
import BraidProject.TrueFalse_C

section toAdd

theorem infix_cons_ne (h : a :: b <:+: c :: d) (ne : a ≠ c) : a :: b <:+: d := by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at hwt
    exact (ne hwt.1).elim
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    use tail, t
    exact hwt.2

theorem infix_cons_cons_ne_double (h : [a, b] <:+: c1 :: c2 :: d) (ne : b ≠ c2) : [a, b] <:+: c2 :: d := by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at hwt
    exact (ne hwt.2.1).elim
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    use tail, t
    exact hwt.2

theorem infix_cons_cons_def (h : [a, b] <:+: c :: d :: e) : a = c ∧ b =d ∨  [a, b] <:+: d :: e:= by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at hwt
    left
    exact ⟨hwt.1, hwt.2.1⟩
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    right
    use tail, t
    exact hwt.2

theorem infix_append_right (h : l1 <:+: l2) : l1 <:+: (l2 ++ l3) := by
  rcases h with ⟨w, t, hwt⟩
  use w, t ++ l3
  rw [← hwt]
  simp

theorem infix_append_left (h : l1 <:+: l2) : l1 <:+: (l3 ++ l2) := by
  rcases h with ⟨w, t, hwt⟩
  use l3 ++ w, t
  rw [← hwt]
  simp

theorem infix_length_le (h : l1 <:+: l2) : l1.length ≤ l2.length := by
  rcases h with ⟨w, t, hwt⟩
  apply congr_arg List.length at hwt
  simp only [List.append_assoc, List.length_append] at hwt
  omega


-- theorem List.infix_singleton (h : L <:+: [a]) : L = [] ∨ L = [a] := by
--   match L with
--   | [] => left; rfl
--   | head :: tail =>
--     match tail with
--     | [] =>
--       right
--       rcases h with ⟨w, t, hwt⟩
--       have H := congr_arg List.length hwt
--       simp at H
--       have hw : w = [] := length_eq_zero.mp (by omega)
--       have ht : t = [] := length_eq_zero.mp (by omega)
--       rw [hw, List.nil_append, ht, List.append_nil] at hwt
--       exact hwt
--     | t1 :: t2 =>
--       rcases h with ⟨w, t, hwt⟩
--       have H := congr_arg List.length hwt
--       simp at H
--       omega

-- theorem List.infix_cons_concat (h : L <:+: a :: b ++ [c]) : L =  a :: b ++ [c] ∨ L <:+: a :: b ∨ L <:+: a :: b ++ [c] := by
--   induction L
--   · right; left; exact nil_infix
--   rename_i head tail ih
--   rcases h with ⟨w, t, hwt⟩
--   match w with
--   | [] =>
--     cases t using List.reverseRecOn
--     · left; rw [List.append_nil, List.nil_append] at hwt; exact hwt
--     rename_i tf tl _
--     right; left
--     use [], tf
--     simp at hwt
--     rw [hwt.1, List.nil_append]
--     rw [← List.append_assoc, ← List.concat_eq_append, ← List.concat_eq_append] at hwt
--     rw [← (List.concat_inj.mp hwt.2).1]
--     rfl
--   | w1 :: wr =>
--     cases t using List.reverseRecOn
--     · right; right; rw [List.append_nil] at hwt; simp at hwt; use a :: wr; use []; simp [hwt.2]
--     rename_i tf tl _
--     right; left
--     use a :: wr, tf
--     simp at hwt
--     simp
--     have H : wr ++ head :: (tail ++ (tf ++ [tl])) = wr ++ head :: tail ++ tf ++ [tl] := by simp
--     rw [H] at hwt
--     rw [← List.concat_eq_append, ← List.concat_eq_append] at hwt
--     rw [← (List.concat_inj.mp hwt.2).1]
--     simp

end toAdd

inductive reversing : List (ℕ × Bool) → List (ℕ × Bool) → Type
| basic {n : ℕ} : reversing [(n, false), (n, true)] []
| apart {i j : ℕ} (h : Nat.dist i j > 1) : reversing [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : reversing [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

inductive grid_style : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| basic (n : ℕ) : grid_style [(some n, false), (some n, true)] [(none, true), (none, false)]
| over (n : ℕ) : grid_style [(n, false), (none, true)] [(none, true), (n, false)]
| up (n : ℕ) : grid_style [(none, false), (some n, true)] [(n, true), (none, false)]
| empty : grid_style [(none, false), (none, true)] [(none, true), (none, false)]
| apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

def remove_ones (L : List (Option α × Bool)) : List (α × Bool) :=
  match L with
  | [] => []
  | (some a, b) :: c => (a, b) :: remove_ones c
  | (none, _) :: c => remove_ones c

@[simp]
theorem remove_ones_nil : remove_ones ([] : List (Option α × Bool)) = [] := rfl

@[simp]
theorem remove_ones_append : remove_ones (L1 ++ L2) = remove_ones L1 ++ remove_ones L2 := by
  induction L1
  · simp
  rename_i head tail ih
  match head with
  | (none, _) => simp [remove_ones, ih]
  | (some _, _) => simp [remove_ones, ih]

def insert_one (a : Option ℕ × Bool) (L : List (Option ℕ × Bool)) : List (Option ℕ × Bool) :=
  match L with
  | [] => [a]
  | (none, true) :: tail =>
    match a with
    | (_, true) => a :: L
    | (_, false)=> (none, true) :: insert_one a tail
  | (none, false) :: tail => a :: (none, false) :: tail
  | (some b, true) :: tail =>
    match a with
    | (none, true) => a :: L
    | (none, false) => (some b, true) :: insert_one a tail
    | (_, _) => a :: L
  | _ => a :: L

@[simp]
theorem insert_one_nil : insert_one a [] = [a] := rfl

@[simp]
theorem insert_one_singleton : insert_one (none, true) L = (none, true) :: L := by
  induction L
  · rfl
  conv => lhs; unfold insert_one
  rename_i head tail ih
  split
  all_goals aesop

@[simp]
theorem insert_one_none_true : insert_one (none, true) L = (none, true) :: L := by
  induction L
  · rfl
  conv => lhs; unfold insert_one
  rename_i head tail ih
  split
  all_goals aesop

@[simp]
theorem insert_one_to_none_false : insert_one a ((none, false) :: tail) = a :: ((none, false) :: tail) := by rfl

@[simp]
theorem insert_one_some_some : insert_one (some a1, b1) ((some a2, b2) :: tail) = (some a1, b1) :: (some a2, b2) :: tail := by
  unfold insert_one
  split
  all_goals aesop

@[simp]
theorem insert_none_false_end : insert_one a (L ++ [(none, false)]) = insert_one a L ++ [(none, false)] := by
  have H : ∀ t a L, L.length = t → insert_one a (L ++ [(none, false)]) = insert_one a L ++ [(none, false)] := by
    intro t
    induction t with
    | zero =>
      intro a L len
      simp at len
      simp [len]
    | succ n ih =>
      intro a L len
      match a with
      | (none, true) =>
        simp
      | (none, false) =>
        match L with
        | [] => simp
        | (none, true) :: tail =>
          simp [insert_one]
          apply ih
          simp at len
          exact len
        | (none, false) :: tail =>
          simp [insert_one]
        | (some c, true) :: tail1 =>
          simp [insert_one]
          apply ih
          simp at len
          exact len
        | (some c, false) :: tail1 =>
          simp [insert_one]
      | (some b, true) =>
        match L with
        | [] => simp
        | (none, true) :: tail => simp [insert_one]
        | (none, false) :: tail => simp [insert_one]
        | (some c, true) :: tail1 => simp [insert_one]
        | (some c, false) :: tail1 => simp [insert_one]
      | (some b, false) =>
        match L with
        | [] => simp
        | (none, true) :: tail =>
          simp [insert_one]
          apply ih
          simp at len
          exact len
        | (none, false) :: tail => simp [insert_one]
        | (some c, true) :: tail1 => simp [insert_one]
        | (some c, false) :: tail1 => simp [insert_one]
  exact H _ _ _ rfl

theorem insert_one_length (h : L.length = n) : (insert_one a L).length = n + 1 := by
  induction L generalizing n
  · simp [h]
  simp at h
  rename_i ht tt htt
  specialize @htt (tt.length) rfl
  match a with
  | (none, true) =>
    simp [insert_one_none_true, h]
  | (none, false) =>
    match ht with
    | (none, true) => simp [htt, h, insert_one]
    | (none, false) => simp [h]
    | (some c, true) => simp [insert_one, htt, h]
    | (some c, false) => simp [insert_one, htt, h]
  | (some a, true) =>
    match ht with
    | (none, true) => simp [htt, h, insert_one]
    | (none, false) => simp [h]
    | (some c, true) => simp [insert_one, htt, h]
    | (some c, false) => simp [insert_one, htt, h]
  | (some a, false) =>
      match ht with
    | (none, true) => simp [htt, h, insert_one]
    | (none, false) => simp [h]
    | (some c, true) => simp [insert_one, htt, h]
    | (some c, false) => simp [insert_one, htt, h]

noncomputable def equiv_insert : SemiThue grid_style (a :: L) (insert_one a L) := by
  have H : ∀ t L a, L.length ≤ t → SemiThue grid_style (a :: L) (insert_one a L) := by
    intro t
    induction t
    · intro L a len
      simp at len
      rw [len]
      exact SemiThue.refl [a]
    rename_i n ih
    intro L a len
    match a with
    | (none, true) =>
      simp
      exact SemiThue.refl ((none, true) :: L)
    | (none, false) =>
      match L with
      | [] => exact SemiThue.refl [(none, false)]
      | (none, true) :: tail =>
        simp at len
        exact SemiThue.trans _ _ _ (SemiThue_append_right (SemiThue_rel grid_style.empty)) (SemiThue_cons (ih tail _ len))
      | (none, false) :: tail => exact SemiThue.refl ((none, false) :: (none, false) :: tail)
      | (some c, true) :: tail1 =>
        simp at len
        specialize ih tail1 (none, false) len
        exact SemiThue.trans _ _ _ (SemiThue_append_right (SemiThue_rel (grid_style.up c))) (SemiThue_cons ih)
      | (some c, false) :: tail1 =>
        exact SemiThue.refl ((none, false) :: (some c, false) :: tail1)
    | (some b, true) =>
      match L with
      | [] => exact SemiThue.refl _
      | (none, true) :: tail => exact SemiThue.refl _
      | (none, false) :: tail => exact SemiThue.refl _
      | (some c, true) :: tail1 => exact SemiThue.refl _
      | (some c, false) :: tail1 => exact SemiThue.refl _
    | (some b, false) =>
      match L with
      | [] => exact SemiThue.refl _
      | (none, true) :: tail =>
        simp at len
        specialize ih tail (some b, false) len
        exact SemiThue.trans _ _ _ (SemiThue_append_right (SemiThue_rel (grid_style.over b))) (SemiThue_cons ih)
      | (none, false) :: tail => exact SemiThue.refl _
      | (some c, true) :: tail1 => exact SemiThue.refl _
      | (some c, false) :: tail1 => exact SemiThue.refl _
  exact H L.length _ _ (by simp)

@[simp]
theorem remove_ones_insert_none : remove_ones (insert_one (none, b) L) = remove_ones L := by
  induction L
  · simp [remove_ones]
  rename_i head tail ih
  match head with
  | (none, true) =>
    cases b
    all_goals
    simp [insert_one, remove_ones, ih]
  | (none, false) => simp [insert_one, remove_ones, ih]
  | (some a, true) =>
    cases b
    all_goals
    simp [insert_one, remove_ones, ih]
  | (some a, false) => simp [insert_one, remove_ones, ih]

@[simp]
theorem remove_ones_insert_some : remove_ones (insert_one (some a, b) L) = (a, b) :: remove_ones L := by
  induction L
  · simp [remove_ones]
  rename_i head tail ih
  match head with
  | (none, true) =>
    cases b
    all_goals
    simp [insert_one, remove_ones, ih]
  | (none, false) => simp [insert_one, remove_ones, ih]
  | (some a, true) =>
    cases b
    all_goals
    simp [insert_one, remove_ones, ih]
  | (some a, false) => simp [insert_one, remove_ones, ih]

def move_ones (L : List (Option ℕ × Bool)) :=
  match L with
  | [] => []
  | head :: tail => insert_one head (move_ones tail)

@[simp]
theorem moves_ones_nil : move_ones [] = [] := rfl

@[simp]
theorem move_ones_singleton : move_ones [a] = [a] := by
  unfold move_ones
  unfold insert_one
  simp

@[simp]
theorem move_ones_length : (move_ones L).length = L.length := by
  induction L
  · rfl
  unfold move_ones
  rename_i ih
  simp [insert_one_length, ih]

@[simp]
theorem move_ones_none_true : move_ones ((none, true)::a) = (none, true) :: move_ones a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    conv => lhs; unfold move_ones
    simp

@[simp]
theorem move_ones_none_false_end : move_ones (a ++ [(none, false)]) = move_ones a ++ [(none, false)] := by
  induction a
  · simp
  simp [move_ones]
  rename_i ih
  rw [ih, insert_none_false_end]

noncomputable def equiv_move_ones : SemiThue grid_style L (move_ones L) := by
  induction L
  · exact SemiThue.refl []
  rename_i head tail ih
  exact SemiThue.trans _ _ _ (SemiThue_cons ih) (equiv_insert)

theorem remove_ones_move_ones : remove_ones (move_ones L) = remove_ones L := by
  induction L
  · simp
  rename_i head tail ih
  match head with
  | (none, true) => simp [move_ones, remove_ones, ih]
  | (none, false) =>
    simp [remove_ones, move_ones, ih]
  | (some a, true) => simp [move_ones, remove_ones, ih]
  | (some a, false) => simp [move_ones, remove_ones, ih]

def pairsTogether_C  (L : List (Option ℕ × Bool)) := ∀ a b, List.Infix' [(a, false), (b, true)] (remove_ones L) →
    [(some a, false), (some b, true)] <:+: L

def pairsTogether  (L : List (Option ℕ × Bool)) := ∀ a b, List.Infix' [(a, false), (b, true)] (remove_ones L) →
    List.Infix' [(some a, false), (some b, true)] L

def pairsTogether_empty : pairsTogether [] := by
  unfold pairsTogether
  simp [remove_ones_nil,
  infix_nil_C, reduceCtorEq, imp_self, implies_true]
  intro a b h1
  exfalso
  apply infix_length_le_C at h1
  simp at h1



def pairs_together_singleton : pairsTogether [a] := by
  intro c d hcd
  exfalso
  match a with
  | (none, _) =>
    change List.Infix' [(c, false), (d, true)] [] at hcd
    apply infix_length_le_C  at hcd
    simp at hcd
  | (some a, b) =>
    change List.Infix' [(c, false), (d, true)] [(a, b)] at hcd
    rcases hcd with ⟨w, t, ⟨hwt⟩⟩
    apply congr_arg List.length at hwt
    simp at hwt
    omega

def pts (L) := ∀ L1, List.Infix' L1 L → pairsTogether L1

def pts_empty : pts [] := by
  unfold pts
  intro L1 hl
  rw [List.Infix'_of_nil hl]
  exact pairsTogether_empty

def pts_chop_right (h : pts (a ++ b)) : pts a := fun L1 hl c d hcd ↦ h L1 (infix_append_right_C hl) c d hcd

def pts_chop_left (h : pts (a ++ b)) : pts b := fun L1 hl c d hcd ↦ h L1 (infix_append_left_C hl) c d hcd

def irreducible (L : List (Option ℕ × Bool)) :=
  ∀ a, (List.Infix' [(some a, false), (none, true)] L → Empty) × (List.Infix'  [(none, false), (some a, true)] L → Empty) ×
   (List.Infix' [(none, false), (none, true)] L → Empty)

def irreducible_nil : irreducible [] := by
  simp [irreducible]
  intro h
  exact ⟨double_not_infix_nil, ⟨double_not_infix_nil, double_not_infix_nil⟩⟩

def irreducible_singleton : irreducible [a] := by
  simp [irreducible]
  intro a
  constructor
  · intro h
    apply infix_length_le_C at h
    simp at h
  constructor
  · intro h
    apply infix_length_le_C at h
    simp at h
  intro h
  apply infix_length_le_C at h
  simp at h

def irreducible_rest (h : irreducible (head :: tail)) : irreducible tail := by
  intro a
  constructor
  · intro h1
    specialize h a
    apply h.1
    exact infix_cons_C h1
  constructor
  · intro h1
    specialize h a
    apply h.2.1
    exact infix_cons_C h1
  intro h1
  specialize h a
  apply h.2.2
  exact infix_cons_C h1

def irreducible_concat (h : irreducible (L ++ [a])) : irreducible (L) := by
  intro a1
  specialize h a1
  constructor
  · intro h1
    apply h.1
    exact infix_append_right_C h1
  constructor
  · intro h1
    apply h.2.1
    exact infix_append_right_C h1
  intro h1
  apply h.2.2
  exact infix_append_right_C h1

def irreducible_append (h : irreducible (a ++ b)) : irreducible a × irreducible b :=
  ⟨fun x ↦ ⟨fun hx ↦ (h x).1 (infix_append_right_C hx),
      ⟨fun hx ↦ (h x).2.1 (infix_append_right_C hx), fun hx ↦ (h x).2.2 (infix_append_right_C hx)⟩⟩,
  fun x ↦ ⟨fun hx ↦ (h x).1 (infix_append_left_C hx),
      ⟨fun hx ↦ (h x).2.1 (infix_append_left_C hx), fun hx ↦ (h x).2.2 (infix_append_left_C hx)⟩⟩⟩


def irreducible_cons_true (h : irreducible L) : irreducible ((a, true) :: L) := by
  intro a
  constructor
  · intro h1
    specialize h a
    apply h.1
    apply infix_cons_ne_C h1 (by simp)
  constructor
  · intro h1
    specialize h a
    apply h.2.1
    apply infix_cons_ne_C h1 (by simp)
  intro h1
  specialize h a
  apply h.2.2
  apply infix_cons_ne_C h1 (by simp)

def irreducible_two_cons {a b} (h : irreducible (b :: L)) (h1 : PLift (a.2 = b.2) ⊕ PLift (a.2 = true) ⊕ (Σ c d, PLift (a.1 = some c ∧ b.1 = some d))) :
    irreducible (a :: b :: L) := by
  intro a1
  rcases h1 with ⟨h1⟩ | ⟨h2⟩ | ⟨c, d, hcd⟩
  · constructor
    · intro h2
      specialize h a1
      apply h.1
      match hb : a with
      | (_, true) =>
        apply infix_cons_ne_C h2
        simp [hb]
      | (_, false) =>
        match hbb : b with
        | (_, true) =>
          simp only [Bool.false_eq_true, or_self] at h1
          exact (h1.down).elim
        | (_, false) =>
          apply infix_cons_cons_ne_double_C h2
          simp
    constructor
    · intro h2
      specialize h a1
      apply h.2.1
      match hb : a with
      | (_, true) =>
        apply infix_cons_ne_C h2
        simp [hb]
      | (_, false) =>
        match b with
        | (_, true) =>
          simp at h1
          exact (h1.down).elim
        | (_, false) =>
          apply infix_cons_cons_ne_double_C h2
          simp
    intro h2
    specialize h a1
    apply h.2.2
    match hb : a with
    | (_, true) =>
      apply infix_cons_ne_C h2
      simp [hb]
    | (_, false) =>
      match hbb : b with
      | (_, true) =>
        simp at h1
        exact (h1.down).elim
      | (_, false) =>
        apply infix_cons_cons_ne_double_C h2
        simp
  · match hb : a with
    | (fst, true) =>
      constructor
      · intro h3
        apply (h a1).1
        exact infix_cons_ne_C h3 (by simp)
      constructor
      · intro h3
        apply (h a1).2.1
        exact infix_cons_ne_C h3 (by simp)
      intro h3
      apply (h a1).2.2
      exact infix_cons_ne_C h3 (by simp)
    | (fst, false) =>
      simp at h2
      exact h2.1.elim
  match ha : a with
  | (some a2, true) =>
    match b with
    | (some b2, _) =>
      constructor
      · intro h3
        apply (h a1).1
        apply infix_cons_ne_C h3 (by simp)
      constructor
      · intro h3
        apply (h a1).2.1
        apply infix_cons_ne_C h3 (by simp)
      intro h3
      apply (h a1).2.2
      apply infix_cons_ne_C h3 (by simp)
    | (none, _) =>
      simp at hcd
      exact hcd.1.elim
  | (some a2, false) =>
    match b with
    | (some b2, _) =>
      constructor
      · intro h3
        apply (h a1).1
        apply infix_cons_cons_ne_double_C h3 (by simp)
      constructor
      · intro h3
        apply (h a1).2.1
        apply infix_cons_ne_C h3 (by simp)
      intro h3
      apply (h a1).2.2
      apply infix_cons_ne_C h3 (by simp)
    | (none, _) =>
      simp at hcd
      exact hcd.1.elim
  | (none, _) =>
    rename_i hcd
    simp at hcd
    exact hcd.1.elim


def irreducible_insert (h : irreducible L) : irreducible (insert_one a L) := by
  have H : ∀ t a L, L.length = t → irreducible L → irreducible (insert_one a L) := by
    intro t
    induction t with
    | zero =>
      intro a L len
      simp at len
      simp [len]
      intro h
      exact irreducible_singleton
    | succ n ih =>
      intro a L m irr
      match a with
      | (none, true) =>
        simp [insert_one]
        exact irreducible_cons_true irr
      | (none, false) =>
        match hl : L with
        | [] =>
          simp
          exact irreducible_singleton
        | (none, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_cons_true (ih _ _ m (irreducible_rest irr))
        | (none, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr
          left
          simp only
          exact { down := trivial }
        | (some b, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_cons_true (ih _ _ m (irreducible_rest irr))
        | (some b, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr
          left
          simp only
          exact { down := trivial }
      | (some b, true) =>
        match hl : L with
        | [] =>
          simp
          exact irreducible_singleton
        | (none, true) :: tail =>
          simp only [insert_one]
          simp at m
          apply irreducible_two_cons
          · apply irreducible_cons_true
            exact irreducible_rest irr
          left; simp only; exact { down := trivial }
        | (none, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr
          right; left; simp only
          exact { down := trivial }
        | (some b, true) :: tail =>
          simp only [insert_one]
          simp at m
          apply irreducible_two_cons irr
          right; left; simp only
          exact { down := trivial }
        | (some b, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr
          right; left; simp; exact { down := trivial }
      | (some c, false) =>
        match hl : L with
        | [] =>
          simp
          exact irreducible_singleton
        | (none, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_cons_true (ih _ _ m (irreducible_rest irr))
        | (none, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr
          left; simp only; exact { down := trivial }
        | (some b, true) :: tail =>
          simp only [insert_one]
          simp at m
          apply irreducible_two_cons irr
          right; right
          use c
          use b
          simp
          exact { down := trivial }
        | (some b, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr
          left; simp only; exact { down := trivial }
  exact H _ _ _ rfl h

def irreducible_move_ones : irreducible (move_ones L) := by
  induction L
  · simp
    exact irreducible_nil
  rename_i head tail ih
  unfold move_ones
  exact irreducible_insert ih

theorem insert_irreducible (h : irreducible (head :: tail)) : insert_one head tail = head :: tail := by
  match head with
  | (none, true) => simp [insert_one]
  | (none, false) =>
    match hl : tail with
    | [] => simp [irreducible_singleton]
    | (none, true) :: tail =>
      simp only [insert_one]
      have H : Empty := by
        apply (h 0).2.2
        use [], tail
        simp
        exact {down := trivial}
      cases H
    | (none, false) :: tail => simp only [insert_one]
    | (some b, true) :: tail =>
      simp only [insert_one]
      have H : Empty := by
        apply (h b).2.1
        use [], tail
        simp
        exact {down := trivial}
      cases H
    | (some b, false) :: tail =>
      simp only [insert_one]
  | (some b, true) =>
    match hl : tail with
    | [] => simp [irreducible_singleton]
    | (none, true) :: tail => simp only [insert_one]
    | (none, false) :: tail => simp only [insert_one]
    | (some b, true) :: tail => simp only [insert_one]
    | (some b, false) :: tail => simp only [insert_one]
  | (some c, false) =>
    match hl : tail with
    | [] => simp [irreducible_singleton]
    | (none, true) :: tail =>
      simp only [insert_one]
      have H := by
        apply (h c).1
        use [], tail
        simp
        exact {down := trivial}
      cases H
    | (none, false) :: tail => simp only [insert_one]
    | (some b, true) :: tail => simp only [insert_one]
    | (some b, false) :: tail => simp only [insert_one]

theorem move_irreducible (h : irreducible L) : move_ones L = L := by
  induction L
  · simp
  rename_i head tail ih
  simp [move_ones]
  specialize ih (irreducible_rest h)
  rw [ih, insert_irreducible h]

theorem move_ones_rep : move_ones (move_ones L) = move_ones L := by
  apply move_irreducible
  exact irreducible_move_ones

theorem irr_helper (h : irreducible ((none, false) :: tail)) (h2 : remove_ones tail = (a, true) :: rest) : False := by
  have H : ∀ t L rest, L.length = t → irreducible ((none, false) :: L) → remove_ones L = (a, true) :: rest → False := by
    intro t
    induction t with
    | zero =>
      intro L rest len irr hin
      simp at len
      simp [len, remove_ones] at hin
    | succ n ih =>
      intro L rest len irr hin
      match L with
      | [] => simp at len
      | (none, true) :: tail1 =>
        have H := by
          apply (irr 0).2.2
          use [], tail1
          simp
          exact {down := trivial}
        cases H
      | (none, false) :: tail1 =>
        simp [remove_ones] at hin
        specialize ih tail1 rest
        simp at len
        exact ih len (irreducible_rest irr) hin
      | (some b, true) :: tail1 =>
        have H := by
          apply (irr b).2.1
          use [], tail1
          simp
          exact {down := trivial}
        cases H
      | (some b, false) :: tail1 => simp [remove_ones] at hin
  exact H _ _ _ rfl h h2

def funky_helper (irr : irreducible ((none, false) :: L)) (hin : List.Infix' [(c, false), (d, true)] ((b, false) :: remove_ones L)) :
    List.Infix' [(c, false), (d, true)] (remove_ones L) := by
  match hl : remove_ones L with
  | [] =>
    rw [hl] at hin
    apply infix_length_le_C at hin
    simp at hin
  | (a, true) :: tail =>
    exact (irr_helper irr hl).elim
  | (a, false) :: tail =>
    rw [hl] at hin
    apply infix_cons_cons_ne_double_C hin
    simp

def pt_of_irr (h : irreducible L) : pairsTogether L := by
  have H : ∀ t L, L.length ≤ t → irreducible L → pairsTogether L := by
    intro t
    induction t
    · intro L len
      simp at len
      intro h
      rw [len]
      exact pairsTogether_empty
    rename_i n ih
    intro L len irr c d h
    cases L with
    | nil =>
      apply infix_length_le_C at h
      simp at h
    | cons head tail =>
      match head with
      | (none, true) =>
        simp [remove_ones] at h
        simp at len
        exact infix_cons_C <| ih tail len (irreducible_rest irr) c d h
      | (none, false) =>
        match tail with
        | [] =>
          apply infix_length_le_C at h
          simp [remove_ones] at h
        | (none, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply infix_cons_C
          apply infix_cons_C
          exact ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) c d h
        | (none, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply infix_cons_C
          apply infix_cons_C
          exact ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) c d h
        | (some e, true) :: tail1 =>
          simp at len
          apply infix_cons_C
          apply ih ((some e, true) :: tail1) _ (irreducible_rest irr) _ _ h
          simp [len]
        | (some e, false) :: tail1 =>
          simp at len
          apply infix_cons_C
          apply ih ((some e, false) :: tail1) _ (irreducible_rest irr) _ _ h
          simp [len]
      | (some b, true) =>
        match tail with
        | [] =>
          apply infix_length_le_C at h
          simp [remove_ones] at h
        | (none, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply infix_cons_C
          apply infix_cons_C
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          apply infix_cons_ne_C h
          simp
        | (none, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply infix_cons_C
          apply infix_cons_C
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          apply infix_cons_ne_C h
          simp
        | (some e, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply infix_cons_C
          apply infix_cons_C
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          have h3 : [(c, false), (d, true)].Infix' ((e, true) :: remove_ones tail1) := by
            apply infix_cons_ne_C h
            simp
          apply infix_cons_ne_C h3
          simp
        | (some c, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply infix_cons_C
          apply ih ((some c, false) :: tail1)
          · simp [len]
          apply irreducible_rest irr
          apply infix_cons_ne_C h
          simp
      | (some b, false) =>
        match tail with
        | [] =>
          apply infix_length_le_C at h
          simp [remove_ones] at h
        | (none, true) :: tail1 =>
          simp at len
          apply infix_cons_C
          apply infix_cons_C
          have H : Empty := by
            apply (irr b).1
            use [], tail1
            simp
            exact {down := trivial}
          cases H
        | (none, false) :: tail1 =>
          simp only [List.length_cons, add_le_add_iff_right] at len
          apply infix_cons_C <| infix_cons_C <| ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) _ _
            (funky_helper (irreducible_rest irr) h)
        | (some e, true) :: tail1 =>
          simp at len
          have H : PLift (c = b ∧ e = d) ⊕ PLift (c ≠ b) ⊕ PLift (e ≠ d) := by
            if hcb : c = b then
              if hed : e = d
                then
                  left
                  exact {down := ⟨hcb, hed⟩}
                else
                  right; right
                  exact {down := hed}
            else
              right; left
              exact {down := hcb}
          rcases H with ⟨h1⟩ | h2 | h3
          · rw [h1.1.1, h1.1.2]
            use [], tail1
            simp
            exact {down := trivial}
          · have h3 : [(c, false), (d, true)].Infix' (remove_ones ((some e, true) :: tail1)) := by
              apply infix_cons_ne_C h
              simp [h2.1]
            simp [remove_ones] at h3
            have h4 : [(c, false), (d, true)].Infix' (remove_ones (tail1)) := by
              apply infix_cons_ne_C h3
              simp [h2.1]
            apply infix_cons_C <| infix_cons_C <| ih tail1 (by omega)
              (irreducible_rest (irreducible_rest irr)) _ _ h4
          simp [remove_ones] at h
          have h3 : [(c, false), (d, true)].Infix' ((e, true) :: remove_ones tail1) := by
            apply infix_cons_cons_ne_double_C h
            simp [h3.1.symm]
          have h4 : [(c, false), (d, true)].Infix' (remove_ones tail1) := by
            apply infix_cons_ne_C h3
            simp
          exact infix_cons_C <| infix_cons_C <| ih tail1 (by omega) (irreducible_rest
            (irreducible_rest irr)) _ _ h4
        | (some e, false) :: tail1 =>
          simp at len
          apply infix_cons_C
          apply ih ((some e, false) :: tail1) (by simp [len]) (irreducible_rest irr)
          apply infix_cons_cons_ne_double_C h
          simp
  exact H L.length L (by simp) h

def irr_infix (h : irreducible L) (h2 : List.Infix' L1 L) : irreducible L1 :=
  fun a ↦ ⟨fun ha ↦ (h a).1 (ha.trans h2), ⟨fun ha ↦ (h a).2.1 (ha.trans h2), fun ha ↦
        (h a).2.2 (ha.trans h2)⟩⟩

def pts_of_irr (h : irreducible L) : pts L := by
  intro h1 hl
  apply pt_of_irr (irr_infix h hl)

def to_option (L : List (ℕ × Bool)) : List (Option ℕ × Bool) := (List.map (fun x ↦ (some x.1, x.2)) L)

def is_false_to_option (ha : is_false a) : is_false (to_option a) := by
  unfold to_option
  unfold is_false
  exact {down := by
              intro x hx
              simp at hx
              rcases hx with ⟨a1, h1 | h2⟩
              · rw [← h1.2]
              have := ha.1 _ h2.1
              rw [← h2.2]
              simp at this
              }
  -- intro x hx
  -- simp only [List.mem_map, Prod.exists, Bool.exists_bool] at hx
  -- rcases hx with ⟨a1, (spec1 | spec2)⟩
  -- · rw [← spec1.2]
  -- have := ha _ spec2.1
  -- simp at this

def is_true_to_option (ha : is_true a) : is_true (to_option a) := by
  unfold to_option
  intro x hx
  simp only [List.mem_map, Prod.exists, Bool.exists_bool] at hx
  exact {down := by
              rcases hx with ⟨a1, spec1 | spec2⟩
              · have := (ha _ ⟨spec1.1⟩).1
                simp [this, ← spec1.2]
              rw [← spec2.2]}
  -- rcases hx with ⟨a1, (spec1 | spec2)⟩
  -- · have := ha _ spec1.1
  --   simp at this
  -- rw [← spec2.2]

def skeleton_to_option (h : skeleton_order a) : skeleton_order (to_option a) := by
  rcases h with ⟨a1, a2, spec⟩
  use to_option a1, to_option a2
  constructor
  · exact is_false_to_option spec.1
  constructor
  · exact is_true_to_option spec.2.1
  rw [spec.2.2.1]
  unfold to_option
  rw [List.map_append]
  exact ⟨rfl⟩
  --simp [is_false_to_option spec.1, is_true_to_option spec.2.1, spec.2.2]
  -- unfold to_option
  -- exact List.map_append (fun x ↦ (some x.1, x.2)) a1 a2

theorem remove_map_helper {a : List (ℕ × Bool)} : remove_ones (to_option a) = a := by
  induction a
  · rfl
  rename_i ih
  simp [to_option, remove_ones]
  exact ih

def pt_to_option : pairsTogether (to_option c) := by
  intro a b hab
  simp [remove_map_helper] at hab
  rcases hab with ⟨w, t, hwt⟩
  use to_option w
  use to_option t
  rw [← hwt.1]
  simp [to_option]
  exact {down := trivial}

def pts_to_option : pts (to_option a) := by
  have H : irreducible (to_option a) := by
    intro c
    constructor
    · intro h
      induction a
      · simp [to_option] at h
        exact double_not_infix_nil h
      rename_i ha ta iha
      apply iha
      match ta with
      | [] =>
        simp [to_option] at h
        apply infix_length_le_C at h
        simp at h
      | t :: taa =>
        simp [to_option] at h
        have h3 := by
          apply infix_cons_cons_ne_double_C h
          simp
        exact h3
    constructor
    · intro h
      induction a
      · simp [to_option] at h
        exact double_not_infix_nil h
      rename_i ha ta iha
      apply iha
      simp [to_option] at h
      exact infix_cons_ne_C h (by simp)
    intro h
    induction a
    · simp [to_option] at h
      exact double_not_infix_nil h
    rename_i ha ta iha
    apply iha
    simp [to_option] at h
    exact infix_cons_ne_C h (by simp)
  exact pts_of_irr H

def irr_to_option : irreducible (to_option a) := by
  induction a with
  | nil => simp [to_option]; exact irreducible_nil
  | cons head tail ih =>
    simp [to_option]
    intro x
    constructor
    · intro hx
      match tail with
      | [] =>
        apply infix_length_le_C at hx
        simp at hx
      | t1 :: tr =>
        exact (ih x).1 (infix_cons_cons_ne_double_C hx (by simp))
    constructor
    · intro hx
      exact (ih x).2.1 (infix_cons_ne_C hx (by simp))
    intro hx
    exact (ih x).2.2 (infix_cons_ne_C hx (by simp))

def five_cases (b_ne : b1 ≠ b2) (h : a ++ [b1, b2] ++ c = d ++ [b1, b2] ++ e) :
  PLift (a = d ∧ c = e) ⊕ (Σ a1 a2, PLift (a = a1 ++ [b1, b2] ++ a2 ∧ d = a1 ∧ e = a2 ++ [b1, b2] ++ c)) ⊕
  (Σ c1 c2, PLift (c = c1 ++ [b1, b2] ++ c2 ∧ d = a ++ [b1, b2] ++ c1 ∧ e = c2)) := by
  induction a generalizing b1 b2 c d e
  · simp at h
    simp
    match d with
    | [] =>
      left
      simp at h
      exact ⟨rfl, h⟩
    | d1 :: [] =>
      simp at h
      left
      simp
      rw [h.2.1] at b_ne
      exact {down := by simp at b_ne}
    | d1 :: d2 :: dr =>
      simp at h
      right; right
      use dr, e
      simp [h]
      exact {down := trivial}
  rename_i a1 ar ih
  match d with
  | [] =>
    simp at h
    match ar with
    | [] => simp [b_ne] at h
    | a2 :: arr =>
      simp at h
      simp [h.2.1, h.2.2]
      right; left
      use [], arr
      simp [h]
      exact {down := trivial}
  | d1 :: [] =>
    simp at h
    simp [h.1]
    match ar with
    | [] => left; simp at h; exact {down := ⟨⟨h.1, rfl⟩, h.2⟩}
    | a2 :: a3 :: arr =>
      simp at h
      simp [h]
      right; left
      use [d1]
      simp [h.1, h.2.1]
      use arr
      simp [h.2.1, h.2.2]
      exact {down := trivial}
    | a2 :: [] =>
      simp at h
      exfalso
      apply b_ne
      exact h.2.2.1
  | d1 :: d2 :: dr =>
    simp at h
    simp [h.1]
    have H1 : ar ++ b1 :: b2 :: c  = ar ++ [b1, b2] ++ c := by simp
    have H : d2 :: (dr ++ b1 :: b2 :: e) = (d2 :: dr) ++ [b1, b2] ++ e := by simp
    rw [H1, H] at h
    specialize ih b_ne h.2
    rcases ih with h1 | h2 | h3
    · left
      exact {down := ⟨⟨h.1, h1.1.1⟩, h1.1.2⟩}
    · rcases h2 with ⟨a1', a2', spec⟩
      right; left
      use d1 :: a1'
      use a2'
      rw [spec.1.1, spec.1.2.1, spec.1.2.2, h.1]
      exact {down := by simp}
    rcases h3 with ⟨c1', c2', spec⟩
    right; right
    use c1', c2'
    rw [spec.1.1, spec.1.2.1, spec.1.2.2, h.1]
    exact {down := by simp}

def irreducible_none_false_swap (b) (h : irreducible ((none, false) :: L)) : irreducible ((b, false) :: L) := by
  match L with
  | [] => exact irreducible_singleton
  | (some c, true) :: tail =>
    specialize h c
    have H := by
      apply h.2.1
      use [], tail
      simp
      exact {down := trivial}
    cases H
  | (some c, false) :: tail =>
    intro a
    constructor
    · intro h1
      apply (irreducible_rest h a).1 (infix_cons_cons_ne_double_C h1 (by simp))
    constructor
    · intro h1
      apply (irreducible_rest h a).2.1 (infix_cons_cons_ne_double_C h1 (by simp))
    intro h1
    apply (irreducible_rest h a).2.2 (infix_cons_cons_ne_double_C h1 (by simp))
  | (none, true) :: tail =>
    specialize h 0
    have H := by
      apply h.2.2
      use [], tail
      simp
      exact {down := trivial}
    cases H
  | (none, false) :: tail =>
    intro a
    constructor
    · intro h1
      apply (irreducible_rest h a).1 (infix_cons_cons_ne_double_C h1 (by simp))
    constructor
    · intro h1
      apply (irreducible_rest h a).2.1 (infix_cons_cons_ne_double_C h1 (by simp))
    intro h1
    apply (irreducible_rest h a).2.2 (infix_cons_cons_ne_double_C h1 (by simp))

theorem helper5 (h : irreducible ((some d, false) :: (L ++ [(some e, true)])))
    (h2 : remove_ones L = []) : L = [] := by
  induction L
  · rfl
  rename_i head tail ih
  have H : remove_ones tail = [] := by
    match head with
    | (none, snd) =>
      simp [remove_ones] at h2
      exact h2
    | (some a, snd) =>
      simp [remove_ones] at h2
  exfalso
  match head with
  | (some a, snd) =>
    simp [remove_ones] at h2
  | (none, true) =>
    specialize h d
    have H := by
      apply h.1
      use []
      use tail ++ [(some e, true)]
      simp
      exact {down := trivial}
    cases H
  | (none, false) =>
    specialize ih (irreducible_none_false_swap _ (irreducible_rest h)) H
    rw [ih] at h
    specialize h e
    have H := by
      apply h.2.1
      use [(some d, false)], []
      simp
      exact {down := trivial}
    cases H

def helper4 (hi : irreducible ((some d, false) :: L)) (h : [(b2, true)] = remove_ones L) :
    Σ L2, PLift (L = (some b2, true) :: L2 ∧ remove_ones L2 = []) := by
  induction L using List.reverseRecOn
  · simp at h
  rename_i train caboose ih
  have H : irreducible ((some d, false) :: train) := irreducible_concat hi
  specialize ih H
  match caboose with
  | (none, snd) =>
    simp [remove_ones] at h
    rcases ih h with ⟨L2, spec⟩
    use L2 ++ [(none, snd)]
    simp [spec.1, remove_ones]
    exact {down := trivial}
  | (some e, snd2) =>
    simp [remove_ones] at h
    have H1 : [(b2, true)] = [].concat (b2, true) := by simp
    have H2 : remove_ones train ++ [(e, snd2)] = (remove_ones train).concat (e, snd2) := by simp
    rw [H1, H2] at h
    have := List.concat_inj.mp h
    simp at this
    rw [this.2.2] at hi
    use []
    simp [helper5 hi this.1, this]
    exact {down := trivial}

def helper3 (h : [(b1, false), (b2, true)] = remove_ones L) (hi : irreducible L) :
    Σ L1 L2, PLift (L = L1 ++ [(some b1, false), (some b2, true)] ++ L2 ∧
    [] = remove_ones L1 ∧ [] = remove_ones L2) := by
  induction L
  · simp at h
  rename_i head tail ih
  match head with
  | (none, snd) =>
    simp [remove_ones] at h
    specialize ih h (irreducible_rest hi)
    rcases ih with ⟨L3, L4, spec⟩
    use (none, snd) :: L3, L4
    rw [spec.1.1]
    simp [remove_ones, ← spec.1.2.1, ←  spec.1.2.2]
    exact {down := trivial}
  | (some d, snd) =>
    simp [remove_ones] at h
    simp [h.1]
    use []
    simp
    rw [h.1.2] at hi
    exact helper4 hi h.2

def helper2 (h : [(b1, false), (b2, true)] ++ c = remove_ones L)(hi : irreducible L) :
    Σ L1 L2, PLift (L = L1 ++ [(some b1, false), (some b2, true)] ++ L2 ∧ [] = remove_ones L1 ∧ c = remove_ones L2) := by
  induction L using List.reverseRecOn generalizing c
  · simp at h
  rename_i train caboose ih
  match caboose with
  | (none, snd) =>
    simp only [remove_ones_append, remove_ones, List.append_nil] at h
    have := ih h (irreducible_concat hi)
    rcases this with ⟨L3, L4, spec⟩
    use L3, L4 ++ [(none, snd)]
    rw [← spec.1.2.1, spec.1.2.2, spec.1.1]
    simp [remove_ones]
    exact {down := trivial}
  | (some d, bo) =>
    induction c using List.reverseRecOn
    · rw [List.append_nil] at h
      exact helper3 h hi
    rename_i train1 caboose1 _
    simp [remove_ones] at h
    have H1 : (b1, false) :: (b2, true) :: (train1 ++ [caboose1]) = ((b1, false) :: (b2, true) :: train1).concat caboose1 := by simp
    have H2 : remove_ones train ++ [(d, bo)] = (remove_ones train).concat (d, bo) := by simp
    rw [H1, H2] at h
    have := List.concat_inj.mp h
    specialize ih (List.concat_inj.mp h).1 (irreducible_concat hi)
    rcases ih with ⟨L1, L2, spec⟩
    use L1
    use L2 ++ [(some d, bo)]
    simp [spec.1, h, remove_ones]
    exact {down := (List.concat_inj.mp h).2}

def helper (h : a ++ [(b1, false), (b2, true)] ++ c = remove_ones L)(hi : irreducible L) :
    Σ L1 L2, PLift (L = L1 ++ [(some b1, false), (some b2, true)] ++ L2 ∧ a = remove_ones L1 ∧ c = remove_ones L2) := by
  induction L generalizing a c
  · simp at h
  rename_i headl taill ihl
  match headl with
  | (none, snd) =>
    simp only [remove_ones] at h
    specialize ihl h (irreducible_rest hi)
    rcases ihl with ⟨L1, L2, spec⟩
    use (none, snd) :: L1
    use L2
    exact {down := by simp [spec.1, remove_ones]}
  | (some d, bo) =>
    match a with
    | [] =>
      rw [List.nil_append] at h
      exact helper2 h hi
    | a1 :: ar =>
      simp only [List.cons_append, remove_ones, List.cons.injEq] at h
      specialize ihl h.2 (irreducible_rest hi)
      rcases ihl with ⟨L1, L2, spec⟩
      use (some d, bo) :: L1
      use L2
      simp [spec.1, h.1, remove_ones]
      exact {down := trivial}

def giant_list_split {w : List (Option ℕ × Bool)} (h : remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t =
    e ++ [(c1, false), (c2, true)] ++ f) (ptw : irreducible w) (ptt : irreducible t) : PLift (remove_ones w = e ∧ remove_ones t = f) ⊕
    (Σ w1 w2, PLift (w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = remove_ones w1 ∧
    f = remove_ones w2 ++ [(c1, false), (c2, true)] ++ remove_ones t)) ⊕
    (Σ t1 t2, PLift (t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧
    e = remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t1 ∧ f = remove_ones t2)) := by
  rcases five_cases (by simp) h with h1 | h2 | h3
  · left; exact h1
  · rcases h2 with ⟨a1, a2, spec⟩
    have := helper spec.1.1.symm ptw
    rcases this with ⟨L3, L4, speckle⟩
    simp at speckle
    right; left
    use L3, L4
    exact {down := by simp [spec.1, speckle.1]}
  rcases h3 with ⟨a1, a2, spec⟩
  have := helper spec.1.1.symm ptt
  rcases this with ⟨L3, L4, speckle⟩
  simp at speckle
  right; right
  use L3, L4
  exact {down := by simp [spec.1, speckle.1]}

noncomputable def rg_of_rev_rel (d1) (gr : SemiThue grid_style (to_option a) b') (b'_is : remove_ones b' =
      e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b') (rel_holds : grid_style
      [(some c1, false), (some c2, true)] d1) : Σ b', SemiThue grid_style (to_option a) b' ×
      PLift (remove_ones b' = e ++ (remove_ones d1) ++ f) × irreducible b' := by
  have H1 : [(c1, false), (c2, true)].Infix' (remove_ones b') := by
    rw [b'_is]
    use e, f
    exact {down := rfl}
  rcases (pts_of_irr pt_b) b' (List.infix_refl_C b') c1 c2 H1 with ⟨w, t, hwt⟩
  rw [← hwt.1] at b'_is
  rw [remove_ones_append, remove_ones_append] at b'_is
  simp only [remove_ones] at b'_is
  have ptw : pts w := by
    rw [← hwt.1] at pt_b
    exact pts_chop_right (pts_chop_right (pts_of_irr pt_b))
  have ptt : pts t := by
    rw [← hwt.1, List.append_assoc] at pt_b
    exact pts_chop_left (pts_chop_left (pts_of_irr pt_b))
  rw [← hwt.1] at pt_b
  have := giant_list_split b'_is (irreducible_append (irreducible_append pt_b).1).1
    (irreducible_append pt_b).2
  rcases this with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
  · use move_ones (w ++ d1 ++ t)
    constructor
    · apply SemiThue.trans _ _ _ gr
      rw [← hwt.1]
      exact SemiThue.trans _ _ _ (SemiThue.reduction rel_holds) equiv_move_ones
    exact ⟨{down := by rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, h2.1.1,
        h2.1.2]}, irreducible_move_ones⟩
  · use move_ones (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
    constructor
    · apply SemiThue.trans _ _ _ gr
      rw [← hwt.1]
      have H : SemiThue grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t) := by
        apply SemiThue_append_right
        rw [hw.1.1]
        exact SemiThue_append_right (SemiThue_append_right (SemiThue_append_left
          (SemiThue_rel rel_holds)))
      apply H.trans _ _ _ equiv_move_ones
    constructor
    · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, hw.1.2.1, hw.1.2.2]
      exact {down := by simp [remove_ones, remove_ones_append]}
    exact irreducible_move_ones
  use move_ones (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
  constructor
  · apply SemiThue.trans _ _ _ gr
    rw [← hwt.1]
    have H : SemiThue grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2) := by
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
      apply SemiThue_append_left
      rw [List.append_assoc, List.append_assoc] at ht
      rw [ht.1.1]
      exact SemiThue_append_left
          (SemiThue_append_left (SemiThue_append_right (SemiThue_rel rel_holds)))
    exact H.trans _ _ _ equiv_move_ones
  constructor
  · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, ht.1.2.1, ht.1.2.2]
    exact {down := by simp [remove_ones, remove_ones_append]}
  exact irreducible_move_ones

noncomputable def rev_to_grid (h : SemiThue reversing a b) : Σ b', SemiThue grid_style (to_option a) b' × PLift
  (remove_ones b' = b) × irreducible b' := by
  have H := one_step_equiv_reg.1 h
  induction H with
  | refl a =>
    exact ⟨to_option a, (SemiThue.refl (to_option a), { down := remove_map_helper }, irr_to_option)⟩
  | one_step h1 h2 ih =>
    rename_i c d e f g
    rcases ih (one_step_equiv_reg.2 h1) with ⟨b', gr, b'_is, pt_b⟩
    cases h2 with
    | basic =>
      exact rg_of_rev_rel ([(none, true), (none, false)]) gr  b'_is.1 pt_b (.basic _)
    | apart h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, false)]) gr b'_is.1 pt_b (.apart h_dist)
    | close h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, true), (some j, false), (some i, false)]) gr b'_is.1 pt_b (.close h_dist)

def in_order_of_rm_irr (h : in_order (remove_ones L)) (h2 : irreducible L) : in_order L := by
  induction L
  · exact in_order_nil
  rename_i head tail ih
  have h_io : in_order (remove_ones tail) := by
    match head with
    | (none, _) =>
      simp [remove_ones] at h
      exact h
    | (some _, _) =>
      simp [remove_ones] at h
      exact in_order_rest h
  specialize ih h_io (irreducible_rest h2)
  rcases ih with ⟨a1, a2, ha⟩
  match head with
  | (none, true) =>
    use (none, true) :: a1, a2
    constructor
    · intro x hx
      simp at hx
      exact {down := by
                rcases hx.1 with h1 | h2
                · simp [h1]
                exact (ha.1 _ ⟨h2⟩).1}
    constructor
    · exact ha.2.1
    simp
    exact ha.2.2
  | (none, false) =>
    use [], (none, false) :: a2
    constructor
    · exact is_true_nil
    constructor
    · exact is_false_cons _ ha.2.1
    simp [ha.2.2.1]
    match a1 with
    | [] => exact ⟨rfl⟩
    | head :: tail1 =>
      exfalso
      match head with
      | (fst, false) =>
        simp [is_true] at ha
        have H := ha.1 (fst, false) ⟨List.mem_cons_self⟩
        simp at H
        exact H.1
      | (none, true) =>
        simp [remove_ones] at h
        simp [is_true] at ha
        rw [ha.2.2.1] at h2
        specialize h2 0
        have H := by
          apply h2.2.2
          use [], tail1 ++ a2
          exact {down := by simp}
        cases H
      | (some c, true) =>
        simp [remove_ones] at h
        simp [is_true] at ha
        rw [ha.2.2.1] at h2
        specialize h2 c
        have H := by
          apply h2.2.1
          use [], tail1 ++ a2
          exact {down := by simp}
        cases H
  | (some a, true) =>
    simp [remove_ones] at h
    use (some a, true) :: a1
    use a2
    constructor
    · intro x hx
      simp at hx
      exact {down := by
              rcases hx with h1 | h2
              · simp [h1]
              exact (ha.1 _ ⟨h2⟩).1}
    constructor
    · exact ha.2.1
    simp [ha.2.2.1]
    exact ⟨trivial⟩
  | (some a, false) =>
    simp [remove_ones] at h
    use []
    use (some a, false) :: a2
    constructor
    · exact is_true_nil
    constructor
    · exact is_false_cons _ ha.2.1
    simp [ha.2.2.1]
    match tail with
    | [] =>
      simp at ha
      exact ⟨ha.2.2.1.1⟩
    | (none, true) :: tail2 =>
      have H := by
        apply (h2 a).1
        use [], tail2
        exact {down := by simp}
      cases H
    | (_, false) :: tail2 =>
      match a1 with
      | [] => exact ⟨rfl⟩
      | (_, true) :: rest =>
        simp at ha
        exact ha.2.2.1.elim
      | (fst, false) :: rest =>
        simp [is_true] at ha
        have H := ha.1 (fst, false) ⟨List.mem_cons_self⟩
        simp at H
        exact H.1.elim
    | (some c, true) :: tail2 =>
      simp [remove_ones] at h
      change in_order ([(a, false), (c, true)] ++ _ ) at h
      apply in_order_append at h
      exfalso
      rcases h.1 with ⟨a3, a4, ha34⟩
      match a3 with
      | [] =>
        have H := ha34.2.2
        simp at H
        rw [← H.1] at ha34
        simp [is_false] at ha34
        exact ha34.2.1.1
      | head :: tail =>
        have H := ha34.2.2
        simp at H
        rw [← H.1.1] at ha34
        simp [is_true] at ha34
        have H := ha34.1 (a, false) ⟨List.mem_cons_self⟩
        simp at H
        apply H.1

noncomputable def stepOne_mid (h : SemiThue reversing a b) (ha : skeleton_order a) : Σ b', SemiThue grid_style (to_option a) b' ×
    skeleton_order (to_option a) ×  PLift (remove_ones b' = b) := by
  rcases rev_to_grid h with ⟨b', gr, b'_is, pt_b⟩
  use b'
  constructor
  · exact gr
  constructor
  · exact skeleton_to_option ha
  exact b'_is


noncomputable def stepOne (h : SemiThue reversing a b) (ha : skeleton_order a) (hb : in_order b) : Σ b', SemiThue grid_style (to_option a) b' ×
    skeleton_order (to_option a) × in_order b' × PLift (remove_ones b' = b) := by
  rcases rev_to_grid h with ⟨b', gr, b'_is, pt_b⟩
  use b'
  constructor
  · exact gr
  constructor
  · exact skeleton_to_option ha
  constructor
  · apply in_order_of_rm_irr _ pt_b
    rw [b'_is.1]
    exact hb
  exact b'_is
