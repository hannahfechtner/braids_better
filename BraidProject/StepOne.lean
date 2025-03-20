import BraidProject.SemiThue
import BraidProject.ListFact
import BraidProject.AlphabetRel

section toAdd

theorem infix_cons_ne (h : a :: b <:+: c :: d) (ne : a ≠ c) : a :: b <:+: d := by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp at hwt
    exact (ne hwt.1).elim
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    use tail, t
    exact hwt.2

theorem infix_cons_cons_ne_double (h : [a, b] <:+: c1 :: c2 :: d) (ne : b ≠ c2) : [a, b] <:+: c2 :: d := by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp at hwt
    exact (ne hwt.2.1).elim
  | cons head tail =>
    simp only [List.cons_append, List.cons.injEq] at hwt
    use tail, t
    exact hwt.2

theorem infix_cons_cons_def (h : [a, b] <:+: c :: d :: e) : a = c ∧ b =d ∨  [a, b] <:+: d :: e:= by
  rcases h with ⟨w, t, hwt⟩
  cases w with
  | nil =>
    simp at hwt
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
  simp at hwt
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

section anotherFile

def is_false (a : List (α × Bool)) := ∀ x ∈ a, x.2 = false

@[simp]
theorem is_false_nil : is_false ([] : List (α × Bool)) := by
  intro x hx
  simp at hx

theorem is_false_cons (a : List (α × Bool)) (h : is_false a): is_false ((b, false) :: a) := by
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h2
  · simp [h1]
  exact h _ h2

def is_true (a : List (α × Bool)) := ∀ x ∈ a, x.2 = true

@[simp]
theorem is_true_nil : is_true ([] : List (α × Bool)) := by
  intro x hx
  simp at hx

theorem is_true_cons (a : List (α × Bool)) (h : is_true a): is_true ((b, true) :: a) := by
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h2
  · simp [h1]
  exact h _ h2

def in_order (a : List (α × Bool)) := ∃ a1 a2, is_true a1 ∧ is_false a2 ∧ a = a1 ++ a2

theorem in_order_rest (h : in_order (head :: t)) : in_order t := by
  rcases h with ⟨a1, a2, ha⟩
  match a1 with
  | [] => match a2 with
    | [] => simp at ha
    | heada :: taila =>
      use [], taila
      constructor
      · exact ha.1
      constructor
      · exact fun _ hx => ha.2.1 _ (List.mem_cons_of_mem heada hx)
      simp only [is_true_nil, List.nil_append, List.cons.injEq, true_and] at ha
      simp [ha.2.2]
  | heada :: taila =>
    use taila, a2
    constructor
    · exact fun _ hx => ha.1 _ (List.mem_cons_of_mem heada hx)
    constructor
    · exact ha.2.1
    simp only [List.cons_append, List.cons.injEq] at ha
    exact ha.2.2.2

theorem in_order_of_true (h : is_true L) : in_order L := by
  use L, []
  constructor
  · exact h
  constructor
  · intro x hx
    simp at hx
  simp

theorem in_order_of_false (h : is_false L) : in_order L := by
  use [], L
  constructor
  · intro x hx
    simp at hx
  constructor
  · exact h
  simp

theorem in_order_append (h : in_order (a++b)) : in_order a ∧ in_order b := by
  rcases h with ⟨a1, a2, a1_true, a2_false, ha⟩
  rcases list_splits_somewhere ha with h1 | ⟨to_middle, spec⟩ | ⟨to_middle, spec⟩
  · rw [h1] at ha
    simp at ha
    rw [h1, ha]
    exact ⟨in_order_of_true a1_true, in_order_of_false a2_false⟩
  · constructor
    · rw [spec.1] at ha
      simp only [List.append_assoc, List.append_cancel_left_eq] at ha
      rw [spec.1]
      use a1, to_middle
      constructor
      · exact a1_true
      constructor
      · intro x hx
        apply a2_false
        rw [spec.2]
        exact List.mem_append_left _ hx
      rfl
    use [], b
    constructor
    · intro x hx
      simp at hx
    constructor
    · rw [spec.2] at a2_false
      exact fun _ hx => a2_false _ (List.mem_append_right to_middle hx)
    rfl
  constructor
  · use a, []
    constructor
    · intro x hx
      rw [← spec.1] at a1_true
      exact a1_true _ (List.mem_append_left to_middle hx)
    constructor
    · intro x hx
      simp at hx
    simp
  use to_middle, a2
  constructor
  · rw [← spec.1] at a1_true
    exact fun _ hx => a1_true _ (List.mem_append_right _ hx)
  exact ⟨a2_false, spec.right⟩

theorem in_order_nil {α} : in_order ([] : List (α × Bool)) := by use [], []; simp

end anotherFile

inductive reversing : List (ℕ × Bool) → List (ℕ × Bool) → Prop
| basic {n : ℕ} : reversing [(n, false), (n, true)] []
| apart {i j : ℕ} (h : Nat.dist i j > 1) : reversing [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : reversing [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

inductive grid_style : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Prop
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

theorem equiv_insert : SemiThue grid_style (a :: L) (insert_one a L) := by
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

theorem equiv_move_ones : SemiThue grid_style L (move_ones L) := by
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

def pairsTogether  (L : List (Option ℕ × Bool)) := ∀ a b, [(a, false), (b, true)] <:+: remove_ones L →
    [(some a, false), (some b, true)] <:+: L

theorem pairsTogether_empty : pairsTogether [] := by unfold pairsTogether; simp

theorem pairs_together_singleton : pairsTogether [a] := by
  intro c d hcd
  exfalso
  match a with
  | (none, _) =>
    change [(c, false), (d, true)] <:+: [] at hcd
    simp at hcd
  | (some a, b) =>
    change [(c, false), (d, true)] <:+: [(a, b)] at hcd
    rcases hcd with ⟨w, t, hwt⟩
    apply congr_arg List.length at hwt
    simp at hwt
    omega

def pts (L) := ∀ L1, L1 <:+: L → pairsTogether L1

theorem pts_empty : pts [] := by unfold pts; intro L1 hl; unfold pairsTogether; simp at hl; simp [hl]

theorem pts_chop_right (h : pts (a ++ b)) : pts a := fun L1 hl c d hcd ↦ h L1 (infix_append_right hl) c d hcd

theorem pts_chop_left (h : pts (a ++ b)) : pts b := fun L1 hl c d hcd ↦ h L1 (infix_append_left hl) c d hcd

def irreducible (L : List (Option ℕ × Bool)) :=
  ∀ a, ¬ [(some a, false), (none, true)] <:+: L ∧ ¬ [(none, false), (some a, true)] <:+: L ∧
   ¬ [(none, false), (none, true)] <:+: L

theorem irreducible_nil : irreducible [] := by simp [irreducible]

theorem irreducible_singleton : irreducible [a] := by
  simp [irreducible]
  intro a
  constructor
  · intro h
    apply infix_length_le at h
    simp at h
  constructor
  · intro h
    apply infix_length_le at h
    simp at h
  intro h
  apply infix_length_le at h
  simp at h

theorem irreducible_rest (h : irreducible (head :: tail)) : irreducible tail := by
  intro a
  constructor
  · intro h1
    specialize h a
    apply h.1
    exact List.infix_cons h1
  constructor
  · intro h1
    specialize h a
    apply h.2.1
    exact List.infix_cons h1
  intro h1
  specialize h a
  apply h.2.2
  exact List.infix_cons h1

theorem irreducible_concat (h : irreducible (L ++ [a])) : irreducible (L) := by
  intro a1
  specialize h a1
  constructor
  · intro h1
    apply h.1
    exact infix_append_right h1
  constructor
  · intro h1
    apply h.2.1
    exact infix_append_right h1
  intro h1
  apply h.2.2
  exact infix_append_right h1

theorem irreducible_append (h : irreducible (a ++ b)) : irreducible a ∧ irreducible b :=
  ⟨fun x ↦ ⟨fun hx ↦ (h x).1 (infix_append_right hx),
      ⟨fun hx ↦ (h x).2.1 (infix_append_right hx), fun hx ↦ (h x).2.2 (infix_append_right hx)⟩⟩,
  fun x ↦ ⟨fun hx ↦ (h x).1 (infix_append_left hx),
      ⟨fun hx ↦ (h x).2.1 (infix_append_left hx), fun hx ↦ (h x).2.2 (infix_append_left hx)⟩⟩⟩


theorem irreducible_cons_true (h : irreducible L) : irreducible ((a, true) :: L) := by
  intro a
  constructor
  · intro h1
    specialize h a
    apply h.1
    apply infix_cons_ne h1 (by simp)
  constructor
  · intro h1
    specialize h a
    apply h.2.1
    apply infix_cons_ne h1 (by simp)
  intro h1
  specialize h a
  apply h.2.2
  apply infix_cons_ne h1 (by simp)

theorem irreducible_two_cons (h : irreducible (b :: L)) (h1 : a.2 = b.2 ∨ a.2 = true ∨ (∃ c d, a.1 = some c ∧ b.1 = some d)) :
    irreducible (a :: b :: L) := by
  intro a1
  rcases h1 with h1 | h2 | ⟨c, d, hcd⟩
  · constructor
    · intro h2
      specialize h a1
      apply h.1
      match hb : a with
      | (_, true) =>
        apply infix_cons_ne h2
        simp [hb]
      | (_, false) =>
        match hbb : b with
        | (_, true) => simp at h1
        | (_, false) =>
          apply infix_cons_cons_ne_double h2
          simp
    constructor
    · intro h2
      specialize h a1
      apply h.2.1
      match hb : a with
      | (_, true) =>
        apply infix_cons_ne h2
        simp [hb]
      | (_, false) =>
        match b with
        | (_, true) => simp at h1
        | (_, false) =>
          apply infix_cons_cons_ne_double h2
          simp
    intro h2
    specialize h a1
    apply h.2.2
    match hb : a with
    | (_, true) =>
      apply infix_cons_ne h2
      simp [hb]
    | (_, false) =>
      match hbb : b with
      | (_, true) => simp at h1
      | (_, false) =>
        apply infix_cons_cons_ne_double h2
        simp
  · match a with
    | (fst, true) =>
      constructor
      · intro h3
        apply (h a1).1
        exact infix_cons_ne h3 (by simp)
      constructor
      · intro h3
        apply (h a1).2.1
        exact infix_cons_ne h3 (by simp)
      intro h3
      apply (h a1).2.2
      exact infix_cons_ne h3 (by simp)
    | (fst, false) => simp at h2
  match ha : a with
  | (some a2, true) =>
    match b with
    | (some b2, _) =>
      constructor
      · intro h3
        apply (h a1).1
        apply infix_cons_ne h3 (by simp)
      constructor
      · intro h3
        apply (h a1).2.1
        apply infix_cons_ne h3 (by simp)
      intro h3
      apply (h a1).2.2
      apply infix_cons_ne h3 (by simp)
    | (none, _) => simp at hcd
  | (some a2, false) =>
    match b with
    | (some b2, _) =>
      constructor
      · intro h3
        apply (h a1).1
        apply infix_cons_cons_ne_double h3 (by simp)
      constructor
      · intro h3
        apply (h a1).2.1
        apply infix_cons_ne h3 (by simp)
      intro h3
      apply (h a1).2.2
      apply infix_cons_ne h3 (by simp)
    | (none, _) => simp at hcd
  | (none, _) => simp at hcd

theorem irreducible_insert (h : irreducible L) : irreducible (insert_one a L) := by
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
        | [] => simp [irreducible_singleton]
        | (none, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_cons_true (ih _ _ m (irreducible_rest irr))
        | (none, false) :: tail =>
          simp only [insert_one]
          exact irreducible_two_cons irr (Or.inl (by rfl))
        | (some b, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_cons_true (ih _ _ m (irreducible_rest irr))
        | (some b, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr (Or.inl (by rfl))
      | (some b, true) =>
        match hl : L with
        | [] => simp [irreducible_singleton]
        | (none, true) :: tail =>
          simp only [insert_one]
          simp at m
          apply irreducible_two_cons
          · apply irreducible_cons_true
            exact irreducible_rest irr
          left; rfl
        | (none, false) :: tail =>
          simp only [insert_one]
          exact irreducible_two_cons irr (Or.inr (Or.inl (by rfl)))
        | (some b, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_two_cons irr (Or.inr (Or.inl (by rfl)))
        | (some b, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr
          right; left; rfl
      | (some c, false) =>
        match hl : L with
        | [] => simp [irreducible_singleton]
        | (none, true) :: tail =>
          simp only [insert_one]
          simp at m
          exact irreducible_cons_true (ih _ _ m (irreducible_rest irr))
        | (none, false) :: tail =>
          simp only [insert_one]
          exact irreducible_two_cons irr (Or.inl (by rfl))
        | (some b, true) :: tail =>
          simp only [insert_one]
          simp at m
          apply irreducible_two_cons irr
          right; right
          use c
          use b
        | (some b, false) :: tail =>
          simp only [insert_one]
          apply irreducible_two_cons irr (Or.inl (by rfl))
  exact H _ _ _ rfl h

theorem irreducible_move_ones : irreducible (move_ones L) := by
  induction L
  · simp [irreducible_nil]
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
      exfalso
      apply (h 0).2.2
      use [], tail
      rfl
    | (none, false) :: tail => simp only [insert_one]
    | (some b, true) :: tail =>
      simp only [insert_one]
      exfalso
      apply (h b).2.1
      use [], tail
      rfl
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
      exfalso
      apply (h c).1
      use [], tail
      rfl
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
        apply (irr 0).2.2
        use [], tail1
        simp
      | (none, false) :: tail1 =>
        simp [remove_ones] at hin
        specialize ih tail1 rest
        simp at len
        exact ih len (irreducible_rest irr) hin
      | (some b, true) :: tail1 =>
        apply (irr b).2.1
        use [], tail1
        simp
      | (some b, false) :: tail1 => simp [remove_ones] at hin
  exact H _ _ _ rfl h h2

theorem funky_helper (irr : irreducible ((none, false) :: L)) (hin : [(c, false), (d, true)] <:+: (b, false) :: remove_ones L) :
    [(c, false), (d, true)] <:+: remove_ones L := by
  match hl : remove_ones L with
  | [] =>
    rw [hl] at hin
    apply infix_length_le at hin
    simp at hin
  | (a, true) :: tail =>
    exact (irr_helper irr hl).elim
  | (a, false) :: tail =>
    rw [hl] at hin
    apply infix_cons_cons_ne_double at hin
    simp at hin
    exact hin

theorem pt_of_irr (h : irreducible L) : pairsTogether L := by
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
      apply infix_length_le at h
      simp at h
    | cons head tail =>
      match head with
      | (none, true) =>
        simp [remove_ones] at h
        simp at len
        exact List.infix_cons <| ih tail len (irreducible_rest irr) c d h
      | (none, false) =>
        match tail with
        | [] =>
          apply infix_length_le at h
          simp [remove_ones] at h
        | (none, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          exact ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) c d h
        | (none, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          exact ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) c d h
        | (some e, true) :: tail1 =>
          simp at len
          apply List.infix_cons
          apply ih ((some e, true) :: tail1) _ (irreducible_rest irr) _ _ h
          simp [len]
        | (some e, false) :: tail1 =>
          simp at len
          apply List.infix_cons
          apply ih ((some e, false) :: tail1) _ (irreducible_rest irr) _ _ h
          simp [len]
      | (some b, true) =>
        match tail with
        | [] =>
          apply infix_length_le at h
          simp [remove_ones] at h
        | (none, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          apply infix_cons_ne at h
          simp at h
          exact h
        | (none, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          apply infix_cons_ne at h
          simp [h]
        | (some e, true) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          apply ih tail1
          · omega
          apply irreducible_rest (irreducible_rest irr)
          apply infix_cons_ne at h
          simp at h
          apply infix_cons_ne at h
          simp [h]
        | (some c, false) :: tail1 =>
          simp [remove_ones] at h
          simp at len
          apply List.infix_cons
          apply ih ((some c, false) :: tail1)
          · simp [len]
          apply irreducible_rest irr
          apply infix_cons_ne at h
          simp at h
          exact h
      | (some b, false) =>
        match tail with
        | [] =>
          apply infix_length_le at h
          simp [remove_ones] at h
        | (none, true) :: tail1 =>
          simp at len
          apply List.infix_cons
          apply List.infix_cons
          apply (irr b).1.elim
          use [], tail1
          simp
        | (none, false) :: tail1 =>
          simp only [List.length_cons, add_le_add_iff_right] at len
          apply List.infix_cons <| List.infix_cons <| ih tail1 (by omega) (irreducible_rest (irreducible_rest irr)) _ _
            (funky_helper (irreducible_rest irr) h)
        | (some e, true) :: tail1 =>
          simp at len
          have H : (c = b ∧ e = d) ∨ (c ≠ b ∨ e ≠ d) := by
            rcases eq_or_ne c b with h1 | h2
            · rcases eq_or_ne e d with h3 | h4
              · left; simp [h1, h3]
              right; simp [h4]
            right; simp [h2]
          rcases H with h1 | h2 | h3
          · rw [h1.1, h1.2]
            use [], tail1
            simp
          · apply infix_cons_ne at h
            simp only [ne_eq, Prod.mk.injEq, h2, and_true, not_false_eq_true, forall_const] at h
            apply infix_cons_ne at h
            simp only [ne_eq, Prod.mk.injEq, Bool.false_eq_true, and_false, not_false_eq_true,
              forall_const] at h
            apply List.infix_cons <| List.infix_cons <| ih tail1 (by omega)
              (irreducible_rest (irreducible_rest irr)) _ _ h
          apply infix_cons_cons_ne_double at h
          simp only [ne_eq, Prod.mk.injEq, h3.symm, and_true, not_false_eq_true, forall_const] at h
          apply infix_cons_ne at h
          simp only [ne_eq, Prod.mk.injEq, Bool.false_eq_true, and_false, not_false_eq_true,
            forall_const] at h
          exact List.infix_cons <| List.infix_cons <| ih tail1 (by omega) (irreducible_rest
            (irreducible_rest irr)) _ _ h
        | (some e, false) :: tail1 =>
          simp at len
          apply List.infix_cons
          apply ih ((some e, false) :: tail1) (by simp [len]) (irreducible_rest irr)
          apply infix_cons_cons_ne_double at h
          simp at h
          exact h
  exact H L.length L (by simp) h

theorem irr_infix (h : irreducible L) (h2 : L1 <:+: L) : irreducible L1 :=
  fun a ↦ ⟨fun ha ↦ (h a).1 (ha.trans h2), ⟨fun ha ↦ (h a).2.1 (ha.trans h2), fun ha ↦
        (h a).2.2 (ha.trans h2)⟩⟩

theorem pts_of_irr (h : irreducible L) : pts L := fun _ hl ↦ pt_of_irr (irr_infix h hl)

def to_option (L : List (ℕ × Bool)) : List (Option ℕ × Bool) := (List.map (fun x ↦ (some x.1, x.2)) L)

theorem remove_map_helper {a : List (ℕ × Bool)} : remove_ones (to_option a) = a := by
  induction a
  · rfl
  rename_i ih
  simp [to_option, remove_ones]
  exact ih

theorem pt_to_option : pairsTogether (to_option c) := by
  intro a b hab
  simp [remove_map_helper] at hab
  rcases hab with ⟨w, t, hwt⟩
  use to_option w
  use to_option t
  rw [← hwt]
  simp [to_option]

theorem pts_to_option : pts (to_option a) := by
  have H : irreducible (to_option a) := by
    intro c
    constructor
    · intro h
      induction a
      · simp [to_option] at h
      rename_i ha ta iha
      apply iha
      match ta with
      | [] =>
        simp [to_option] at h
        apply infix_length_le at h
        simp at h
      | t :: taa =>
        simp [to_option] at h
        apply infix_cons_cons_ne_double at h
        simp at h
        exact h
    constructor
    · intro h
      induction a
      · simp [to_option] at h
      rename_i ha ta iha
      apply iha
      simp [to_option] at h
      apply infix_cons_ne at h
      simp at h
      exact h
    intro h
    induction a
    · simp [to_option] at h
    rename_i ha ta iha
    apply iha
    simp [to_option] at h
    apply infix_cons_ne at h
    simp at h
    exact h
  exact pts_of_irr H

theorem irr_to_option : irreducible (to_option a) := by
  induction a with
  | nil => simp [to_option, irreducible_nil]
  | cons head tail ih =>
    simp [to_option]
    intro x
    constructor
    · intro hx
      match tail with
      | [] =>
        apply infix_length_le at hx
        simp at hx
      | t1 :: tr =>
        apply infix_cons_cons_ne_double at hx
        simp only [ne_eq, Prod.mk.injEq, reduceCtorEq, Bool.true_eq, false_and, not_false_eq_true,
          forall_const] at hx
        exact (ih x).1 hx
    constructor
    · intro hx
      apply infix_cons_ne at hx
      simp at hx
      exact (ih x).2.1 hx
    intro hx
    apply infix_cons_ne at hx
    simp at hx
    exact (ih x).2.2 hx

theorem five_cases (b_ne : b1 ≠ b2) (h : a ++ [b1, b2] ++ c = d ++ [b1, b2] ++ e) :
  (a = d ∧ c = e) ∨ (∃ a1 a2, a = a1 ++ [b1, b2] ++ a2 ∧ d = a1 ∧ e = a2 ++ [b1, b2] ++ c) ∨
  (∃ c1 c2, c = c1 ++ [b1, b2] ++ c2 ∧ d = a ++ [b1, b2] ++ c1 ∧ e = c2) := by
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
      simp
      apply b_ne
      rw [h.2.1]
    | d1 :: d2 :: dr =>
      simp at h
      simp [h.1]
      constructor
      · rw [← h.1]
        exact h.2.2
      exact h.2.1.symm
  rename_i a1 ar ih
  match d with
  | [] =>
    simp at h
    simp [h.1, h.2]
    use []
    simp
    match ar with
    | [] => simp [b_ne] at h
    | a2 :: arr =>
      simp at h
      use arr
      simp [h.2.1, h.2.2]
  | d1 :: [] =>
    simp at h
    simp [h.1]
    match ar with
    | [] => left; simp at h; exact ⟨rfl, h.2⟩
    | a2 :: a3 :: arr =>
      simp at h
      simp
      use [d1]
      simp [h.1, h.2.1]
      use arr
      simp [h.2.1, h.2.2]
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
      exact h1
    · rcases h2 with ⟨a1', a2', spec⟩
      right; left
      use d1 :: a1'
      use a2'
      simp [spec.1, spec.2]
    rcases h3 with ⟨c1', c2', spec⟩
    right; right
    use c1'
    simp [spec.1, spec.2]

theorem irreducible_none_false_swap (b) (h : irreducible ((none, false) :: L)) : irreducible ((b, false) :: L) := by
  match L with
  | [] => exact irreducible_singleton
  | (some c, true) :: tail =>
    specialize h c
    apply h.2.1.elim
    use [], tail
    simp
  | (some c, false) :: tail =>
    intro a
    constructor
    · intro h1
      apply infix_cons_cons_ne_double at h1
      simp at h1
      apply (irreducible_rest h a).1 h1
    constructor
    · intro h1
      apply infix_cons_cons_ne_double at h1
      simp at h1
      apply (irreducible_rest h a).2.1 h1
    intro h1
    apply infix_cons_cons_ne_double at h1
    simp at h1
    apply (irreducible_rest h a).2.2 h1
  | (none, true) :: tail =>
    specialize h 0
    apply h.2.2.elim
    use [], tail
    simp
  | (none, false) :: tail =>
    intro a
    constructor
    · intro h1
      apply infix_cons_cons_ne_double at h1
      simp at h1
      apply (irreducible_rest h a).1 h1
    constructor
    · intro h1
      apply infix_cons_cons_ne_double at h1
      simp at h1
      apply (irreducible_rest h a).2.1 h1
    intro h1
    apply infix_cons_cons_ne_double at h1
    simp at h1
    apply (irreducible_rest h a).2.2 h1

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
    apply h.1
    use []
    use tail ++ [(some e, true)]
    simp
  | (none, false) =>
    specialize ih (irreducible_none_false_swap _ (irreducible_rest h)) H
    rw [ih] at h
    specialize h e
    apply h.2.1
    use [(some d, false)], []
    simp

theorem helper4 (hi : irreducible ((some d, false) :: L)) (h : [(b2, true)] = remove_ones L) :
    ∃ L2, L = (some b2, true) :: L2 ∧ remove_ones L2 = [] := by
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
    simp [spec.1, spec.2, remove_ones]
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

theorem helper3 (h : [(b1, false), (b2, true)] = remove_ones L) (hi : irreducible L) :
    ∃ L1 L2, L = L1 ++ [(some b1, false), (some b2, true)] ++ L2 ∧
    [] = remove_ones L1 ∧ [] = remove_ones L2 := by
  induction L
  · simp at h
  rename_i head tail ih
  match head with
  | (none, snd) =>
    simp [remove_ones] at h
    specialize ih h (irreducible_rest hi)
    rcases ih with ⟨L3, L4, spec⟩
    use (none, snd) :: L3, L4
    constructor
    · rw [spec.1]
      simp
    exact spec.2
  | (some d, snd) =>
    simp [remove_ones] at h
    simp [h.1]
    use []
    simp
    rw [h.1.2] at hi
    exact helper4 hi h.2

theorem helper2 (h : [(b1, false), (b2, true)] ++ c = remove_ones L)(hi : irreducible L) :
    ∃ L1 L2, L = L1 ++ [(some b1, false), (some b2, true)] ++ L2 ∧ [] = remove_ones L1 ∧ c = remove_ones L2 := by
  induction L using List.reverseRecOn generalizing c
  · simp at h
  rename_i train caboose ih
  match caboose with
  | (none, snd) =>
    simp only [remove_ones_append, remove_ones, List.append_nil] at h
    have := ih h (irreducible_concat hi)
    rcases this with ⟨L3, L4, spec⟩
    use L3, L4 ++ [(none, snd)]
    constructor
    · simp [spec.1]
    constructor
    · exact spec.2.1
    simp [remove_ones, spec.2.2]
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
    simp [spec.1, spec.2, h, remove_ones]
    exact (List.concat_inj.mp h).2

theorem helper (h : a ++ [(b1, false), (b2, true)] ++ c = remove_ones L)(hi : irreducible L) :
    ∃ L1 L2, L = L1 ++ [(some b1, false), (some b2, true)] ++ L2 ∧ a = remove_ones L1 ∧ c = remove_ones L2 := by
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
    simp [spec.1, spec.2, remove_ones]
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
      simp [spec.1, spec.2, h.1, remove_ones]


theorem giant_list_split {w : List (Option ℕ × Bool)} (h : remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t =
    e ++ [(c1, false), (c2, true)] ++ f) (ptw : irreducible w) (ptt : irreducible t) : (remove_ones w = e ∧ remove_ones t = f) ∨
    (∃ w1 w2, w = w1 ++ [(some c1, false), (some c2, true)] ++ w2 ∧ e = remove_ones w1 ∧
    f = remove_ones w2 ++ [(c1, false), (c2, true)] ++ remove_ones t) ∨
    (∃ t1 t2, t = t1 ++ [(some c1, false), (some c2, true)] ++ t2 ∧
    e = remove_ones w ++ [(c1, false), (c2, true)] ++ remove_ones t1 ∧ f = remove_ones t2) := by
  rcases five_cases (by simp) h with h1 | h2 | h3
  · left; exact h1
  · rcases h2 with ⟨a1, a2, spec⟩
    have := helper spec.1.symm ptw
    rcases this with ⟨L3, L4, speckle⟩
    simp at speckle
    right; left
    use L3, L4
    simp [spec, speckle]
  rcases h3 with ⟨a1, a2, spec⟩
  have := helper spec.1.symm ptt
  rcases this with ⟨L3, L4, speckle⟩
  simp at speckle
  right; right
  use L3, L4
  simp [spec, speckle]

theorem rg_of_rev_rel (d1) (gr : SemiThue grid_style (to_option a) b') (b'_is : remove_ones b' =
      e ++ [(c1, false), (c2, true)] ++ f) (pt_b : irreducible b') (rel_holds : grid_style
      [(some c1, false), (some c2, true)] d1) : ∃ b', SemiThue grid_style (to_option a) b' ∧
      remove_ones b' = e ++ (remove_ones d1) ++ f ∧ irreducible b' := by
  rcases (pts_of_irr pt_b) b' (List.infix_refl b') c1 c2 (.intro e (.intro f b'_is.symm))
    with ⟨w, t, hwt⟩
  rw [← hwt] at b'_is
  rw [remove_ones_append, remove_ones_append] at b'_is
  simp only [remove_ones] at b'_is
  have ptw : pts w := by
    rw [← hwt] at pt_b
    exact pts_chop_right (pts_chop_right (pts_of_irr pt_b))
  have ptt : pts t := by
    rw [← hwt, List.append_assoc] at pt_b
    exact pts_chop_left (pts_chop_left (pts_of_irr pt_b))
  rw [← hwt] at pt_b
  have := giant_list_split b'_is (irreducible_append (irreducible_append pt_b).1).1
    (irreducible_append pt_b).2
  rcases this with h2 | ⟨w1, w2, hw⟩ | ⟨t1, t2, ht⟩
  · use move_ones (w ++ d1 ++ t)
    constructor
    · apply SemiThue.trans _ _ _ gr
      rw [← hwt]
      exact SemiThue.trans _ _ _ (SemiThue.reduction rel_holds) equiv_move_ones
    exact ⟨by rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, h2.1,
        h2.2], irreducible_move_ones⟩
  · use move_ones (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t)
    constructor
    · apply SemiThue.trans _ _ _ gr
      rw [← hwt]
      have H : SemiThue grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w1 ++ d1 ++ w2 ++ [(some c1, false), (some c2, true)] ++ t) := by
        apply SemiThue_append_right
        rw [hw.1]
        exact SemiThue_append_right (SemiThue_append_right (SemiThue_append_left
          (SemiThue_rel rel_holds)))
      apply H.trans _ _ _ equiv_move_ones
    constructor
    · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, hw.2.1, hw.2.2]
      simp [remove_ones, remove_ones_append]
    exact irreducible_move_ones
  use move_ones (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2)
  constructor
  · apply SemiThue.trans _ _ _ gr
    rw [← hwt]
    have H : SemiThue grid_style (w ++ [(some c1, false), (some c2, true)] ++ t)
        (w ++ [(some c1, false), (some c2, true)] ++ t1 ++ d1 ++ t2) := by
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
      apply SemiThue_append_left
      rw [List.append_assoc, List.append_assoc] at ht
      rw [ht.1]
      exact SemiThue_append_left
          (SemiThue_append_left (SemiThue_append_right (SemiThue_rel rel_holds)))
    exact H.trans _ _ _ equiv_move_ones
  constructor
  · rw [remove_ones_move_ones, remove_ones_append, remove_ones_append, ht.2.1, ht.2.2]
    simp [remove_ones, remove_ones_append]
  exact irreducible_move_ones

theorem rev_to_grid (h : SemiThue reversing a b) : ∃ b', SemiThue grid_style (to_option a) b' ∧
  remove_ones b' = b ∧ irreducible b':= by
  induction one_step_equiv_reg.mp h with
  | refl a => exact .intro (to_option a) ⟨.refl _, ⟨remove_map_helper, irr_to_option⟩⟩
  | one_step h1 h2 ih =>
    rename_i c d e f g
    rcases ih (one_step_equiv_reg.mpr h1) with ⟨b', gr, b'_is, pt_b⟩
    cases h2 with
    | basic =>
      exact rg_of_rev_rel ([(none, true), (none, false)]) gr  b'_is pt_b (.basic _)
    | apart h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, false)]) gr b'_is pt_b (.apart h_dist)
    | close h_dist =>
      rename_i i j
      exact rg_of_rev_rel ([(some j, true), (some i, true), (some j, false), (some i, false)]) gr b'_is pt_b (.close h_dist)

theorem in_order_of_rm_irr (h : in_order (remove_ones L)) (h2 : irreducible L) : in_order L := by
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
      rcases hx with h1 | h2
      · simp [h1]
      exact ha.1 _ h2
    constructor
    · exact ha.2.1
    simp [ha.2.2]
  | (none, false) =>
    use [], (none, false) :: a2
    constructor
    · intro x hx
      simp at hx
    constructor
    · exact is_false_cons _ ha.2.1
    simp [ha.2.2]
    match a1 with
    | [] => rfl
    | head :: tail1 =>
      exfalso
      match head with
      | (_, false) => simp [is_true] at ha
      | (none, true) =>
        simp [remove_ones] at h
        simp [is_true] at ha
        rw [ha.2.2] at h2
        specialize h2 0
        apply h2.2.2
        use [], tail1 ++ a2
        simp
      | (some c, true) =>
        simp [remove_ones] at h
        simp [is_true] at ha
        rw [ha.2.2] at h2
        specialize h2 c
        apply h2.2.1
        use [], tail1 ++ a2
        simp
  | (some a, true) =>
    simp [remove_ones] at h
    use (some a, true) :: a1
    use a2
    constructor
    · intro x hx
      simp at hx
      rcases hx with h1 | h2
      · simp [h1]
      exact ha.1 _ h2
    constructor
    · exact ha.2.1
    simp [ha.2.2]
  | (some a, false) =>
    simp [remove_ones] at h
    use []
    use (some a, false) :: a2
    constructor
    · intro x hx
      simp at hx
    constructor
    · exact is_false_cons _ ha.2.1
    simp [ha.2.2]
    match tail with
    | [] =>
      simp at ha
      exact ha.2.2.1
    | (none, true) :: tail2 =>
      apply (h2 a).1.elim
      use [], tail2
      simp
    | (_, false) :: tail2 =>
      match a1 with
      | [] => rfl
      | (_, true) :: rest => simp at ha
      | (_, false) :: rest => simp [is_true] at ha
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
        rw [← H] at ha34
        simp [is_false] at ha34
      | head :: tail =>
        have H := ha34.2.2
        simp at H
        rw [← H.1] at ha34
        simp [is_true] at ha34

theorem stepOne (h : SemiThue reversing a b) (hb : in_order b) : ∃ b', SemiThue grid_style (to_option a) b' ∧
    in_order b' := by
  rcases rev_to_grid h with ⟨b', gr, b'_is, pt_b⟩
  use b'
  constructor
  · exact gr
  apply in_order_of_rm_irr _ pt_b
  rw [b'_is]
  exact hb
