import Mathlib.Data.List.Basic
import BraidProject.ListFact

def is_false (a : List (α × Bool)) := ∀ x ∈ a, x.2 = false

@[simp]
theorem is_false_nil : is_false ([] : List (α × Bool)) := by simp [is_false]

theorem is_false_append (h : is_false (a ++ b)) : is_false a ∧ is_false b := by
  constructor
  · exact fun x hx => h x (List.mem_append_left b hx)
  exact fun x hx => h x (List.mem_append_right a hx)

def is_true (a : List (α × Bool)) := ∀ x ∈ a, x.2 = true

theorem is_false_of_false_false (h1 : is_false a) (h2 : is_false b) : is_false (a ++ b) := by
  intro x h
  simp at h
  cases h with
  | inl h => exact h1 x h
  | inr h => exact h2 x h

@[simp]
theorem is_true_nil : is_true ([] : List (α × Bool)) := by simp [is_true]

theorem is_true_append (h : is_true (a ++ b)) : is_true a ∧ is_true b := by
  constructor
  · exact fun x hx => h x (List.mem_append_left b hx)
  exact fun x hx => h x (List.mem_append_right a hx)

theorem is_true_of_true_true (h1 : is_true a) (h2 : is_true b) : is_true (a ++ b) := by
  intro x h
  simp at h
  cases h with
  | inl h => exact h1 x h
  | inr h => exact h2 x h


theorem is_false_cons (a : List (α × Bool)) (h : is_false a): is_false ((b, false) :: a) := by
  intro x hx
  rcases List.mem_cons.mp hx with h1 | h2
  · simp [h1]
  exact h _ h2

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

def skeleton_order (a : List (α × Bool)) := ∃ a1 a2, is_false a1 ∧ is_true a2 ∧ a = a1 ++ a2

theorem skeleton_order_nil {α} : skeleton_order ([] : List (α × Bool)) := by use [], []; simp

def to_up (a : List ℕ) : List (Option ℕ × Bool) :=
  match a with
  | [] => [(none, false)]
  | _ => List.map (fun x => (some x, false)) a.reverse

def to_over (a : List ℕ) : List (Option ℕ × Bool) :=
  match a with
  | [] => [(none, true)]
  | _ => List.map (fun x => (some x, true)) a

def remover : (a : List (Option α × Bool)) → List α
  | [] => []
  | (some a, _) :: c => a :: remover c
  | (none, _) :: c => remover c

@[simp]
theorem to_up_nil : to_up [] = [(none, false)] := rfl

@[simp]
theorem to_up_singleton (a : ℕ) : to_up [a] = [(some a, false)] := rfl

@[simp]
theorem to_up_pair (a : ℕ) : to_up [a, b] = [(some b, false), (some a, false)] := rfl

@[simp]
theorem to_up_cons_cons : to_up (a :: b :: c) = to_up (b :: c) ++ [(some a, false)] := by
  simp [to_up]

theorem to_up_len_pos : (to_up a).length > 0 := by
  induction a
  · simp
  rename_i h t ht
  simp
  cases t
  · simp
  simp

@[simp]
theorem to_over_nil : to_over [] = [(none, true)] := rfl

@[simp]
theorem to_over_singleton (a : ℕ) : to_over [a] = [(some a, true)] := rfl

@[simp]
theorem to_over_pair (a : ℕ) : to_over [a, b] = [(some a, true), (some b, true)] := rfl

@[simp]
theorem to_over_cons_cons : to_over (a :: b :: c) = (some a, true) :: to_over (b :: c):= by
  simp [to_over]

theorem to_over_len_pos : (to_over a).length > 0 := by
  induction a
  · simp
  rename_i h t ht
  simp
  cases t
  · simp
  simp

theorem to_over_eq_cons (c) : ∃ a b, to_over c = (a, true) :: b := by
  induction c
  · use none, []
    rfl
  rename_i h t ht
  cases t
  · use some h, []
    rfl
  simp

theorem to_over_options (c) : (∃ a, to_over c = [(a, true)]) ∨ ∃ a b, to_over c = (some a, true) :: (to_over b) := by
  induction c
  · simp
  rename_i h t ht
  cases t
  · simp
  simp

theorem remover_mul : remover ((some a, bo) :: b) = a :: remover b := rfl

theorem remover_none : remover ((none, bo) :: b) = remover b := rfl

theorem remover_split : ∀ b, remover (a ++ b) = remover a ++ remover b := by
  induction a
  · exact fun _ => rfl
  intro b
  rename_i h t ht
  rcases h with a | b
  · change remover (_ :: _) = remover (_ :: _) ++ _
    rw [remover_none, remover_none]
    exact ht _
  change remover (_ :: _) = remover (_ :: _) ++ _
  rw [remover_mul, remover_mul]
  rename_i bb _
  simp only [List.append_eq, List.cons_append, List.cons.injEq, true_and]
  exact ht _

@[simp]
theorem remover_up : remover (to_up a) = a.reverse := by
  induction a
  · rfl
  rename_i a b hb
  unfold to_up
  simp only [List.reverse_cons, List.map_append, List.map_reverse, List.map_cons, List.map_nil]
  rw [remover_split]
  cases b with
  | nil =>
    simp [remover, List.nil_append]
  | cons head tail =>
    simp [remover]
    simp [remover, to_up] at hb
    rw [hb]
    simp

@[simp]
theorem remover_up_rev : remover (to_up a).reverse = a := by
  unfold remover
  unfold to_up
  induction a
  · simp [remover]
  rename_i tail ih
  cases tail
  · simp [remover]
  simp
  simp at ih
  rename_i head tailly
  rw [remover_mul]
  simp
  exact ih

@[simp]
theorem remover_over : remover (to_over a) = a := by
  induction a
  · rfl
  rename_i a b hb
  unfold to_over
  simp
  rw [remover_mul]
  simp only [List.cons.injEq, true_and]
  cases b with
  | nil =>
    simp [remover]
  | cons head tail =>
    exact hb

theorem is_false_up : is_false (to_up a) := by
  unfold to_up
  cases a with
  | nil =>
    simp [is_false]
  | cons head tail =>
    simp [is_false]

theorem is_true_over : is_true (to_over a) := by
  unfold to_over
  cases a with
  | nil =>
    simp [is_true]
  | cons head tail =>
    simp [is_true]


theorem over_up_neq_false_true (h : to_over d ++ to_up c = k ++ [(a1, false), (b1, true)] ++ l) : False := by
  induction k generalizing d with
  | nil =>
    rw [List.nil_append] at h
    have H : List.get? (to_over d ++ to_up c) 0 = List.get? ([(a1, false), (b1, true)] ++ l) 0 := by
      rw [h]
    rcases to_over_eq_cons d with ⟨w, w2, hw⟩
    rw [hw] at H
    simp at H
  | cons head tail ih =>
    rcases to_over_options d with h1 | h2
    · rcases h1 with ⟨a3, h3⟩
      rw [h3] at h
      simp at h
      have H : is_false (tail ++ (a1, false) :: (b1, true) :: l) := by
        rw [← h.2]
        exact is_false_up
      have b1_in : (b1, true) ∈ tail ++ (a1, false) :: (b1, true) :: l  := by
        simp
      have H2 := H (b1, true) b1_in
      simp at H2
    rcases h2 with ⟨a3, b3, h3⟩
    rw [h3] at h
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.cons.injEq] at h
    simp only [List.append_assoc, List.cons_append, List.singleton_append, imp_false] at ih
    exact ih h.2

def option_to_cell (a : Option ℕ) : List ℕ :=
  match a with
  | none => []
  | some b => [b]

theorem over_oc : to_over (option_to_cell b1) = [(b1, true)] := by
  cases b1 with
  | none => rfl
  | some val => rfl

theorem up_oc : to_up (option_to_cell a1) = [(a1, false)] := by
  cases a1 with
  | none => rfl
  | some val => rfl


theorem bool_change_second (h : a.length > 0) (h1 : is_false a) (h3 : a ++ b = [(a1, false), (b1, true)]) :
    a = [(a1, false)]  := by
  have H : a.length = 1 := by
    have h2 : ¬ a.length > 2 := by
        intro h
        apply congr_arg List.length at h3
        simp at h3
        omega
    have H : ¬ a.length = 2 := by
      intro h
      have H : b = [] := by
        apply congr_arg List.length at h3
        simp only [List.length_append, List.length_cons, List.length_singleton, Nat.succ_eq_add_one,
          Nat.reduceAdd] at h3
        rw [h] at h3
        exact List.length_eq_zero_iff.mp (Nat.add_eq_left.mp h3)
      rw [H, List.append_nil] at h3
      rw [h3] at h1
      simp only [is_false, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq,
        Bool.true_eq_false, and_false, List.not_mem_nil, false_implies, implies_true, and_true,
        and_false] at h1
    omega
  change a ++ b = [(a1, false)] ++ [(b1, true)] at h3
  exact (List.append_inj_left h3.symm H.symm).symm

theorem bool_change_first (h : b.length > 0) (h1 : is_true b) (h3 : a ++ b = [(a1, false), (b1, true)]) :
    b = [(b1, true)]  := by
  have H : b.length = 1 := by
    have h2 : ¬ b.length > 2 := by
        intro h
        apply congr_arg List.length at h3
        simp at h3
        omega
    have H : ¬ b.length = 2 := by
      intro h
      have H : a = [] := by
        apply congr_arg List.length at h3
        simp only [List.length_append, List.length_cons, List.length_singleton, Nat.succ_eq_add_one,
          Nat.reduceAdd] at h3
        rw [h] at h3
        simp only [List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.add_left_eq_self,
          List.length_eq_zero_iff] at h3
        exact h3
      rw [H, List.nil_append] at h3
      rw [h3] at h1
      simp [is_true] at h1
    omega
  change a ++ b = [(a1, false)] ++ [(b1, true)] at h3
  exact (List.append_inj_right' h3.symm H.symm).symm


theorem bool_split (ha : is_false a2) (hb : is_true b1) (h : [(a3, false), (b3, true)] = a2 ++ b1) :
    a2 = [(a3, false)] ∧ b1 = [(b3, true)] := by
  have H : a2.length = 1 := by
    have H1 : ¬ a2.length = 0 := by
      intro h1
      simp at h1
      rw [h1, List.nil_append] at h
      rw [← h] at hb
      simp [is_true] at hb
    have H2 : ¬ a2.length = 2 := by
      intro h1
      have h2 := congr_arg List.length h
      simp only [List.length_cons, List.length_singleton, Nat.succ_eq_add_one, Nat.reduceAdd,
        List.length_append] at h2
      rw [h1] at h2
      simp at h2
      rw [h2, List.append_nil] at h
      rw [← h] at ha
      simp [is_false] at ha
    have H3 : ¬ a2.length > 2 := by
      intro h1
      apply congr_arg List.length at h
      simp only [List.length_cons, List.length_singleton, Nat.succ_eq_add_one, Nat.reduceAdd,
        List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
      omega
    omega
  exact List.append_inj h.symm H

theorem is_true_split (h : is_true (a :: b)) : is_true [a] ∧ is_true b := by
  change is_true ([a]++b) at h
  exact is_true_append h

theorem is_false_split (h : is_false (a :: b)) : is_false [a] ∧ is_false b := by
  change is_false ([a]++b) at h
  exact is_false_append h

theorem is_true_singleton (h : is_true [a]) : ∃ a', a = (a', true) := by
  rcases a with ⟨c, b⟩
  use c
  simp
  specialize h (c, b) (List.mem_singleton.mpr rfl)
  exact h

theorem is_false_singleton (h : is_false [a]) : ∃ a', a = (a', false) := by
  rcases a with ⟨c, b⟩
  use c
  simp
  specialize h (c, b) (List.mem_singleton.mpr rfl)
  exact h


theorem prefix_true (h1 : is_true bot3) (h : k₂ ++ [(a1, false), (b1, true)] ++ l = bot3 ++ mid3 ++ up3) :
    bot3 <+: k₂ := by
  induction k₂ generalizing bot3 with
  | nil =>
    cases bot3 with
    | nil => exact List.nil_prefix
    | cons head tail =>
      simp at h
      rw [← h.1] at h1
      simp [is_true] at h1
  | cons head tail ih =>
    cases bot3 with
    | nil => exact List.nil_prefix
    | cons head1 tail1 =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      specialize @ih tail1 (is_true_split h1).2 h.2
      rw [h.1]
      exact (List.prefix_cons_inj head1).mpr ih

theorem prefix_false (h1 : is_false t3) (h : tk ++ [(a1, false), (b1, true)] ++ l =
    t3 ++ (f, false) :: (m ++ [(c, true)]) ++ up3) : t3 <+: tk := by
  induction tk generalizing t3 with
  | nil =>
    cases t3 with
    | nil => exact List.nil_prefix
    | cons head tail =>
      cases tail with
      | nil =>
        simp at h
      | cons ht tt =>
        simp at h
        rw [← h.2.1] at h1
        simp [is_false] at h1
  | cons head tail ih =>
    cases t3 with
    | nil =>
      exact List.nil_prefix
    | cons ht tt =>
      simp at h
      specialize @ih tt (is_false_split h1).2 (by simp [h.2])
      rw [h.1]
      exact (List.prefix_cons_inj ht).mpr ih
