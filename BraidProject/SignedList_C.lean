import BraidProject.List_C
import BraidProject.SignedList

namespace SignedList

def is_false_singleton (h : is_false [a]) : Σ a', PLift (a = (a', false)) := by
  rcases a with ⟨c, b⟩
  use c
  simp only [Prod.mk.injEq, true_and]
  constructor
  exact h (c, b) (List.mem_singleton.mpr rfl)


def is_true_singleton (h : is_true [a]) : Σ a', PLift (a = (a', true)) := by
  rcases a with ⟨c, b⟩
  use c
  simp
  specialize h (c, b) (List.mem_singleton.mpr rfl)
  constructor
  exact h

def PosNegData (a : List (α × Bool)) := Σ a1 a2, PLift (is_true a1 ∧ is_false a2 ∧ a = a1 ++ a2)

def PosNegData.nil {α} : PosNegData ([] : List (α × Bool)) := by use [], []; simp; exact ⟨trivial⟩

def PosNegData.singleton : PosNegData ([a]) := by
  match a with
  | (a1, false) => use [], [(a1,false)]; simp [is_false]; constructor; trivial
  | (a1, true) => use [(a1, true)], []; simp [is_true]; constructor; trivial

def PosNegData.of_true (h : is_true L) : PosNegData L := by
  use L, []
  exact ⟨⟨h, ⟨is_false_nil,(List.append_nil L).symm⟩⟩⟩

def PosNegData.of_false (h : is_false L) : PosNegData L := by
  use [], L
  exact ⟨⟨is_true_nil, ⟨h, rfl⟩⟩⟩

def PosNegData.tail (h : PosNegData (head :: t)) : PosNegData t := by
  rcases h with ⟨a1, a2, ha⟩
  match a1 with
  | [] => match a2 with
    | [] =>
      simp only [is_true_nil, is_false_nil, List.append_nil, reduceCtorEq, and_false] at ha
      exact ha.1.elim
    | heada :: taila =>
      apply PosNegData.of_false
      apply (@is_false_tail _ head)
      rw [ha.1.2.2, List.nil_append]
      exact ha.1.2.1
  | heada :: taila =>
    use taila, a2
    constructor
    constructor
    · intro _ hx
      apply ha.1.1 _ (List.mem_cons_of_mem heada hx)
    constructor
    · exact ha.1.2.1
    simp only [List.cons_append, List.cons.injEq] at ha
    rw [ha.1.2.2.2]

noncomputable def PosNegData.of_append (h : PosNegData (a++b)) : PosNegData a × PosNegData b := by
  rcases h with ⟨a1, a2, a1_true, a2_false, ha⟩
  rcases ListC.append_eq_append ha with ⟨to_middle, ⟨spec⟩⟩ | ⟨to_middle, ⟨spec⟩⟩
  · constructor
    · rw [spec.1] at ha
      simp only [List.append_assoc, List.append_cancel_left_eq] at ha
      rw [spec.1]
      use a1, to_middle
      constructor
      constructor
      · exact a1_true
      constructor
      · rw [← ha] at a2_false
        exact (is_false_of_append a2_false).1
      rfl
    apply PosNegData.of_false
    rw [spec.2] at a2_false
    exact (is_false_of_append a2_false).2
  constructor
  · apply PosNegData.of_true
    rw [← spec.1] at a1_true
    exact (is_true_of_append a1_true).1
  use to_middle, a2
  constructor
  constructor
  · rw [← spec.1] at a1_true
    exact fun _ hx => a1_true _ (List.mem_append_right _ hx)
  exact ⟨a2_false, spec.right⟩

def NegPosData (a : List (α × Bool)) := Σ a1 a2, PLift (is_false a1 ∧ is_true a2 ∧ a = a1 ++ a2)

def NegPosData.nil {α} : NegPosData ([] : List (α × Bool)) := by
  use [], []
  exact ⟨⟨is_false_nil, is_true_nil, rfl⟩⟩

def NegPosData.singleton : NegPosData ([a]) := by
  match a with
  | (a1, false) => use [(a1,false)], []; simp [is_false]; constructor; trivial
  | (a1, true) => use [], [(a1, true)]; simp [is_true]; constructor; trivial
  
def NegPosData.of_false (h : is_false L) : NegPosData L := by
  use L, []
  exact ⟨⟨h, is_true_nil, by simp⟩⟩

def NegPosData.of_true (h : is_true L) : NegPosData L := by
  use [], L
  exact ⟨⟨is_false_nil, h, by simp⟩⟩

def NegPosData.tail (h : NegPosData (head :: t)) : NegPosData t := by
  rcases h with ⟨a1, a2, ha⟩
  match a1 with
  | [] => match a2 with
    | [] =>
      simp only [is_false_nil, is_true_nil, List.append_nil, reduceCtorEq, and_false] at ha
      exact ha.1.elim
    | heada :: taila =>
      apply NegPosData.of_true
      apply (@is_true_tail _ head)
      rw [ha.1.2.2, List.nil_append]
      exact ha.1.2.1
  | heada :: taila =>
    use taila, a2
    constructor
    constructor
    · intro _ hx
      apply ha.1.1 _ (List.mem_cons_of_mem heada hx)
    constructor
    · exact ha.1.2.1
    simp only [List.cons_append, List.cons.injEq] at ha
    rw [ha.1.2.2.2]

noncomputable def NegPosData.of_append (h : NegPosData (a++b)) : NegPosData a × NegPosData b := by
  rcases h with ⟨a1, a2, a1_false, a2_true, ha⟩
  rcases ListC.append_eq_append ha with ⟨to_middle, ⟨spec⟩⟩ | ⟨to_middle, ⟨spec⟩⟩
  · constructor
    · rw [spec.1] at ha
      simp only [List.append_assoc, List.append_cancel_left_eq] at ha
      rw [spec.1]
      use a1, to_middle
      constructor
      constructor
      · exact a1_false
      constructor
      · rw [← ha] at a2_true
        exact (is_true_of_append a2_true).1
      rfl
    apply NegPosData.of_true
    rw [spec.2] at a2_true
    exact (is_true_of_append a2_true).2
  constructor
  · apply NegPosData.of_false
    rw [← spec.1] at a1_false
    exact (is_false_of_append a1_false).1
  use to_middle, a2
  constructor
  constructor
  · rw [← spec.1] at a1_false
    exact fun _ hx => a1_false _ (List.mem_append_right _ hx)
  exact ⟨a2_true, spec.right⟩

def toSignedOptionList_NegPosData (h : NegPosData a) : NegPosData (to_SignedOptionList a) := by
  rcases h with ⟨a1, a2, ⟨spec⟩⟩
  use to_SignedOptionList a1, to_SignedOptionList a2
  refine ⟨⟨is_false_to_SignedOptionList spec.1, is_true_to_SignedOptionList spec.2.1, ?_⟩⟩
  rw [spec.2.2]
  unfold to_SignedOptionList
  rw [List.map_append]

def prefix_true (h1 : is_true bot3) (h : k₂ ++ [(a1, false), (b1, true)] ++ l = bot3 ++ mid3 ++ up3) :
    List.PrefixData bot3 k₂ := by
  induction k₂ generalizing bot3 with
  | nil =>
    cases bot3 with
    | nil => exact List.PrefixData.nil
    | cons head tail =>
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.cons.injEq] at h
      rw [← h.1] at h1
      simp [is_true] at h1
  | cons head tail ih =>
    cases bot3 with
    | nil => exact List.PrefixData.nil
    | cons head1 tail1 =>
      simp only [List.cons_append, List.cons.injEq] at h
      specialize @ih tail1 (is_true_of_cons h1).2 h.2
      rw [h.1]
      exact (List.PrefixData.cons head1) ih

def prefix_false (h1 : is_false t3) (h : tk ++ [(a1, false), (b1, true)] ++ l =
    t3 ++ (f, false) :: (m ++ [(c, true)]) ++ up3) : List.PrefixData t3 tk := by
  induction tk generalizing t3 with
  | nil =>
    cases t3 with
    | nil => exact List.PrefixData.nil
    | cons head tail =>
      cases tail with
      | nil =>
        simp at h
      | cons ht tt =>
        simp at h
        rw [← h.2.1] at h1
        specialize h1 (b1, true)
        simp at h1
  | cons head tail ih =>
    cases t3 with
    | nil =>
      exact List.PrefixData.nil
    | cons ht tt =>
      simp at h
      specialize @ih tt (is_false_of_cons h1).2 (by simp [h.2])
      rw [h.1]
      exact List.PrefixData.cons ht ih

end SignedList
