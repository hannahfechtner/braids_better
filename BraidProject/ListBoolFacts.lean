import BraidProject.BraidGroup
import BraidProject.FreeMonoid_mine

theorem List.map_injective (hf : Function.Injective f) (h : List.map f a = List.map f b) :
    a = b := by
  revert b
  induction a with
  | nil =>
    intro b h
    simp only [map_nil] at h
    symm
    exact map_eq_nil.mp h.symm
  | cons head tail ih =>
    intro b h
    rcases b
    · simp only [map_cons, map_nil] at h
    rename_i h_b tail_b
    simp only [map_cons, cons.injEq] at h
    specialize ih h.2
    rw [ih, hf h.1]

theorem foldl_one : ∀ (L : List (FreeMonoid (α × Bool)))
    (a : FreeMonoid (α × Bool)), List.foldl (fun a b => a * b) a L = a * List.foldl (fun a b => a * b) 1 L := by
  intro L
  induction L with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, FreeMonoid'.length_one, FreeMonoid'.eq_one_of_length_eq_zero]
    intro a
    specialize ih (a * head)
    exact List.foldl_assoc

theorem lift_to_map_inj {a b : FreeMonoid α} {z : Bool} (h1 : FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) a =
    FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) b) :
    List.map (fun x ↦ FreeMonoid.of (x, z)) a = List.map (fun x ↦ FreeMonoid.of (x, z)) b := by
  unfold FreeMonoid.lift at h1
  simp at h1
  unfold FreeMonoid.prodAux at h1
  revert b
  induction a with
  | nil =>
    intro b h
    have H : List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList ([] : List α)) = [] := rfl
    rw [H] at h
    simp at h
    rcases b
    · rfl
    rename_i hb tb
    have H : List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList (hb :: tb)) =
        (FreeMonoid.of (hb, z)) ::List.map (fun x ↦ FreeMonoid.of (x, z))
        (FreeMonoid.toList tb) := by rfl
    rw [H] at h
    simp at h
    exfalso
    rw [foldl_one] at h
    have H1 := congr_arg List.length h
    have H2 : List.length (1 : FreeMonoid (α × Bool)) = 0 := rfl
    have H3 : List.length (FreeMonoid.of (hb, z) * List.foldl (fun x x_1 ↦ x * x_1) 1
        (List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList tb))) =
        1 + List.length (List.foldl (fun (x x_1 : FreeMonoid (α × Bool)) ↦ x * x_1) (1 : FreeMonoid (α × Bool))
        (List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList tb))) :=
      Nat.succ_eq_one_add ([].append (FreeMonoid.toList (List.foldl (fun x x_1 ↦ x * x_1) 1
        (List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList tb))))).length
    rw [H2, H3] at H1
    exact Nat.not_succ_le_zero 0 (Nat.le.intro H1.symm)
  | cons head tail ih =>
    intro b
    have H : List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList (head :: tail)) =
      FreeMonoid.of (head, z) :: List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList tail) := rfl
    rw [H]
    have H1 : List.map (fun x ↦ FreeMonoid.of (x, z)) (head :: tail) =
      FreeMonoid.of (head, z) :: List.map (fun x ↦ FreeMonoid.of (x, z)) tail := rfl
    rw [H1]
    simp only [FreeMonoid'.length_one, FreeMonoid'.eq_one_of_length_eq_zero]
    induction b
    · intro hyp
      have H : List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList ([] : List α)) = [] := rfl
      rw [H] at hyp
      simp only at hyp
      exfalso
      rw [foldl_one] at hyp
      have H := congr_arg FreeMonoid'.length hyp
      simp at H
      rw [FreeMonoid'.length_mul] at H
      have H1 : FreeMonoid'.length (FreeMonoid.of (head, z)) = 1 := rfl
      rw [H1] at H
      simp only [FreeMonoid'.length_one, add_eq_zero, one_ne_zero, false_and] at H
    rename_i hb tb ihb
    intro h
    have H : List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList (hb :: tb)) =
      FreeMonoid.of (hb, z) :: List.map (fun x ↦ FreeMonoid.of (x, z)) (FreeMonoid.toList tb) := rfl
    rw [H] at h
    simp at h
    specialize @ih tb
    sorry

theorem FreeMonoid.lift_bool {a b : FreeMonoid α} {z : Bool}
    (h1 : FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) a =
    FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, z)) b) : a = b := by
  apply List.map_injective _ (lift_to_map_inj h1)
  intro x x1 h_x
  apply FreeMonoid.of_injective at h_x
  rw [Prod.mk.injEq] at h_x
  exact h_x.1

theorem FreeMonoid.lift_bool_one {a : FreeMonoid α} {b : Bool}
    (h1 : FreeMonoid.lift (fun x ↦ FreeMonoid.of (x, b)) a = 1) :
    a = 1 := by
  have H1 : (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, b)) ([] : List α) = 1 := rfl
  rw [← H1] at h1
  exact FreeMonoid.lift_bool h1


theorem false_true_true_false {a b c d : FreeMonoid' ℕ}
    (h : (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, false)) a.reverse *
    (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, true)) b =
    (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, true)) d *
    (FreeMonoid.lift fun x ↦ FreeMonoid.of (x, false)) c.reverse) : (a = 1 ∧ c = 1 ∧ b = d) ∨
    (b = 1 ∧ d = 1 ∧ a = c) := by
  rcases a
  · left
    constructor
    · rfl
    have reverse_empty : FreeMonoid'.reverse ([] : List ℕ) = 1 := by rfl
    rw [reverse_empty] at h
    simp only [FreeMonoid'.length_one, map_one, FreeMonoid'.eq_one_of_length_eq_zero, one_mul] at h
    rcases c
    · constructor
      · rfl
      rw [reverse_empty] at h
      simp only [FreeMonoid'.length_one, map_one, FreeMonoid'.eq_one_of_length_eq_zero, mul_one] at h
      sorry
    sorry
  sorry
