import Mathlib.Data.Nat.Dist
import BraidProject.Additions.SignedOptionList

namespace Braid

namespace Relations

inductive reversing : List (ℕ × Bool) → List (ℕ × Bool) → Type
| basic {i j : ℕ} (h : Nat.dist i j = 0) : reversing [(i, false), (j, true)] []
| apart {i j : ℕ} (h : Nat.dist i j > 1) : reversing [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : reversing [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

def reversing.length (h : reversing a b) := 1

def reversing.spec (h : reversing i j) : Σ a b, PLift (i = [(a, false), (b, true)]) := by
  match h with
  | reversing.basic h =>
    rename_i i j
    use i, j
    exact {down := rfl}
  | reversing.apart h =>
    rename_i i j
    use i, j
    exact {down := rfl}
  | reversing.close h =>
    rename_i i j
    use i, j
    exact {down := rfl}

inductive reversing_prop : List (ℕ × Bool) → List (ℕ × Bool) → Prop
| basic {i : ℕ} : reversing_prop [(i, false), (i, true)] []
| apart {i j : ℕ} (h : Nat.dist i j > 1) : reversing_prop [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : reversing_prop [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

theorem reversing_subset_reversing_prop (h : reversing a b) : reversing_prop a b := by
  match h with
  | reversing.basic h =>
    rw [Nat.eq_of_dist_eq_zero h]
    apply reversing_prop.basic
  | reversing.apart h => exact reversing_prop.apart h
  | reversing.close h => exact reversing_prop.close h

inductive grid_style : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| basic (n : ℕ) : grid_style [(some n, false), (some n, true)] [(none, true), (none, false)]
| over (n : ℕ) : grid_style [(n, false), (none, true)] [(none, true), (n, false)]
| up (n : ℕ) : grid_style [(none, false), (some n, true)] [(n, true), (none, false)]
| empty : grid_style [(none, false), (none, true)] [(none, true), (none, false)]
| apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

def grid_style.length (h : grid_style a b) := match h with
| grid_style.basic _ => 1
| grid_style.over _ => 0
| grid_style.up _ => 0
| grid_style.empty => 0
| grid_style.apart _ => 1
| grid_style.close _ => 1

@[simp] theorem grid_style.length_basic (n : ℕ) :
    grid_style.length (grid_style.basic n) = 1 := rfl

@[simp] theorem grid_style.length_over (n) :
    grid_style.length (grid_style.over n) = 0 := rfl

@[simp] theorem grid_style.length_up (n) :
    grid_style.length (grid_style.up n) = 0 := rfl

@[simp] theorem grid_style.length_empty :
    grid_style.length grid_style.empty = 0 := rfl

@[simp] theorem grid_style.length_apart {i j : ℕ} (h : Nat.dist i j > 1) :
    grid_style.length (grid_style.apart h) = 1 := rfl

@[simp] theorem grid_style.length_close {i j : ℕ} (h : Nat.dist i j = 1) :
    grid_style.length (grid_style.close h) = 1 := rfl

inductive grid_style_nontrivial : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| basic (n : ℕ) : grid_style_nontrivial [(some n, false), (some n, true)] [(none, true), (none, false)]
| apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style_nontrivial [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style_nontrivial [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

def grid_style_nontrivial.length (h : grid_style_nontrivial a b) := 1

inductive grid_style_trivial : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| over (n : ℕ) : grid_style_trivial [(n, false), (none, true)] [(none, true), (n, false)]
| up (n : ℕ) : grid_style_trivial [(none, false), (some n, true)] [(n, true), (none, false)]
| empty : grid_style_trivial [(none, false), (none, true)] [(none, true), (none, false)]

def grid_style_trivial.length (h : grid_style_trivial a b) := 0

def grid_style.of_grid_style_nontrivial (h : grid_style_nontrivial a b) : grid_style a b :=
  match h with
  | grid_style_nontrivial.basic n => grid_style.basic n
  | grid_style_nontrivial.apart hdist => grid_style.apart hdist
  | grid_style_nontrivial.close hdist => grid_style.close hdist

def grid_style.of_grid_style_trivial (h : grid_style_trivial a b) : grid_style a b :=
  match h with
  | grid_style_trivial.over n => grid_style.over n
  | grid_style_trivial.up n => grid_style.up n
  | grid_style_trivial.empty => grid_style.empty

def grid_style.spec (h : grid_style i j) : Σ a b, PLift (i = [(a, false), (b, true)]) := by
  match h with
  | grid_style.basic n=>
    use n, n
    exact {down := rfl}
  | grid_style.over n =>
    use n, none
    exact {down := rfl}
  | grid_style.up n=>
    use none, n
    exact {down := rfl}
  | grid_style.empty =>
    use none, none
    exact {down := rfl}
  | grid_style.apart h =>
    rename_i i j
    use i, j
    exact {down := rfl}
  | grid_style.close h =>
    rename_i i j
    use i, j
    exact {down := rfl}

def grid_style_nontrivial.spec (h : grid_style_nontrivial i j) :
    Σ a b, PLift (i = [(some a, false), (some b, true)]) := by
  match h with
  | grid_style_nontrivial.basic n =>
    use n, n
    exact {down := rfl}
  | grid_style_nontrivial.apart h =>
    rename_i i j
    use i, j
    exact {down := rfl}
  | grid_style_nontrivial.close h =>
    rename_i i j
    use i, j
    exact {down := rfl}

def grid_style_trivial.spec (h : grid_style_trivial i j) :
    Σ a b, PLift (i = [(a, false), (b, true)]) := by
  match h with
  | grid_style_trivial.empty =>
    use none, none
    exact {down := rfl}
  | grid_style_trivial.over i =>
    use some i, none
    exact {down := rfl}
  | grid_style_trivial.up i =>
    use none, some i
    exact {down := rfl}


def SignedList.toSignedOptionList_nil_to_empty_corner (a : List (ℕ × Bool)) :=
  match a with
  | [] => [(none, true), (none, false)]
  | _ => List.map (fun (x : ℕ × Bool) => (some x.1, x.2)) a

@[simp]
private theorem SignedOptionList.toSignedList_map_some : SignedOptionList.toSignedList (List.map (fun x ↦ (some x.1, x.2)) tail) = (tail : List (ℕ × Bool)) := by
  induction tail with
  | nil => rfl
  | cons head tail ih =>
    simp [ih]

@[simp]
theorem SignedList.toSignedOptionList_nil_to_empty_corner_to_SignedList :
  SignedOptionList.toSignedList (toSignedOptionList_nil_to_empty_corner d) = d := by
  cases d with
  | nil => rfl
  | cons head tail =>
    unfold toSignedOptionList_nil_to_empty_corner
    simp only [List.map_cons, SignedOptionList.toSignedList_cons_some, Prod.mk.eta,
      SignedOptionList.toSignedList_map_some]

def reversing.to_grid_style_nontrivial (h : reversing a b) :
    grid_style_nontrivial (List.map (fun x => (some x.1, x.2)) a)
    (SignedList.toSignedOptionList_nil_to_empty_corner b) := by
  cases h with
  | basic h =>
    simp only [List.map_cons, List.map_nil, SignedList.toSignedOptionList_nil_to_empty_corner]
    rename_i i j
    rw [Nat.eq_of_dist_eq_zero h]
    apply grid_style_nontrivial.basic
  | apart h =>
    simp only [List.map_cons, List.map_nil, SignedList.toSignedOptionList_nil_to_empty_corner]
    apply grid_style_nontrivial.apart h
  | close h =>
    simp only [List.map_cons, List.map_nil, SignedList.toSignedOptionList_nil_to_empty_corner]
    apply grid_style_nontrivial.close h

end Relations

end Braid
