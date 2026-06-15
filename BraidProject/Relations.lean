import Mathlib.Data.Nat.Dist

namespace Braid

inductive reversing : List (ℕ × Bool) → List (ℕ × Bool) → Type
| basic {i j : ℕ} (h : Nat.dist i j = 0) : reversing [(i, false), (j, true)] []
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

inductive grid_style_nontrivial : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| basic (n : ℕ) : grid_style_nontrivial [(some n, false), (some n, true)] [(none, true), (none, false)]
| apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style_nontrivial [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style_nontrivial [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

inductive grid_style_trivial : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| over (n : ℕ) : grid_style_trivial [(n, false), (none, true)] [(none, true), (n, false)]
| up (n : ℕ) : grid_style_trivial [(none, false), (some n, true)] [(n, true), (none, false)]
| empty : grid_style_trivial [(none, false), (none, true)] [(none, true), (none, false)]

def gs_of_real (h : grid_style_nontrivial a b) : grid_style a b :=
  match h with
  | grid_style_nontrivial.basic n => grid_style.basic n
  | grid_style_nontrivial.apart hdist => grid_style.apart hdist
  | grid_style_nontrivial.close hdist => grid_style.close hdist

def grid_style_spec (h : grid_style i j) : Σ a b, PLift (i = [(a, false), (b, true)]) := by
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

def grid_style_nontrivial_spec (h : grid_style_nontrivial i j) :
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

def grid_style_trivial_spec (h : grid_style_trivial i j) :
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
