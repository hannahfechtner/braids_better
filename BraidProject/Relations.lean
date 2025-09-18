import Mathlib.Data.Nat.Dist

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

inductive grid_style_real : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| basic (n : ℕ) : grid_style_real [(some n, false), (some n, true)] [(none, true), (none, false)]
| apart {i j : ℕ} (h : Nat.dist i j > 1) : grid_style_real [(i, false), (j, true)] [(j, true), (i, false)]
| close {i j : ℕ} (h : Nat.dist i j = 1) : grid_style_real [(i, false), (j, true)]
    [(j, true), (i, true), (j, false), (i, false)]

inductive empty_fill : List (Option ℕ × Bool) → List (Option ℕ × Bool) → Type
| over (n : ℕ) : empty_fill [(n, false), (none, true)] [(none, true), (n, false)]
| up (n : ℕ) : empty_fill [(none, false), (some n, true)] [(n, true), (none, false)]
| empty : empty_fill [(none, false), (none, true)] [(none, true), (none, false)]
