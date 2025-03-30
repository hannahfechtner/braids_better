import Mathlib.Data.List.Basic

def List.Infix' {α : Type} (l₁ l₂ : List α) : Type :=
  Σ pr sx, PLift (l₁ = pr ++ l₂ ++ sx)
