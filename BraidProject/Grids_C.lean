import BraidProject.BraidMonoidInf
import BraidProject.Grids'
import Mathlib.Data.Nat.Dist
import BraidProject.Additions.Classical

open FreeMonoid

namespace Braid

/-- a reversing GridData, inductively defined as the set of basic CellDatas, and a vertical and horizontal
closure under appending-/
inductive GridData : FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → FreeMonoid ℕ → Type
  | empty : GridData 1 1 1 1
  | top_bottom (i : ℕ) : GridData 1 (of i) (of i) 1
  | sides (i : ℕ) : GridData (of i) 1 1 (of i)
  | top_left (i : ℕ) : GridData (of i) (of i) 1 1
  | adjacent (i k : ℕ) (h : i.dist k = 1) : GridData (of i) (of k) (of k * of i) (of i * of k)
  | separated (i j : ℕ) (h : i.dist j > 1) : GridData (of i) (of j) (of j) (of i)
  | vertical (h1: GridData a b c d) (h2 : GridData e c f g) : GridData (a * e) b f (d * g)
  | horizontal (h1: GridData a b c d) (h2 : GridData d e f g) : GridData a (b * e) (c * f) g

inductive CellData : List ℕ → List ℕ → List ℕ → List ℕ → Type
  | empty : (CellData [] [] [] [])
  | top_bottom (i : ℕ) : CellData [] [i] [i] []
  | sides (i : ℕ) : CellData [i] [] [] [i]
  | top_left (i : ℕ) : CellData [i] [i] [] []
  | adjacent (i k : ℕ) (h : Nat.dist i k = 1) : CellData [i] [k] [k, i] [i, k]
  | separated (i j : ℕ) (h : Nat.dist i j > 1) : CellData [i] [j] [j] [i]

def CellData.symm (h : CellData a b c d) : CellData b a d c :=
  match h with
  | .empty => CellData.empty
  | .top_bottom i => CellData.sides i
  | .sides i => CellData.top_bottom i
  | .top_left i => CellData.top_left i
  | .adjacent i k h => CellData.adjacent k i (by rw [Nat.dist_comm] at h; exact h)
  | .separated i j h => CellData.separated j i (by rw [Nat.dist_comm] at h; exact h)


namespace GridData

theorem to_grid (h : GridData a b c d) : grid a b c d := by
  induction h with
  | empty => exact grid.empty
  | top_bottom i => exact grid.top_bottom i
  | sides i => exact grid.sides i
  | top_left i => exact grid.top_left i
  | adjacent i k h => exact grid.adjacent i k h
  | separated i j h => exact grid.separated i j h
  | vertical h1 h2 ih1 ih2 => exact ih1.vertical ih2
  | horizontal h1 h2 ih1 ih2 => exact ih1.horizontal ih2

noncomputable def of_CellData (h : CellData a b c d) : GridData a b c d := by
  induction h with
  | empty => exact GridData.empty
  | top_bottom i => exact GridData.top_bottom _
  | sides i => exact GridData.sides _
  | top_left i => exact GridData.top_left _
  | adjacent i k h => exact GridData.adjacent _ _ h
  | separated i j h => exact GridData.separated _ _ h

def length : GridData a b c d → ℕ := by
  intro h
  match h with
  | GridData.empty => exact 0
  | GridData.top_bottom _ => exact 0
  | GridData.sides _ => exact  0
  | GridData.top_left _ => exact 1
  | GridData.adjacent _ _ _ => exact 1
  | GridData.separated _ _ _ => exact 1
  | GridData.horizontal h1 h2 => exact length h1 + length h2
  | GridData.vertical h1 h2 => exact length h1 + length h2

def of_grid (h : grid a b c d) : Nonempty (GridData a b c d) := by
  induction h with
  | empty =>
    apply Nonempty.intro GridData.empty
  | top_bottom i => apply Nonempty.intro (GridData.top_bottom i)
  | sides i => apply Nonempty.intro (GridData.sides i)
  | top_left i => apply Nonempty.intro (GridData.top_left i)
  | adjacent i k h => apply Nonempty.intro (GridData.adjacent i k h)
  | separated i j h => apply Nonempty.intro (GridData.separated i j h)
  | vertical h1 h2 ih1 ih2 =>
    exact Nonempty.intro ((Classical.choice ih1).vertical (Classical.choice ih2))
  | horizontal h1 h2 ih1 ih2 =>
    exact Nonempty.intro ((Classical.choice ih1).horizontal (Classical.choice ih2))

noncomputable def swap : GridData a b c d → GridData b a d c := by
  intro h
  have := to_grid h
  have := of_grid (Grid.swap this)
  use Classical.choice this

def sides_word (u : FreeMonoid ℕ) : GridData u 1 1 u := by
  match u with
  | [] => exact GridData.empty
  | head :: tail => exact GridData.vertical (GridData.sides head) (sides_word tail)

-- def GridData_top_bottom_word (u : FreeMonoid ℕ) : GridData 1 u u 1 := by
--   induction u
--   · exact GridData.empty
--   · exact GridData.top_bottom _
--   · rename_i one two
--     exact GridData.horizontal one two

-- def GridData_top_left_word (u : FreeMonoid ℕ) : GridData u u 1 1 := by
--   induction u
--   · exact GridData.empty
--   · exact GridData.top_left _
--   · rename_i x y one two
--     exact GridData.vertical (GridData.horizontal one (GridData_top_bottom_word y))
--       (GridData.horizontal (GridData_sides_word y) two)

/-- relating GridData equivalence to braid equivalence, one way -/
theorem braid_eq (h : GridData a b c d) :
    BraidMonoidInf.mk (a * c) = BraidMonoidInf.mk (b * d) := by
  apply Grid.braid_eq_of_grid (to_grid h)

theorem diag_length_eq (h : GridData a b c d) : a.length + c.length = b.length + d.length := by
  apply Grid.diag_length_eq (to_grid h)

-- noncomputable def splittable_vertically {a b c d : FreeMonoid ℕ} (h : GridData a b c d) :
--     ∀ b₁ b₂, b = b₁ * b₂ → Σ u c₁ c₂, (GridData a b₁ c₁ u) × GridData u b₂ c₂ d × PLift (c = c₁ * c₂) := by
--   intro b1 b2 hb
--   have H := Grid.splittable_vertically (to_grid h) b1 b2 hb
--   use Classical.choose₃₁ H, Classical.choose₃₂ H, Classical.choose₃₃ H
--   constructor
--   · exact Classical.choice (of_grid (Classical.choose₃_spec' H).1)
--   constructor
--   · exact Classical.choice (of_grid (Classical.choose₃_spec' H).2.1)
--   exact ⟨(Classical.choose₃_spec' H).2.2⟩

-- noncomputable def splittable_horizontally {a b c d : FreeMonoid ℕ} (h : GridData a b c d) :
--     ∀ a₁ a₂, a = a₁ * a₂ →  Σ u d₁ d₂, GridData a₁ b u d₁ × GridData a₂ u c d₂ × PLift (d = d₁ * d₂) := by
--   intro a1 a2 ha
--   have H := Grid.splittable_horizontally (to_grid h) a1 a2 ha
--   use Classical.choose₃₁ H, Classical.choose₃₂ H, Classical.choose₃₃ H
--   constructor
--   · exact Classical.choice (of_grid (Classical.choose₃_spec' H).1)
--   constructor
--   · exact Classical.choice (of_grid (Classical.choose₃_spec' H).2.1)
--   exact ⟨(Classical.choose₃_spec' H).2.2⟩

end GridData
end Braid
