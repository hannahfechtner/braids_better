import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic

--yes I'm hardcoding this, sorry ...
def valid_tiles : Finset (Finset (Fin 6)) :=
  {{0,1}, {2, 3}, {4, 5}, {0, 2}, {1, 3}, {2, 4}, {3, 5}}

def tiling := {s : Finset (Finset (Fin 6)) // s.card = 4 ∧ ∃ a b c d,
  a∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ a.card = 2 ∧ b.card = 2 ∧ c.card = 1 ∧ d.card = 1
  ∧ (List.map Finset.toList s.toList).flatten.toFinset = {0, 1, 2, 3, 4, 5} ∧
  a ∩ b = {} ∧ a ∩ c = {} ∧ a ∩ d = {} ∧ b ∩ c = {} ∧ b ∩ d = {} ∧ c ∩ d = {}
  ∧ a ∈ valid_tiles ∧ b ∈ valid_tiles}


#check (Set.univ : Set tiling)

theorem eleven_tilings :
  (Set.univ : Set tiling).card = 11 := by
  -- The proof will be constructed here, but for now we will just state the theorem.
  sorry

#check tiling
