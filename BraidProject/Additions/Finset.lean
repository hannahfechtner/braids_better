import Mathlib.Data.Finset.Empty

theorem mem_nil : (a : α) ∈ (∅ : Finset α) ↔ False := List.mem_nil_iff a
