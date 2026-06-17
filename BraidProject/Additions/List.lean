import Mathlib.Tactic

theorem List.reconstruct_from_projection {L : List (α × β)} {b : β} (h : ∀ x ∈ L, x.2 = b) :
    List.map (fun x ↦ (x, b)) (List.map (fun x ↦ x.1) L) = L := by
  induction L with
  | nil => rfl
  | cons head tail ih => grind

theorem IsSuffix.of_singleton (h : l <:+ [a]) : l = [] ∨ l = [a] := by
  rcases h with ⟨r, hr⟩
  match r with
  | [] => aesop
  | r1 :: r2 => aesop

theorem IsPrefix.of_singleton (h : l <+: [a]) : l = [] ∨ l = [a] := by
  rcases h with ⟨r, hr⟩
  match r with
  | [] => aesop
  | r1 :: r2 =>
    apply congr_arg List.length at hr
    simp at hr
    have H : l.length = 0 := by omega
    aesop
