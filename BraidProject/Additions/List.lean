theorem List.reconstruct_from_projection {L : List (α × β)} {b : β} (h : ∀ x ∈ L, x.2 = b) :
    List.map (fun x ↦ (x, b)) (List.map (fun x ↦ x.1) L) = L := by
  induction L with
  | nil => rfl
  | cons head tail ih => grind
