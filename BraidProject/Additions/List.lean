import Mathlib.Tactic

namespace List

theorem reconstruct_from_projection {L : List (α × β)} {b : β} (h : ∀ x ∈ L, x.2 = b) :
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

theorem IsPrefix.append_cases {a b c : List α} (h : a <+: b ++ c) : a <+: b ∨ ∃ a2, a2.length > 0 ∧
  a = b ++ a2 ∧ a2 <+: c := by
  rcases h with ⟨r, hr⟩
  rcases List.append_eq_append_iff.mp hr with ⟨tm, s1, s2⟩ | ⟨fm, s1, s2⟩
  · match tm with
    | [] => aesop
    | t1 :: t2 =>
      left
      rw [s1]
      exact List.prefix_append a (t1 :: t2)
  match fm with
  | [] => aesop
  | f1 :: f2 =>
    right
    use f1 :: f2
    constructor
    · simp
    constructor
    · exact s1
    simp [s2]
