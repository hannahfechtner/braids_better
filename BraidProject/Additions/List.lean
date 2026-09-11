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
    simp only [length_append, length_cons, length_nil, zero_add] at hr
    have : l.length = 0 := by omega
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

def append_singleton_eq_append_singleton (h : L1 ++ [a] = L2 ++ [b]) : L1 = L2 ∧ a = b := by
  simp only [← concat_eq_append] at h
  exact of_concat_eq_concat h

theorem suffix_append_right (h : l1 <:+ l2) : l1 ++ l3 <:+ l2 ++ l3 := by
  rcases h with ⟨rest, spec⟩
  use rest
  rw [← spec, List.append_assoc]

theorem append_non_nil_eq_len_two (h1 : a.length > 0) (h2 : b.length > 0) (h3 : a ++ b = [c, d]) : a = [c] ∧ b = [d] := by
  have H : ¬ a.length > 1 := by
    intro h
    apply congr_arg List.length at h3
    simp only [length_append, length_cons, length_nil, Nat.zero_add, Nat.reduceAdd] at h3
    omega
  exact append_inj h3 (Nat.le_antisymm h1 (Nat.le_of_not_lt H)).symm

theorem length_geq_one_eq_cons_cons (b) (h : a ++ b = c :: d :: e) (h2 : a.length > 1) : ∃ f, a = c :: d :: f := by
  match a with
  | [] => simp at h2
  | a1 :: [] => simp at h2
  | a1 :: a2 :: tail =>
    use tail
    grind

theorem map_mul (a b : FreeMonoid α) : List.map f (a * b) = List.map f a ++ List.map f b := by
  rw [← List.map_append]
  congr

end List
