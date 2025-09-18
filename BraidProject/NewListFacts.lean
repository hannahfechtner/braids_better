import Mathlib.Tactic.Convert
import Mathlib.Tactic.Use
import Mathlib.Data.List.Induction

def List.append_singleton_eq_append_singleton (h : L1 ++ [a] = L2 ++ [b]) : L1 = L2 ∧ a = b := by
  refine of_concat_eq_concat ?_
  convert h
  simp only [concat_eq_append]
  simp only [concat_eq_append]

theorem List.prefix_of_append {α : Type} {l1 l2 l3: List α} (h : l1 <+: l2) : l1 <+: l2 ++ l3 := by
  rcases h with ⟨rest, spec⟩
  use rest ++ l3
  rw [← spec, List.append_assoc]

theorem suffix_of_append (h : l₁ <:+ l2) : l₁ <:+ l3 ++ l2 := by
  rcases h with ⟨rest, spec⟩
  use l3 ++ rest
  simp [spec]

theorem List.suffix_append_right (h : l1 <:+ l2) : l1 ++ l3 <:+ l2 ++ l3 := by
  rcases h with ⟨rest, spec⟩
  use rest
  rw [← spec, List.append_assoc]


theorem List.append_eq_len_two (h1 : a.length > 0) (h2 : b.length > 0) (h3 : a ++ b = [c, d]) : a = [c] ∧ b = [d] := by
    have H : ¬ a.length > 1 := by
      intro h
      apply congr_arg List.length at h3
      simp only [length_append, length_cons, length_nil, Nat.zero_add, Nat.reduceAdd] at h3
      omega
    exact append_inj h3 (Nat.le_antisymm h1 (Nat.le_of_not_lt H)).symm


theorem List.length_geq_one_eq_cons_cons (b) (h : a ++ b = c :: d :: e) (h2 : a.length > 1) : ∃ f, a = c :: d :: f := by
  induction e using List.reverseRecOn generalizing b with
  | nil =>
    use []
    have H : a.length = 2 := by
      apply congr_arg List.length at h
      simp only [length_append, length_cons, length_singleton, Nat.succ_eq_add_one,
        Nat.reduceAdd, List.length_nil] at h
      omega
    exact append_inj_left h H
  | append_singleton front caboose ih =>
    induction b using List.reverseRecOn with
    | nil =>
      use front ++ [caboose]
      rw [List.append_nil] at h
      exact h
    | append_singleton head tail =>
      apply ih head
      rw [← List.append_assoc] at h
      change (a++head) ++ [tail] = (c :: d :: front) ++ [caboose] at h
      exact (List.append_singleton_eq_append_singleton h).1
