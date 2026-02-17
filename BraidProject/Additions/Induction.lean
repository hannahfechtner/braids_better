import BraidProject.Additions.NatDist


/-- induction on the absolute difference of two numbers. this also permits a non-zero base case -/
theorem induction_dist {k : ℕ} (i j : ℕ) (h : k ≤ Nat.dist i j)
    (p : ℕ → ℕ → Prop) (base_case : ∀ i' j', Nat.dist i' j' = k → p i' j')
    (inductive_case : ∀ i' j', k + 1 ≤ Nat.dist i' j' →
    (∀ i'' j'' : ℕ, k ≤ Nat.dist i'' j'' → (Nat.dist i'' j'' < Nat.dist i' j') →  p i'' j'') →
    p i' j') : p i j := by
  have : ∀ t, ∀ i j, Nat.dist i j = t + k → (∀ i' j', Nat.dist i' j' = k → p i' j') →
      (∀ i' j', k + 1 ≤ Nat.dist i' j' → (∀ i'' j'' : ℕ, k ≤ Nat.dist i'' j'' →
      (Nat.dist i'' j'' < Nat.dist i' j') →  p i'' j'') → p i' j') → p i j := by
    intro t
    induction t using Nat.caseStrongRecOn
    · intro i j ad_is bbase_case _
      rw [zero_add] at ad_is
      exact bbase_case _ _ ad_is
    rename_i k' hk'
    intro new_i new_j new_ad_is _ n_ic
    apply n_ic
    · rw [new_ad_is, Nat.succ_eq_add_one, add_comm, add_assoc, add_comm]
      exact Nat.le_add_left (k + 1) k'
    intro one two bigger_than smaller_thing
    apply hk' (Nat.dist one two - k) _ _ _ _ base_case n_ic
    · rw [new_ad_is, Nat.succ_add k' k] at smaller_thing
      exact Nat.sub_le_of_le_add (Nat.lt_succ.mp smaller_thing)
    exact Nat.eq_add_of_sub_eq bigger_than rfl
  exact this (Nat.dist i j - k) i j (Nat.eq_add_of_sub_eq h rfl) base_case inductive_case

-- mathematical induction, where the induction variable is bound between two others
theorem induction_bounded {i j : ℕ} (k : ℕ) (h : k ≥ i) (h' : k < j) (p : ℕ → Prop)
    (base_case : p i)
    (inductive_case : ∀ k', (k'> i → k'<j → (∀ k'', (i ≤ k'' ∧ k'' < k') → p k'') → p k')) :
    p k := by
  have : ∀ t i j k, k = i + t → k < j → p i →
    (∀ k', (k' > i → k' < j → (∀ k'', (i ≤ k'' ∧ k'' < k') → p k'') → p k')) → p k := by
    intro t
    induction t with
    | zero =>
      intro one two three k_is _ bbc _
      rw [k_is]
      exact bbc
    | succ n hn =>
      intro a b _ _ ub bc ic
      apply hn (a + 1) b _ (by linarith) ub
      · apply ic _ (Nat.le.refl) (Nat.lt_of_le_of_lt (by linarith) ub)
        intro k'' bound
        have : k'' = a := by linarith
        rw [this]
        exact bc
      intro k' lb' ub' ic'
      apply ic
      · linarith [lb']
      · exact ub'
      intro k'' bound''
      rcases Nat.lt_trichotomy k'' a with lt | rfl | gt
      · linarith [bound''.1, lt]
      · exact bc
      exact ic' k'' ⟨gt, bound''.right⟩
  exact this (k - i) i j k (Nat.add_sub_of_le h).symm h' base_case inductive_case
