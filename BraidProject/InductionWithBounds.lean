--import KnotProject.Nat_Facts
import BraidProject.Nat_Dist_Additions

theorem induction_above {k : ℕ} (i j : ℕ) (h : k ≤ Nat.dist i j)
    (p : ℕ → ℕ → Prop) (base_case : ∀ i' j', Nat.dist i' j' = k → p i' j')
    (inductive_case : ∀ i' j', k + 1 <= Nat.dist i' j' →
    (∀ i'' j'' : ℕ, k <= Nat.dist i'' j'' → (Nat.dist i'' j'' < Nat.dist i' j') →  p i'' j'') →
    p i' j') : p i j := by
  have : ∀ t, ∀ i j, Nat.dist i j = t+k → (∀ i' j', Nat.dist i' j' = k → p i' j') →
      (∀ i' j', k + 1 <= Nat.dist i' j' → (∀ i'' j'' : ℕ, k <= Nat.dist i'' j'' →
      (Nat.dist i'' j'' < Nat.dist i' j') →  p i'' j'') → p i' j') → p i j := by
    intro t
    induction t using Nat.caseStrongInductionOn
    · intro i j ad_is bbase_case _
      rw [zero_add] at ad_is
      exact bbase_case _ _ ad_is
    rename_i k' hk'
    intro new_i new_j new_ad_is _ n_ic
    apply n_ic
    · rw [new_ad_is]
      rw [Nat.succ_eq_add_one, add_comm, add_assoc, add_comm]
      exact Nat.le_add_left (k + 1) k'
    intro one two bigger_than smaller_thing
    apply hk' (Nat.dist one two - k)
    · rw [new_ad_is, Nat.succ_add k' k] at smaller_thing
      exact Nat.sub_le_of_le_add (Nat.lt_succ.mp smaller_thing)
    · exact Nat.eq_add_of_sub_eq bigger_than rfl
    · exact base_case
    exact n_ic
  apply this (Nat.dist i j - k) i j
  · exact Nat.eq_add_of_sub_eq h rfl
  · exact base_case
  exact inductive_case

-- startting at two. again, m,ore general version is above
theorem induction_above_two (i j : ℕ) (h : 2 ≤ Nat.dist i j)
    (p : ℕ → ℕ → Prop) (base_case : ∀ i' j', Nat.dist i' j' = 2 → p i' j')
    (inductive_case : ∀ i' j', 3<= Nat.dist i' j' →
    (∀ i'' j'' : ℕ, 2 <= Nat.dist i'' j'' → (Nat.dist i'' j'' < Nat.dist i' j') →  p i'' j'') →
    p i' j') : p i j := by
  have : ∀ t, ∀ i j, Nat.dist i j = t+2 → (∀ i' j', Nat.dist i' j' = 2 → p i' j') →
      (∀ i' j', 3<= Nat.dist i' j' → (∀ i'' j'' : ℕ, 2 <= Nat.dist i'' j'' →
      (Nat.dist i'' j'' < Nat.dist i' j') →  p i'' j'') → p i' j') → p i j := by
    intro t
    induction t using Nat.caseStrongInductionOn
    · intro i j ad_is bbase_case _
      exact bbase_case _ _ ad_is
    rename_i k hk
    intro new_i new_j new_ad_is _ n_ic
    apply n_ic
    · rw [new_ad_is]
      exact Nat.le_add_left 3 k
    intro one two bigger_than smaller_thing
    apply hk (Nat.dist one two - 2)
    · rw [new_ad_is] at smaller_thing
      have helper : Nat.dist one two <= k + 2 := by exact Nat.lt_succ.mp smaller_thing
      exact Nat.sub_le_of_le_add helper
    · exact Nat.eq_add_of_sub_eq bigger_than rfl
    · exact base_case
    exact n_ic
  apply this (Nat.dist i j - 2) i j
  · exact Nat.eq_add_of_sub_eq h rfl
  · exact base_case
  exact inductive_case

--starting at 0. not needed, but helped me step up to the above one
theorem induction_above' (i j : ℕ) (p : ℕ → ℕ → Prop)
    (base_case : ∀ i' j', Nat.dist i' j' = 0 → p i' j')
    (inductive_case : ∀ i' j', (∀ i'' j'' : ℕ, (Nat.dist i'' j'' < Nat.dist i' j') → p i'' j'')
    → p i' j') : p i j := by
  have : ∀ t, ∀ i j, Nat.dist i j = t → (∀ i' j', Nat.dist i' j' = 0 → p i' j') →
      (∀ i' j', (∀ i'' j'' : ℕ, (Nat.dist i'' j'' < Nat.dist i' j') →  p i'' j'') → p i' j') →
      p i j := by
    intro t
    induction t using Nat.caseStrongInductionOn
    · intro i j ad_is bbase_case _
      exact bbase_case _ _ ad_is
    rename_i k hk
    intro new_i new_j new_ad_is _ n_ic
    apply n_ic
    intro one two smaller_thing
    apply hk (Nat.dist one two)
    · rw [new_ad_is] at smaller_thing
      exact Nat.lt_succ.mp smaller_thing
    · exact rfl
    · exact base_case
    exact inductive_case
  apply this (Nat.dist i j) i j
  · exact rfl
  · exact base_case
  exact inductive_case

-- regular induction, where the induction variable is bound between two others
-- this one is used
theorem induction_in_between_with_fact {i j : ℕ} (k : ℕ) (h : k>= i+1) (h' : k<j) (p : ℕ → Prop)
    (base_case : p (i+1))
    (inductive_case : ∀ k', (k'> i+1 → k'<j → (∀ k'', (i+1<=k'' ∧ k''<k') → p k'') → p k'))
      : p k := by
  have : ∀ t i j k, k = i+1+t → k < j → p (i +1) →
    (∀ k', (k'> i+1 → k'<j → (∀ k'', (i+1<=k'' ∧ k''<k') → p k'') → p k')) → p k := by
    intro t
    induction t
    intro one two three k_is _ bbc _
    · rw [k_is]
      exact bbc
    rename_i n hn
    intro one two three three_is ub bbc bic
    apply hn (one +1) (two)
    · linarith [three_is]
    · exact ub
    · apply bic
      · exact Nat.le.refl
      · have H : one + 1 + 1 <= three := by linarith [three_is]
        exact Nat.lt_of_le_of_lt H ub
      intro k'' bound
      have H : k'' = one+1 := by linarith [bound.1, bound.2]
      rw [H]
      exact bbc
    intro k' lb' ub' ic
    apply bic
    · linarith [lb']
    · exact ub'
    intro k'' bound''
    have H : k''<one+1 ∨ k''=one+1 ∨ k''>one+1 := by exact Nat.lt_trichotomy k'' (one + 1)
    cases H
    ·next lt =>
      exfalso
      linarith [bound''.1, lt]
    next both =>
    cases both
    · next eq =>
      rw [eq]
      exact bbc
    next gt =>
    exact ic k'' ⟨gt, bound''.right⟩
  exact this (k - (i + 1)) i j k (Nat.add_sub_of_le h).symm h' base_case inductive_case
