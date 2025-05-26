import BraidProject.Grids_R

open FreeMonoid

theorem all_ones : gridr a b c d → a = [none] → b = [none] → (c = [none] ∧ d = [none]) := by
  intro h one two
  induction h with
  | empty => exact ⟨rfl, rfl⟩
  | top_bottom i => exact ⟨rfl, two⟩
  | sides i => exact ⟨one, rfl⟩
  | top_left i => exact ⟨rfl, rfl⟩
  | adjacent i k _ =>
    simp at one
  | separated i j _ => simp at one
  | vertical _ _ h1_ih h2_ih => sorry
  | horizontal _ _ h1_ih h2_ih => sorry

theorem all_ones_better (h1 : gridr [none] [none] c d) : c = [none] ∧ d = [none] := all_ones h1 rfl rfl

-- def all_one (a b c d : FreeMonoid ℕ) := a = 1 → b = 1 → (c = 1 ∧ d = 1)

-- theorem all_ones' : gridr a b c d → all_one a b c d := by
--   intro h
--   induction h
--   · exact fun _ _ => ⟨rfl, rfl⟩
--   · exact fun _ two => ⟨rfl, two⟩
--   · exact fun one _ => ⟨one, rfl⟩
--   · exact fun _ _ => ⟨rfl, rfl⟩
--   · exact fun one _ => (of_ne_one _ one).elim
--   · exact fun one two => ⟨one, two⟩
--   · rename_i n o
--     intro one two
--     rw [(FreeMonoid.prod_eq_one one).1, two] at n
--     specialize n rfl rfl
--     rw [n.2, (FreeMonoid.prod_eq_one one).2] at o
--     specialize o rfl rfl
--     rw [n.1, o.1]
--     exact ⟨rfl, o.2⟩
--   rename_i n o
--   intro one two
--   rw [one, (FreeMonoid.prod_eq_one two).1] at n
--   specialize n rfl rfl
--   rw [n.1, (FreeMonoid.prod_eq_one two).2] at o
--   specialize o rfl rfl
--   rw [o.2, n.2]
--   exact ⟨o.1, rfl⟩

theorem i_top_bottom {i : ℕ} (h : gridr [none] [some i] c d) : c = [none] ∧ d = [some i] := by
  generalize hb : [some i] = b at h
  generalize ha : ([none] : List (Option ℕ)) = a at h
  induction h with
  | empty =>simp at hb
  | top_bottom i => exact ⟨rfl, rfl⟩
  | sides i => simp at hb
  | top_left i => simp at ha
  | adjacent i k h => simp at ha
  | separated i j h => simp at ha
  | vertical h1 h2 h1_ih h2_ih => sorry
  | horizontal h1 h2 h1_ih h2_ih => sorry

theorem i_side_side (h : gridr [some i] [none] c d) : c = [some i] ∧ d = [none] := by
  generalize one : [some i] = a at h
  generalize two : ([none] : List (Option ℕ)) = b at h
  induction h
  · exact ⟨rfl, rfl⟩
  · simp at two
  · exact ⟨rfl, rfl⟩
  · exact ⟨two, two⟩
  · simp at two
  · exact ⟨rfl, rfl⟩
  · rename_i e f g h j k l m n o p
    rw [two] at o
    sorry
  rename_i o p
  sorry

def itl (a b c d : List (Option ℕ)) := ∀ i, a = [some i] → b = [some i] → c = [none] ∧ d = [none]

theorem i_top_left : gridr a b c d → itl a b c d := by
  intro h
  induction h with
  | empty => exact fun _ _ _ => ⟨rfl, rfl⟩
  | top_bottom i =>
    intro a b c
    simp at b
  | sides i =>
    intro a b c
    simp at c
  | top_left i => exact fun _ _ _ => ⟨rfl, rfl⟩
  | adjacent i k h =>
    intro j h1 h2
    simp at h1
    simp at h2
    aesop
  | separated i j h =>
    intro k h1 h2
    simp at h1
    simp at h2
    aesop
  | vertical h1 h2 h1_ih h2_ih =>
    intro k ha hb
    sorry
  | horizontal h1 h2 h1_ih h2_ih =>
    intro k ha hb
    sorry

theorem word_side_side : ∀ a b c, gridr [none] c a b → a = [none] ∧ b = c := by
  intro a b c
  revert a b
  sorry
  -- induction c using FreeMonoid.inductionOn'
  -- · intro a b gridrdy
  --   exact all_ones gridrdy rfl rfl
  -- rename_i one two three
  -- intro a b gridrdy
  -- rcases splittable_vertically_of_gridr gridrdy (of one) two rfl with ⟨c, d, e, f, g, i⟩
  -- have H2 := i_top_bottom f
  -- rw [H2.1] at g
  -- rw [H2.2] at i
  -- specialize three _ _ g
  -- rw [three.2] at i
  -- exact ⟨three.1, i⟩

theorem word_top_bottom : ∀ a b c, gridr c [none] a b → a = c ∧ b = [none] := by
  intro a b c
  revert a b
  sorry
  -- induction c using FreeMonoid.inductionOn'
  -- · intro a b h
  --   exact all_ones h rfl rfl
  -- intro c d h
  -- rename_i a b ih
  -- apply splittable_horizontally_of_gridr at h
  -- specialize h (of a) b rfl
  -- rcases h with ⟨u, c₁, c₂, h1, h2, h3⟩
  -- apply i_side_side at h1
  -- rw [h1.2] at h2
  -- rw [h1.1] at h3
  -- specialize ih c₂ d h2
  -- rw [ih.1] at h3
  -- rw [h3]
  -- exact ⟨rfl, ih.2⟩

def ia (a b c d : List (Option ℕ)) := ∀ i j, a = [some i] → b = [some j] → (Nat.dist i j = 1) →
  c = [some i, some j] ∧ d = [some j, some i]

theorem i_adjacent : gridr a b c d → ia a b c d := by
  intro h
  induction h with
  | empty =>
    intro i j h1
    simp at h1
  | top_bottom i =>
    intro i j h1
    simp at h1
  | sides i =>
    intro i j _ h2
    simp at h2
  | top_left i =>
    intro i j h1 h2 d
    simp at h1
    simp at h2
    aesop
  | adjacent i k _ =>
    intro i j h1 h2 _
    simp at h1
    simp at h2
    aesop
  | separated i j h =>
    intro i j h1 h2 d
    simp at h1
    simp at h2
    aesop
  | vertical h1 h2 h1_ih h2_ih =>
    intro i j ha hb d
    sorry
  | horizontal h1 h2 h1_ih h2_ih =>
    intro i j ha hb d
    sorry

def ij_eq (a b c d : List (Option ℕ)) := ∀ k, a = [some k] → b = [some k] → (c = [none] ∧ d = [none])

theorem helpier_eq {a b c d : List (Option ℕ)} (h : gridr a b c d) : ij_eq a b c d := by
  induction h
  · intro a b
    simp at b
  · intro a b
    simp at b
  · intro a b c
    simp at c
  · exact fun _ _ _ => ⟨rfl, rfl⟩
  · intro k eq1 eq2
    simp at eq1
    simp at eq2
    aesop
  · intro k eq1 eq2
    simp at eq1
    simp at eq2
    aesop
  · rename_i e f g h i j k l m n o
    intro p eq1 eq2
    sorry
  rename_i e f g h i j k l m n o
  sorry

def ij_close (a b c d : List (Option ℕ)) := ∀ i j, (Nat.dist i j = 1) → a = [some i] → b = [some j] →
    (c = [some i, some j] ∧ d = [some j, some i])

theorem helpier_close {a b c d : List (Option ℕ)} (h : gridr a b c d) : ij_close a b c d := by
  induction h
  · intro a b c d
    simp at d
  · intro a b c d
    simp at d
  · intro a b c d e
    simp at e
  · intro j k dist one two
    simp at one two
    aesop
  · intro j k _ one two
    simp at one two
    aesop
  · intro j k dist one two
    simp at one two
    aesop
  · rename_i e f g h i j k l m n o
    intro p q dist one two
    sorry
  rename_i e f g h i j k l m n o
  intro p q dist one two
  sorry

def ij_st (a b c d : List (Option ℕ)) := ∀ i j, (i + 2 <= j ∨ j + 2 <= i) → a = [some i] → b = [some j] →
    (c = [some i] ∧ d = [some j])

theorem helpier_ij {a b c d : List (Option ℕ)} (h : gridr a b c d) : ij_st a b c d := by
  induction h
  · intro i j _ one two
    exact ⟨one, two⟩
  · intro j k _ one two
    exact ⟨one, two⟩
  · intro i j _ one two
    exact ⟨one, two⟩
  · rename_i i
    intro a b orie one two
    simp at one two
    aesop
  · rename_i i
    intro a b or_thing one two
    exfalso
    apply or_dist_iff.mpr at or_thing
    simp at one two
    aesop
  · intro _ _ _ one two
    exact ⟨one, two⟩
  · rename_i e f g h i j k l m n o
    intro p q or_thing p_is q_is
    sorry
  rename_i e f g h i j k l m n o
  intro p q or_thing p_is q_is
  sorry

theorem i_both_one : gridr a b [none] [none] → PresentedMonoid.rel braid_rels_m_inf (to_fm a) (to_fm b) := by
  intro h
  apply PresentedMonoid.exact
  have H := braid_eq_of_gridr h
  simp [to_fm_append, to_fm] at H
  exact H
