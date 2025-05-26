import BraidProject.Grids_D
import BraidProject.GridsTwo

open FreeMonoid

theorem all_ones_t : gridl a b c d → a = [none] → b = [none] → (c = [none] ∧ d = [none]) := by
  intro h one two
  induction h with
  | empty => exact ⟨rfl, rfl⟩
  | top_bottom i => exact ⟨rfl, two⟩
  | sides i => exact ⟨one, rfl⟩
  | top_left i => exact ⟨rfl, rfl⟩
  | adjacent i k _ => simp at one --exact (of_ne_one _ one).elim
  | separated i j _ => simp at one --exact (of_ne_one _ one).elim
  | vertical _ _ h1_ih h2_ih => sorry
  | horizontal _ _ h1_ih h2_ih => sorry

theorem all_ones_better_t (h1 : gridl [none] [none] c d) : c = [none] ∧ d = [none] := all_ones_t h1 rfl rfl

-- def all_one (a b c d : FreeMonoid ℕ) := a = 1 → b = 1 → (c = 1 ∧ d = 1)

-- theorem all_ones' : gridl a b c d → all_one a b c d := by
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

def itb_t (a b c d : List (Option N)) := ∀ i, a = [none] → b = [some i] → c = [none] ∧ d = [some i]


theorem i_top_bottom_t (h : gridl a b c d) : itb_t a b c d := by
  induction h with
  | empty =>
    intro a b c
    simp at c
  | top_bottom i => exact fun _ ha hb => ⟨rfl, hb⟩
  | sides i =>
    intro a b c
    simp at c
  | top_left i =>
    intro a b c
    simp at b
  | adjacent i k h =>
    intro a b c
    simp at b
  | separated i j h =>
    intro a b c
    simp at b
  | vertical h1 h2 h1_ih h2_ih =>
    intro m ha hb
    sorry
  | horizontal h1 h2 h1_ih h2_ih =>
    intro m ha hb
    sorry

def iss_t (a b c d : List (Option ℕ)) := ∀ i, a = [some i] → b = [none] → c = [some i] ∧ d = [none]

theorem i_side_side_t (h : gridl a b c d) : iss_t a b c d := by
  induction h
  · intro i ha hb
    simp at ha
  · intro i ha hb
    simp at hb
  · intro i ha hb
    exact ⟨ha, hb⟩
  · intro i ha hb
    exact ⟨hb.symm.trans ha, rfl⟩
  · intro i one two
    simp at two
  · intro m ha hb
    rename_i i j h
    exact ⟨ha, hb⟩
  · rename_i e f g h j k l m n o p
    intro q one two
    sorry
  rename_i o p
  intro m one two
  sorry

def itl_t (a b c d : List (Option ℕ)) := ∀ i, a = [some i] → b = [some i] → c = [none] ∧ d = [none]

theorem i_top_left_t : gridl a b c d → itl_t a b c d := by
  intro h
  induction h with
  | empty => exact fun _ _ _ => ⟨rfl, rfl⟩
  | top_bottom i =>
    intro a b
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

theorem word_side_side_t : ∀ a b c, gridl d c a b → d = [none] → a = [none] ∧ b = c := by
  intro a b c
  revert a b d
  induction c using FreeMonoid.inductionOn'
  · intro a b d griddy ha
    exfalso
    have H := gridl_top_len_pos griddy
    change [].length > 0 at H
    simp at H
  rename_i one two three
  intro a b d1 gridldy a_is
  have H : List.length (of one) = 1 := by
    change List.length [one] = 1
    simp
  cases two with
  | h0 => sorry
  | ih x xs =>
  have H3 : List.length (.of x * xs) ≥ 1 := by
    change List.length (x :: xs) ≥ 1
    simp
  rcases splittable_vertically_of_gridl gridldy (of one) (.of x * xs) rfl (by omega) (by omega) with ⟨c, d, e, f, g, i⟩
  sorry
  -- have H2 := i_top_bottom_t f  a_is
  -- rw [H2.2] at i
  -- specialize three _ _ g H2.1
  -- rw [three.2] at i
  -- exact ⟨three.1, i.1⟩

theorem word_top_bottom_t : ∀ a b c, gridl c d a b → d = [none] → a = c ∧ b = [none] := by
  intro a b c
  revert a b d
  sorry
  -- induction c using FreeMonoid.inductionOn'
  -- · intro a b d h ha
  --   exact all_ones_t h rfl ha
  -- intro c d d1 h
  -- rename_i a b ih
  -- apply splittable_horizontally_of_gridl at h
  -- specialize h (of a) b rfl
  -- rcases h with ⟨u, c₁, c₂, h1, h2, h3⟩
  -- apply i_side_side_t at h1
  -- intro c_is
  -- specialize h1 _ rfl c_is
  -- rw [h1.1] at h3
  -- specialize ih c₂ d1 h2 h1.2
  -- rw [ih.1] at h3
  -- rw [h3.1]
  -- exact ⟨rfl, ih.2⟩

def ia_t (a b c d : List (Option ℕ)) := ∀ i j, a = [some i] → b = [some j] → (Nat.dist i j = 1) →
  c = [some i, some j] ∧ d = [some j, some i]

theorem i_adjacent_t : gridl a b c d → ia_t a b c d := by
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
    rw [h1, h2]
    exact ⟨rfl, rfl⟩
  | separated i j h =>
    intro i j h1 h2 d
    simp at h1
    simp at h2
    rw [← h1, ← h2] at d
    rw [d] at h
    simp at h
  | vertical h1 h2 h1_ih h2_ih =>
    intro i j ha hb d
    sorry
  | horizontal h1 h2 h1_ih h2_ih =>
    intro i j ha hb d
    sorry

def ij_eq_t (a b c d : List (Option ℕ)) := ∀ k, a = [some k] → b = [some k] → (c = [none] ∧ d = [none])

theorem helpier_eq_t {a b c d : List (Option ℕ)} (h : gridl a b c d) : ij_eq_t a b c d := by
  induction h
  · intro a b c
    simp at b
  · intro a b c
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
  intro p eq1 eq2
  sorry

def ij_close_t (a b c d : List (Option ℕ)) := ∀ i j, (Nat.dist i j = 1) → a = [some i] → b = [some j] →
    (c = [some i, some j] ∧ d = [some j, some i])

-- theorem helpier_close' {c d : FreeMonoid ℕ} (h1 : Nat.dist i j =1)
--     (h : gridl (of i) (of j) c d) : (c = of i * of j ∧ d = of j * of i):= by
--   generalize one : of i = a at h
--   generalize two : of j = b at h
--   induction h with
--   | empty => exact (of_ne_one _ one).elim
--   | top_bottom k => exact (of_ne_one _ one).elim
--   | sides i => exact (of_ne_one _ two).elim
--   | top_left k =>
--     rw [of_injective one, of_injective two] at h1
--     simp only [Nat.dist_self, zero_ne_one] at h1
  -- | adjacent k l dist => exact ⟨rfl, rfl⟩
  -- | separated i j h =>
  --   rw [of_injective one, of_injective two] at h1
  --   linarith [or_dist_iff.mpr h, h1]
  -- | vertical h1 h2 h1_ih h2_ih =>
  --   rename_i e f g k l m n o
  --   rcases FreeMonoid.prod_eq_of one.symm with h3 | h4
  --   · specialize h2_ih h3.2.symm
  --     rw [h3.1, h3.2, one_mul]
  --     rw [h3.1] at h1
  --     have H4 := word_side_side _ _ _ h1
  --   sorry
  -- | horizontal h1 h2 h1_ih h2_ih => sorry


theorem helpier_close_t {a b c d : List (Option ℕ)} (h : gridl a b c d) : ij_close_t a b c d := by
  induction h
  · intro a b c d e
    simp at d
  · intro a b c d e
    simp at d
  · intro a b c d e
    simp at e
  · intro j k dist one two
    simp at one
    simp at two
    aesop
  · intro j k _ one two
    simp at one
    simp at two
    rw [← one, ← two]
    exact ⟨rfl, rfl⟩
  · intro j k dist one two
    rename_i e f apart
    simp at one
    simp at two
    aesop
  · rename_i e f g h i j k l m n o
    intro p q dist one two
    sorry
  rename_i e f g h i j k l m n o
  intro p q dist one two
  sorry

def ij_st_t (a b c d : List (Option ℕ)) := ∀ i j, (i + 2 <= j ∨ j + 2 <= i) → a = [some i] → b = [some j] →
    (c = [some i] ∧ d = [some j])

theorem helpier_ij_t {a b c d : List (Option ℕ)} (h : gridl a b c d) : ij_st_t a b c d := by
  induction h
  · intro i j _ one two
    exact ⟨one, two⟩
  · intro j k _ one two
    exact ⟨one, two⟩
  · intro i j _ one two
    exact ⟨one, two⟩
  · rename_i i
    intro a b orie one two
    simp at one
    simp at two
    aesop
  · rename_i i
    intro a b or_thing one two
    apply or_dist_iff.mpr at or_thing
    simp at one
    simp at two
    aesop
  · intro _ _ _ one two
    exact ⟨one, two⟩
  · rename_i e f g h i j k l m n o
    intro p q or_thing p_is q_is
    sorry
  rename_i e f g h i j k l m n o
  sorry

theorem i_both_one_t : gridl a b [none] [none] →
    PresentedMonoid.rel braid_rels_m_inf (to_fm a) (to_fm b) := by
  intro h
  apply PresentedMonoid.exact
  have H := braid_eq_of_gridl h
  simp [to_fm_append, to_fm] at H
  exact H
