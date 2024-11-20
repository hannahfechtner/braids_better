import BraidProject.Grids

open FreeMonoid'

theorem all_ones : grid a b c d → a = 1 → b = 1 → (c = 1 ∧ d = 1) := by
  intro h one two
  induction h with
  | empty => exact ⟨rfl, rfl⟩
  | top_bottom i => exact ⟨rfl, two⟩
  | sides i => exact ⟨one, rfl⟩
  | top_left i => exact ⟨rfl, rfl⟩
  | adjacent i k _ => exact (of_neq_one _ one).elim
  | separated i j _ => exact (of_neq_one _ one).elim
  | vertical _ _ h1_ih h2_ih =>
    specialize h1_ih (FreeMonoid.prod_eq_one one).1 two
    specialize h2_ih (FreeMonoid.prod_eq_one one).2 h1_ih.2
    rw [h2_ih.2, h1_ih.1]
    exact ⟨h2_ih.1, rfl⟩
  | horizontal _ _ h1_ih h2_ih =>
    rw [one, (FreeMonoid.prod_eq_one two).1] at h1_ih
    specialize h1_ih rfl rfl
    rw [h1_ih.1, (FreeMonoid.prod_eq_one two).2] at h2_ih
    specialize h2_ih rfl rfl
    rw [h2_ih.2, h1_ih.2]
    exact ⟨h2_ih.1, rfl⟩

theorem all_ones_better (h1 : grid 1 1 c d) : c = 1 ∧ d = 1 := all_ones h1 rfl rfl

-- def all_one (a b c d : FreeMonoid' ℕ) := a = 1 → b = 1 → (c = 1 ∧ d = 1)

-- theorem all_ones' : grid a b c d → all_one a b c d := by
--   intro h
--   induction h
--   · exact fun _ _ => ⟨rfl, rfl⟩
--   · exact fun _ two => ⟨rfl, two⟩
--   · exact fun one _ => ⟨one, rfl⟩
--   · exact fun _ _ => ⟨rfl, rfl⟩
--   · exact fun one _ => (of_neq_one _ one).elim
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

theorem i_top_bottom : grid 1 (of i) c d → (c = 1 ∧ d = of i) := by
  intro h
  generalize hb : of i = b at h
  generalize ha : (1 : FreeMonoid' ℕ) = a at h
  --intro h
  induction h with
  | empty => exact (of_neq_one _ hb).elim
  | top_bottom i => exact ⟨rfl, rfl⟩
  | sides i => exact (of_neq_one _ ha.symm).elim
  | top_left i => exact (of_neq_one _ ha.symm).elim
  | adjacent i k h => exact (of_neq_one _ ha.symm).elim
  | separated i j h => exact (of_neq_one _ ha.symm).elim
  | vertical h1 h2 h1_ih h2_ih =>
    have h3 := (FreeMonoid.prod_eq_one ha.symm)
    rw [h3.1, ← hb] at h1
    rw [h3.2] at h2
    specialize h1_ih hb h3.1.symm
    rw [h1_ih.1]
    rw [h1_ih.2] at h2
    specialize h2_ih (hb.trans h1_ih.2.symm) h3.2.symm
    rw [h2_ih.1, h2_ih.2]
    exact ⟨rfl, h1_ih.2⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rcases FreeMonoid.prod_eq_of hb.symm with h3 | h4
    · rw [h3.1, ← ha] at h1
      have H := all_ones_better h1
      specialize h2_ih h3.2.symm H.1.symm
      rw [← ha, h3.1, one_mul, H.2, one_mul, h2_ih.1]
      exact ⟨H.1, h2_ih.2⟩
    rename_i e f g j k l m
    rw [← ha, h4.1, h4.2, mul_one]
    specialize h1_ih h4.1.symm ha
    rw [h4.2, h1_ih.1.trans ha.symm] at h2
    have H := all_ones_better h2
    rw [H.2, mul_one, h1_ih.2]
    exact ⟨H.1, h4.1⟩

-- theorem i_top_bottom' : grid a b c d → itb a b c d := by
--   intro h
--   induction h
--   · exact fun _ one two => ⟨one, two⟩
--   · exact fun _ one two => ⟨one, two⟩
--   · exact fun _ one two => ⟨one, two⟩
--   · exact fun _ one two => ⟨rfl, one.symm.trans two⟩
--   · intro a one two
--     rw [one, of_injective two]
--     exact ⟨(of_neq_one _ one).elim, rfl⟩
--   · exact fun _ one two => ⟨one, two⟩
--   · rename_i o p
--     intro i one two
--     rw [(FreeMonoid.prod_eq_one one).1, two] at o
--     rw [(FreeMonoid.prod_eq_one one).2] at p
  --   specialize o i rfl rfl
  --   rw [o.1]
  --   rw [o.2] at p
  --   specialize p i rfl rfl
  --   rw [p.1, p.2]
  --   exact ⟨rfl, rfl⟩
  -- rename_i g h j k l m n o p
  -- intro i one two
  -- rw [one] at o
  -- rcases FreeMonoid.prod_eq_of two
  -- · rename_i prod_is
  --   rw [prod_is.1] at o
  --   have H : g = 1 ∧ h = 1 := by
  --     rw [prod_is.1, one] at m
  --     exact all_ones m rfl rfl
  --   rw [H.1, prod_is.2] at p
  --   rw [H.2]
  --   specialize p i rfl rfl
  --   rw [p.1, p.2]
  --   exact ⟨rfl, rfl⟩
  -- rename_i prod_is
  -- rw [prod_is.1] at o
  -- specialize o i rfl rfl
  -- rw [prod_is.2, o.1] at p
  -- have H : k = 1 ∧ l = 1 := by
  --   rw [o.1, prod_is.2] at n
  --   exact all_ones n rfl rfl
  -- rw [H.1, H.2, o.2]
  -- exact ⟨rfl, rfl⟩

def iss (a b c d : FreeMonoid' ℕ) := ∀ i, a = of i → b = 1 → (c = of i ∧ d = 1)

theorem i_side_side : grid a b c d → iss a b c d := by
  intro h
  induction h
  · exact fun _ one two => ⟨one, two⟩
  · exact fun _ one two => ⟨one, two⟩
  · exact fun _ one two => ⟨one, two⟩
  · exact fun _ one two => ⟨two.symm.trans one, rfl⟩
  · intro a one two
    rw [one, two]
    constructor
    · rfl
    exact (of_neq_one _ two).elim
  · exact fun _ one two => ⟨one, two⟩
  · rename_i e f g h j k l m n o p
    intro i one two
    rw [two] at o
    rcases FreeMonoid.prod_eq_of one
    · rename_i prod_is
      rw [prod_is.1] at o
      have H : g = 1 ∧ h = 1 := by
        rw [prod_is.1, two] at m
        exact all_ones m rfl rfl
      rw [H.2, prod_is.2] at p
      rw [H.1]
      specialize p i rfl rfl
      rw [p.1, p.2]
      exact ⟨rfl, rfl⟩
    rename_i prod_is
    rw [prod_is.1] at o
    specialize o i rfl rfl
    rw [prod_is.2, o.2] at p
    have H : k = 1 ∧ l = 1 := by
      rw [o.2, prod_is.2] at n
      exact all_ones n rfl rfl
    rw [H.1, H.2, o.1]
    exact ⟨rfl, rfl⟩
  rename_i o p
  intro i one two
  rw [(FreeMonoid.prod_eq_one two).1, one] at o
  rw [(FreeMonoid.prod_eq_one two).2] at p
  specialize o i rfl rfl
  rw [o.2]
  rw [o.1] at p
  specialize p i rfl rfl
  rw [p.2]
  exact ⟨p.1, rfl⟩

def itl (a b c d : FreeMonoid' ℕ) := ∀ i, a = FreeMonoid'.of i → b = FreeMonoid'.of i → c = 1 ∧ d = 1

theorem i_top_left : grid a b c d → itl a b c d := by
  intro h
  induction h with
  | empty => exact fun _ _ _ => ⟨rfl, rfl⟩
  | top_bottom i => exact fun j h1 => ((FreeMonoid'.of_neq_one j).elim h1.symm).elim
  | sides i => exact fun j _ h2 => ((FreeMonoid'.of_neq_one j).elim h2.symm).elim
  | top_left i => exact fun _ _ _ => ⟨rfl, rfl⟩
  | adjacent i k h =>
    intro j h1 h2
    rw [FreeMonoid'.of_injective h1, FreeMonoid'.of_injective h2] at h
    simp at h
  | separated i j h =>
    intro k h1 h2
    rw [FreeMonoid'.of_injective h1, FreeMonoid'.of_injective h2] at h
    simp at h
  | vertical h1 h2 h1_ih h2_ih =>
    intro k ha hb
    rw [hb] at h1
    rw [hb] at h1_ih
    rcases FreeMonoid.prod_eq_of ha
    · rename_i ua
      rw [ua.1] at h1
      have H_idk := i_top_bottom h1
      rw [H_idk.2, ua.2] at h2_ih
      specialize h2_ih _ rfl rfl
      rw [h2_ih.1, h2_ih.2, H_idk.1]
      exact ⟨rfl, rfl⟩
    rename_i ua
    rw [ua.1] at h1_ih
    specialize h1_ih _ rfl rfl
    rw [h1_ih.2, ua.2] at h2
    have H_idk := all_ones h2 rfl rfl
    rw [H_idk.1, H_idk.2, h1_ih.1]
    exact ⟨rfl, rfl⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    intro k ha hb
    rw [ha] at h1
    rw [ha] at h1_ih
    rcases FreeMonoid.prod_eq_of hb
    · rename_i ua
      rw [ua.1] at h1
      have H_idk := i_side_side h1 _ rfl rfl
      rw [H_idk.1, ua.2] at h2_ih
      specialize h2_ih _ rfl rfl
      rw [h2_ih.1, h2_ih.2, H_idk.2]
      exact ⟨rfl, rfl⟩
    rename_i ua
    rw [ua.1] at h1_ih
    specialize h1_ih _ rfl rfl
    rw [h1_ih.1, ua.2] at h2
    have H_idk := all_ones h2 rfl rfl
    rw [H_idk.1, H_idk.2, h1_ih.2]
    exact ⟨rfl, rfl⟩


theorem word_side_side : ∀ a b c, grid 1 c a b → a = 1 ∧ b = c := by
  intro a b c
  revert a b
  induction c using FreeMonoid'.inductionOn'
  · intro a b griddy
    exact all_ones griddy rfl rfl
  rename_i one two three
  intro a b griddy
  rcases splittable_vertically_of_grid griddy (of one) two rfl with ⟨c, d, e, f, g, i⟩
  have H2 := i_top_bottom f
  rw [H2.1] at g
  rw [H2.2] at i
  specialize three _ _ g
  rw [three.2] at i
  exact ⟨three.1, i⟩

theorem word_top_bottom : ∀ a b c, grid c 1 a b → a = c ∧ b = 1 := by
  intro a b c
  revert a b
  induction c using FreeMonoid'.inductionOn'
  · intro a b h
    exact all_ones h rfl rfl
  intro c d h
  rename_i a b ih
  apply splittable_horizontally_of_grid at h
  specialize h (of a) b rfl
  rcases h with ⟨u, c₁, c₂, h1, h2, h3⟩
  apply i_side_side at h1
  specialize h1 a rfl rfl
  rw [h1.2] at h2
  rw [h1.1] at h3
  specialize ih c₂ d h2
  rw [ih.1] at h3
  rw [h3]
  exact ⟨rfl, ih.2⟩

def ia (a b c d : FreeMonoid' ℕ) := ∀ i j, a = FreeMonoid'.of i → b = FreeMonoid'.of j → (Nat.dist i j = 1) →
  c = FreeMonoid'.of i * FreeMonoid'.of j ∧ d = FreeMonoid'.of j * FreeMonoid'.of i

theorem i_adjacent : grid a b c d → ia a b c d := by
  intro h
  induction h with
  | empty =>
    intro i j h1
    exact ((FreeMonoid'.of_neq_one _).elim h1.symm).elim
  | top_bottom i =>
    intro i j h1
    exact ((FreeMonoid'.of_neq_one _).elim h1.symm).elim
  | sides i =>
    intro i j _ h2
    exact ((FreeMonoid'.of_neq_one _).elim h2.symm).elim
  | top_left i =>
    intro i j h1 h2 d
    rw [FreeMonoid'.of_injective h1.symm, FreeMonoid'.of_injective h2] at d
    simp at d
  | adjacent i k _ =>
    intro i j h1 h2 _
    rw [h1, h2]
    exact ⟨rfl, rfl⟩
  | separated i j h =>
    intro i j h1 h2 d
    rw [FreeMonoid'.of_injective h1.symm, FreeMonoid'.of_injective h2.symm] at d
    have H := or_dist_iff.mpr h
    rw [d] at H
    simp at H
  | vertical h1 h2 h1_ih h2_ih =>
    intro i j ha hb d
    rw [hb] at h1
    rw [hb] at h1_ih
    rcases FreeMonoid.prod_eq_of ha
    · rename_i ua
      rw [ua.1] at h1
      have u'v' := i_top_bottom h1
      rw [ua.2, u'v'.2] at h2_ih
      specialize h2_ih _ _ rfl rfl d
      rw [u'v'.1, h2_ih.1, h2_ih.2, one_mul]
      exact ⟨rfl, rfl⟩
    rename_i ua
    rw [ua.1] at h1_ih
    specialize h1_ih _ _ rfl rfl d
    rw [ua.2, h1_ih.2] at h2
    have H_idk := word_side_side _ _ _ h2
    rw [H_idk.1, H_idk.2, h1_ih.1, mul_one]
    exact ⟨rfl, rfl⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    intro i j ha hb d
    rw [ha] at h1
    rw [ha] at h1_ih
    rcases FreeMonoid.prod_eq_of hb
    · rename_i ua
      rw [ua.1] at h1
      have u'v' := i_side_side h1 _ rfl rfl
      rw [ua.2, u'v'.1] at h2_ih
      specialize h2_ih _ _ rfl rfl d
      rw [u'v'.2, h2_ih.1, h2_ih.2, one_mul]
      exact ⟨rfl, rfl⟩
    rename_i ua
    rw [ua.1] at h1_ih
    specialize h1_ih _ _ rfl rfl d
    rw [ua.2, h1_ih.1] at h2
    have H_idk := word_top_bottom _ _ _ h2
    rw [H_idk.1, H_idk.2, h1_ih.2, mul_one]
    exact ⟨rfl, rfl⟩

def ij_eq (a b c d : FreeMonoid' ℕ) := ∀ k, a = of k → b = of k → (c = 1 ∧ d = 1)

theorem helpier_eq {a b c d : FreeMonoid' ℕ} (h : grid a b c d) : ij_eq a b c d := by
  induction h
  · exact fun _ _ h2 => (of_neq_one _ h2.symm).elim
  · exact fun _ h1 _ => (of_neq_one _ h1.symm).elim
  · exact fun _ _ h2 => (of_neq_one _ h2.symm).elim
  · exact fun _ _ _ => ⟨rfl, rfl⟩
  · intro k eq1 eq2
    rename_i dist
    rw [of_injective (eq1.trans eq2.symm)] at dist
    simp at dist
  · intro k eq1 eq2
    rename_i dist
    rcases dist
    · rename_i ih
      rw [of_injective eq1, of_injective eq2] at ih
      linarith [ih]
    rename_i ih
    rw [of_injective eq1, of_injective eq2] at ih
    linarith [ih]
  · rename_i e f g h i j k l m n o
    intro p eq1 eq2
    rcases FreeMonoid.prod_eq_of eq1
    · rename_i ei
      rw [ei.1, eq2] at l
      have gh := i_top_bottom l
      rw [gh.1]
      rw [gh.2, ei.2] at o
      specialize o p rfl rfl
      rw [o.1, o.2, mul_one]
      exact ⟨rfl, rfl⟩
    rename_i ei
    rw [ei.1, eq2] at n
    specialize n p rfl rfl
    rw [n.1]
    rw [n.2, ei.2] at m
    have jk := all_ones m rfl rfl
    rw [jk.1, jk.2, mul_one]
    exact ⟨rfl, rfl⟩
  rename_i e f g h i j k l m n o
  intro p eq1 eq2
  rcases FreeMonoid.prod_eq_of eq2
  · rename_i fi
    rw [eq1, fi.1] at l
    have gh := i_side_side l p rfl rfl
    rw [gh.1, fi.2] at o
    specialize o p rfl rfl
    rw [o.1, o.2, mul_one]
    exact ⟨rfl, gh.2⟩
  rename_i fi
  rw [eq1, fi.1] at n
  specialize n p rfl rfl
  rw [n.1, fi.2] at m
  have jk := all_ones m rfl rfl
  rw [jk.1, jk.2, n.2]
  exact ⟨rfl, rfl⟩

def ij_close (a b c d : FreeMonoid' ℕ) := ∀ i j, (Nat.dist i j = 1) → a = of i → b = of j →
    (c = of i * of j ∧ d = of j * of i)

-- theorem helpier_close' {c d : FreeMonoid' ℕ} (h1 : Nat.dist i j =1)
--     (h : grid (of i) (of j) c d) : (c = of i * of j ∧ d = of j * of i):= by
--   generalize one : of i = a at h
--   generalize two : of j = b at h
--   induction h with
--   | empty => exact (of_neq_one _ one).elim
--   | top_bottom k => exact (of_neq_one _ one).elim
--   | sides i => exact (of_neq_one _ two).elim
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


theorem helpier_close {a b c d : FreeMonoid' ℕ} (h : grid a b c d) : ij_close a b c d := by
  induction h
  · exact fun _ _ _ one _ => (of_neq_one _ one.symm).elim
  · exact fun _ _ _ one _ => (of_neq_one _ one.symm).elim
  · exact fun _ _ _ _ two => (of_neq_one _ two.symm).elim
  · intro j k dist one two
    rename_i i
    rw [← of_injective one, ← of_injective two] at dist
    simp at dist
  · intro j k _ one two
    rw [← one, ← two]
    exact ⟨rfl, rfl⟩
  · intro j k dist one two
    rename_i e f apart
    rw [← of_injective one, ← of_injective two] at dist
    exfalso
    rcases apart
    · rename_i lt
      rcases or_dist_iff_eq.mp dist
      · rename_i f_is
        rw [← f_is] at lt
        linarith [lt]
      rename_i e_is
      rw [← e_is] at lt
      linarith [lt]
    rename_i gt
    rcases or_dist_iff_eq.mp dist
    · rename_i f_is
      rw [← f_is] at gt
      linarith [gt]
    rename_i e_is
    rw [← e_is] at gt
    linarith [gt]
  · rename_i e f g h i j k l m n o
    intro p q dist one two
    rcases FreeMonoid.prod_eq_of one
    · rename_i ih
      rw [ih.1, two] at l
      rw [ih.1] at n
      have H := i_top_bottom l
      rw [H.1]
      rw [ih.2, H.2] at o
      specialize o _ _ dist rfl rfl
      rw [one_mul]
      exact o
    rename_i ih
    rw [ih.1, two] at n
    specialize n _ _ dist rfl rfl
    rw [n.2, ih.2] at m
    have H := word_side_side _ _ _ m
    rw [H.1, H.2, n.1]
    exact ⟨rfl, rfl⟩
  rename_i e f g h i j k l m n o
  intro p q dist one two
  rcases FreeMonoid.prod_eq_of two
  · rename_i ih
    rw [ih.1, one] at l
    rw [ih.1] at n
    have H := i_side_side l _ rfl rfl
    rw [H.2]
    rw [ih.2, H.1] at o
    specialize o _ _ dist rfl rfl
    rw [one_mul]
    exact o
  rename_i ih
  rw [ih.1, one] at n
  specialize n _ _ dist rfl rfl
  rw [n.1, ih.2] at m
  have H := word_top_bottom _ _ _ m
  rw [H.1, H.2, n.2]
  exact ⟨rfl, rfl⟩

def ij_st (a b c d : FreeMonoid' ℕ) := ∀ i j, (i + 2 <= j ∨ j + 2 <= i) → a = of i → b = of j →
    (c = of i ∧ d = of j)

theorem helpier_ij {a b c d : FreeMonoid' ℕ} (h : grid a b c d) : ij_st a b c d := by
  induction h
  · intro i j _ one two
    exact ⟨one, two⟩
  · intro j k _ one two
    exact ⟨one, two⟩
  · intro i j _ one two
    exact ⟨one, two⟩
  · rename_i i
    intro a b orie one two
    exfalso
    rcases orie
    · linarith [of_injective (one.symm.trans two)]
    linarith [of_injective (one.symm.trans two)]
  · rename_i i
    intro a b or_thing one two
    exfalso
    rcases or_thing
    · rename_i ih
      rw [← of_injective one] at ih
      rw [← of_injective two] at ih
      rcases or_dist_iff_eq.mp i
      · rename_i k_is
        rw [← k_is] at ih
        linarith [ih]
      rename_i k_is
      rw [← k_is] at ih
      linarith [ih]
    rename_i ih
    rw [← of_injective one] at ih
    rw [← of_injective two] at ih
    rcases or_dist_iff_eq.mp i
    · rename_i k_is
      rw [← k_is] at ih
      linarith [ih]
    rename_i k_is
    rw [← k_is] at ih
    linarith [ih]
  · intro _ _ _ one two
    exact ⟨one, two⟩
  · rename_i e f g h i j k l m n o
    intro p q or_thing p_is q_is
    rw [q_is] at n
    rcases FreeMonoid.prod_eq_of p_is
    · rename_i one_way
      rw [one_way.1] at n
      rw [q_is, one_way.1] at l
      have H := i_top_bottom l
      rw [H.1]
      rw [H.2, one_way.2] at o
      specialize o p q or_thing rfl rfl
      rw [o.1]
      exact ⟨rfl, o.2⟩
    rename_i another
    rw [another.1] at n
    specialize n p q or_thing rfl rfl
    rw [n.1]
    rw [n.2, another.2] at o
    unfold ij_st at o
    rw [another.2, n.2] at m
    have H := i_top_bottom m
    rw [H.1]
    exact ⟨rfl, H.2⟩
  rename_i e f g h i j k l m n o
  intro p q or_thing p_is q_is
  rw [p_is] at n
  rcases FreeMonoid.prod_eq_of q_is
  · rename_i one_way
    rw [one_way.1] at n
    rw [p_is, one_way.1] at l
    have H := i_side_side l p rfl rfl
    rw [H.2]
    rw [H.1, one_way.2] at o
    specialize o p q or_thing rfl rfl
    rw [o.1]
    exact ⟨rfl, o.2⟩
  rename_i another
  rw [another.1] at n
  specialize n p q or_thing rfl rfl
  rw [n.2]
  rw [n.1, another.2] at o
  have H := i_side_side m p n.1 another.2
  rw [H.2]
  exact ⟨H.1, rfl⟩

theorem i_both_one : grid a b 1 1 → PresentedMonoid.rel braid_rels_m_inf a b := by
  intro h
  apply PresentedMonoid.exact
  rw [← mul_one a, ← mul_one b]
  exact braid_eq_of_grid h
