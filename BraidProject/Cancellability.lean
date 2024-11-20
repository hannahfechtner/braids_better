import BraidProject.Stability

theorem simpler_grid (u v u' v' : FreeMonoid' ℕ) (h : grid u v u' v') :
    grid (u * v')  (v * u') 1 1 := by
  rcases (stability _ _ 1 1 (grid_top_left_word (u * v')) _ _ rfl (braid_eq_of_grid h)) with
      ⟨a, b, griddy, ha, hb⟩
  rw [BraidMonoidInf.one_of_eq_mk_one ha.symm, BraidMonoidInf.one_of_eq_mk_one hb.symm] at griddy
  exact griddy

theorem grid_of_eq {u v u' v' : FreeMonoid' ℕ} (h : BraidMonoidInf.mk (u * v') = BraidMonoidInf.mk (v * u')) :
    grid (u * v') (v * u') 1 1 := by
  rcases (stability _ _ 1 1 (grid_top_left_word (u * v')) _ _ rfl h) with
      ⟨a, b, griddy, ha, hb⟩
  rw [BraidMonoidInf.one_of_eq_mk_one ha.symm, BraidMonoidInf.one_of_eq_mk_one hb.symm] at griddy
  exact griddy

theorem left_cancellative (a b c : PresentedMonoid braid_rels_m_inf) (h1 : c * a = c * b) : a = b := by
  induction' a with a'
  induction' b with b'
  induction' c with c'
  induction' c' using FreeMonoid'.inductionOn' with d e f
  · change BraidMonoidInf.mk _ = BraidMonoidInf.mk _ at h1
    simp only [FreeMonoid'.length_one, one_mul] at h1
    exact h1
  change BraidMonoidInf.mk _ = BraidMonoidInf.mk _ at h1
  simp at h1
  apply f
  rw [mul_assoc, mul_assoc] at h1
  have H := grid_of_eq h1
  rcases splittable_horizontally_of_grid H _ _ rfl with ⟨middle, f₁, f₂, g₁, g₂, f_is⟩
  rw [(FreeMonoid.prod_eq_one f_is.symm).1] at g₁
  rw [(FreeMonoid.prod_eq_one f_is.symm).2] at g₂
  rcases splittable_vertically_of_grid g₁ _ _ rfl with ⟨s₁, m₁, m₂, g₃, g₄, middle_is⟩
  rcases splittable_vertically_of_grid g₂ _ _ middle_is with ⟨s₂, o₁, o₂, g₅, g₆, bot_is⟩
  have s₁m₁ := i_top_left g₃ _ rfl rfl
  rw [s₁m₁.2] at g₅
  rw [s₁m₁.1] at g₄
  have m₂_is := word_side_side _ _ _ g₄
  have s₂o₁_is := word_top_bottom _ _ _ g₅
  rw [m₂_is.2, s₂o₁_is.1, (FreeMonoid.prod_eq_one bot_is.symm).2] at g₆
  have h7 := braid_eq_of_grid g₆
  rw [mul_one, mul_one] at h7
  exact h7

theorem right_cancellative (a b c : PresentedMonoid braid_rels_m_inf) (h1 : a * c = b * c) : a = b := by
  apply BraidMonoidInf.eq_iff_reverse_eq_reverse.mp at h1
  rw [BraidMonoidInf.reverse_braid_mul, BraidMonoidInf.reverse_braid_mul] at h1
  exact BraidMonoidInf.eq_iff_reverse_eq_reverse.mpr (left_cancellative _ _ _ h1)

theorem unicity (h1 : grid a b c d) : ∀ c' d', grid a b c' d' → c' = c ∧ d' = d := by
  induction h1 with
  | empty => exact fun _ _ h2 => all_ones h2 rfl rfl
  | top_bottom i => exact fun _ _ h2 => i_top_bottom h2
  | sides i => exact fun _ _ h2 =>  i_side_side h2 _ rfl rfl
  | top_left i => exact fun _ _ h2 => i_top_left h2 _ rfl rfl
  | adjacent i k h => exact fun _ _ three => helpier_close three _ _ h rfl rfl
  | separated i j h =>
    intro one two three
    exact helpier_ij three _ _ h rfl rfl
  | vertical _ _ h_ih h'_ih =>
    intro c' d' gr
    rcases splittable_horizontally_of_grid gr _ _ rfl with ⟨u, c₁, c₂, gr1, gr2, c_is⟩
    have c₁u := h_ih c₁ u gr1
    rw [c₁u.2] at gr2
    rw [c_is, c₁u.1, (h'_ih c₂ d' gr2).1, (h'_ih c₂ d' gr2).2]
    exact ⟨rfl, rfl⟩
  | horizontal _ _ h_ih h'_ih =>
    intro c' d' gr
    rcases splittable_vertically_of_grid gr _ _ rfl with ⟨u, c₁, c₂, gr1, gr2, c_is⟩
    have c₁u := h_ih u c₁ gr1
    rw [c₁u.1] at gr2
    rw [c_is, c₁u.2, (h'_ih c' c₂ gr2).1, (h'_ih c' c₂ gr2).2]
    exact ⟨rfl, rfl⟩

theorem common_mul (a b : FreeMonoid' ℕ) : ∃ c d, a * c = b * d := sorry

theorem existence : ∀ a b, ∃ c d, grid a b c d := by
  intro a b
  rcases common_mul a b with ⟨c1, d1, h⟩
  have big_grid : grid (a * c1) (b * d1) 1 1 := by
    apply grid_of_eq
    rw [h]
  rcases splittable_horizontally_of_grid big_grid _ _ rfl with ⟨_, c₁, c₂, top_grid, _, side_one⟩
  rw [(FreeMonoid.prod_eq_one side_one.symm).1] at top_grid
  rcases splittable_vertically_of_grid top_grid _ _ rfl with ⟨top_vert, m₁, m₂, top_left, _, _⟩
  use top_vert, m₁

-- theorem existence_common_mul (a b c d e f : FreeMonoid' ℕ) (h1 : grid a b c d) (h2 : a * e = b * f) :
--   ∃ g, BraidMonoidInf.mk ((a * d) * g) = BraidMonoidInf.mk (a * e) := by
--   have big_grid : grid (a * e) (b * f) 1 1 := by
--     apply grid_of_eq
--     rw [h2]
--   rcases splittable_horizontally_of_grid big_grid _ _ rfl with ⟨middle, c₁, c₂, top_grid, bottom_grid, side_one⟩
--   rw [(FreeMonoid.prod_eq_one side_one.symm).1] at top_grid
--   rcases splittable_vertically_of_grid top_grid _ _ rfl with ⟨top_vert, m₁, m₂, top_left, top_right, mid_is⟩
--   rw [mid_is] at bottom_grid
--   rcases splittable_vertically_of_grid bottom_grid _ _ rfl with ⟨bot_vert, d₁, d₂, bottom_left, bottom_right, d_is⟩
--   use bot_vert
--   apply PresentedMonoid.sound
--   rw [mul_assoc]
--   apply Con'Gen.Rel.mul (Con'Gen.Rel.refl _)
--   sorry

-- theorem existence : ∀ a b, ∃ c d, grid a b c d := by
--   sorry

-- ome of these fields (like one_mul
-- should be set up once I ge the regular monoid things done
instance : CancelMonoid (PresentedMonoid braid_rels_m_inf) where
    mul_right_cancel := fun a b c => right_cancellative a c b
    mul_left_cancel := fun a b c => left_cancellative b c a
    -- what the ? ?
    one_mul := one_mul
    mul_one := mul_one
