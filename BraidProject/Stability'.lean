import BraidProject.GridsTwo'

open FreeMonoid Grid DeterminativeSpine

namespace Braid
namespace Grid

def stable (a b : FreeMonoid ℕ) := ∀ c d, grid a b c d → ∀ a' b',
  BraidMonoidInf.mk a = .mk a' → BraidMonoidInf.mk b = .mk b' → ∃ c' d', grid a' b' c' d' ∧
  BraidMonoidInf.mk c = .mk c' ∧ BraidMonoidInf.mk d = .mk d'

private theorem stable_swap : stable a b → stable b a := by
  intro h c d gr b' a' hb ha
  rcases h d c (swap gr) a' b' ha hb with ⟨d', c', gr', hd, hc⟩
  use c', d'
  exact ⟨swap gr', ⟨hc, hd⟩⟩

private theorem stable_word_one : stable a 1 := by
  intro c d gr a' b' ha hb
  have ⟨hc, hd⟩ := word_one gr
  rw [hc, hd, BraidMonoidInf.one_of_eq_mk_one hb.symm]
  apply PresentedMonoid.exact at ha
  induction ha with
  | of x y bxy =>
    use 1, y
    constructor
    · exact sides_word y
    exact ⟨rfl, PresentedMonoid.sound (.of x y bxy)⟩
  | refl x =>
    use 1, x
    exact ⟨sides_word x, ⟨by rw [hb], rfl⟩⟩
  | symm brxy _ =>
    rename_i x y _
    use 1, x
    exact ⟨sides_word x, ⟨rfl, PresentedMonoid.sound (.symm brxy)⟩⟩
  | trans h1 h2 _ _ =>
    rename_i x y z _ _
    use 1, z
    exact ⟨sides_word z, ⟨rfl, PresentedMonoid.sound (.trans h1 h2)⟩⟩
  | mul h1 h2 _ _ =>
    rename_i x y z w _ _
    use 1, y * w
    exact ⟨sides_word _, ⟨rfl, PresentedMonoid.sound (.mul h1 h2)⟩⟩

private theorem stable_one_word : stable 1 v := stable_swap stable_word_one

private theorem stable_generator_comm_rel (i j k : ℕ) (h : 2 ≤ j.dist k) :
    stable (FreeMonoid.of i) (FreeMonoid.of j * FreeMonoid.of k) := by
  intro c d grid_abcd a' b' ha' hb'
  rw [BraidMonoidInf.singleton_eq ha']
  rcases BraidMonoidInf.length_two_eq hb' with rfl | rfl
  · use c, d
  rcases splittable_vertically grid_abcd (of j) (of k) rfl with ⟨u, c₁, c₂, g1, g2, rfl⟩
  rcases trichotomous_dist i j with ij_dist_ge_two | ij_dist_eq_one | ij_eq
  · have ⟨hc₁, hu⟩ := generator_generator_apart g1 ij_dist_ge_two
    rw [hu] at g2
    rcases trichotomous_dist i k with ik_dist_ge_two | ik_dist_eq_one | ik_eq
    · have ⟨hc₂, hd⟩ := generator_generator_apart g2 ik_dist_ge_two
      use of k * of j, of i
      rw [hd, hc₁, hc₂]
      exact ⟨grid.horizontal (.separated i k ik_dist_ge_two)
        (.separated i j ij_dist_ge_two), ⟨BraidMonoidInf.comm_rw_self _ _ h, rfl⟩⟩
    · use of k * of i * of j, of i * of k
      constructor
      · rw [Nat.dist_comm] at h
        have := grid.vertical (.separated i j ij_dist_ge_two)
          (.separated k j h)
        exact grid.horizontal (.adjacent i k ik_dist_eq_one) this
      have ⟨hc₂, hd⟩ := generator_generator_close g2 ik_dist_eq_one
      rw [hc₁, hc₂, hd]
      constructor
      · simp only [BraidMonoidInf.mk_mul, ← mul_assoc]
        rw [BraidMonoidInf.comm_rw_self j k h, BraidMonoidInf.comm_rw _ j i]
        rw [Nat.dist_comm]
        assumption
      rfl
    rw [ik_eq] at g2
    have ⟨hc₂, hd⟩ := generator_generator_same g2
    rw [hc₁, hd, hc₂, ik_eq]
    use of j, 1
    exact ⟨grid.horizontal (.top_left k) (.top_bottom j), ⟨by rw [mul_one], rfl⟩⟩
  · have ⟨hc₁, hu⟩ := generator_generator_close g1 ij_dist_eq_one
    rw [hu] at g2
    rw [hc₁]
    rcases splittable_horizontally g2 _ _ rfl with ⟨m, d₁, d₂, g3, g4, hd⟩
    rcases trichotomous_dist i k with ik_dist_ge_two | ik_dist_eq_one | ik_eq
    · use of k * of j * of i, of i * of j
      constructor
      · have := grid.horizontal (.separated i k ik_dist_ge_two) (.adjacent i j ij_dist_eq_one)
        exact this
      have ⟨hm, hd₁⟩ := generator_generator_apart g3 ik_dist_ge_two
      rw [hm] at g4
      rcases trichotomous_dist j k with jk_dist_ge_two | jk_dist_eq_one | jk_eq
      · have ⟨hc₂, hd₂⟩ := generator_generator_apart g4 jk_dist_ge_two
        rw [hc₂, hd, hd₁, hd₂]
        constructor
        · simp only [BraidMonoidInf.mk_mul]
          rw [BraidMonoidInf.comm_rw_self k j, BraidMonoidInf.comm_rw _ i k (by assumption)]
          rw [Nat.dist_comm]; assumption
        rfl
      · aesop
      aesop
    · use of k * of i * of j * of i * of k, of i * of j * of k * of i
      constructor
      · apply grid.horizontal (.adjacent i k ik_dist_eq_one)
        apply grid.vertical (.adjacent i j ij_dist_eq_one)
        rw [Nat.dist_comm] at h ik_dist_eq_one
        apply grid.horizontal (.separated k j h) (.adjacent k i ik_dist_eq_one)
      have ⟨hm, hd₁⟩ := generator_generator_close g3 ik_dist_eq_one
      rw [hm] at g4
      rcases splittable_vertically g4 _ _ rfl with ⟨n, c₃, c₄, g5, g6, hc₂⟩
      rw [hc₂]
      have ⟨hc₃, hn⟩ := generator_generator_apart g5 h
      rw [hn] at g6
      rw [Nat.dist_comm] at ij_dist_eq_one
      have ⟨hc₄, hd₂⟩ := generator_generator_close g6 ij_dist_eq_one
      rw [hc₃, hc₄, hd, hd₁, hd₂]
      constructor
      · simp only [BraidMonoidInf.mk_mul, ← mul_assoc]
        rw [BraidMonoidInf.braid_rw _ i k ik_dist_eq_one, BraidMonoidInf.comm_rw_self j k h]
        rw [Nat.dist_comm] at h
        rw [BraidMonoidInf.comm_rw _ k j h, BraidMonoidInf.braid_rw _ j i ij_dist_eq_one]
      simp only [BraidMonoidInf.mk_mul, ← mul_assoc]
      rw [BraidMonoidInf.comm_rw _ j k]
      assumption
    rw [← ik_eq, Nat.dist_comm] at h
    aesop
  rw [ij_eq] at g1
  have ⟨hc₁, hu⟩ := generator_generator_same g1
  rw [hu] at g2
  have ⟨hc₂, hd⟩ := one_generator g2
  rw [hc₁, hc₂, hd]
  rw [← ij_eq]
  rcases trichotomous_dist i k with ik_dist_ge_two | ik_dist_eq_one | ik_eq
  · use of k, 1
    constructor
    · exact grid.horizontal (.separated i k ik_dist_ge_two) (.top_left i)
    aesop
  · use of k * of i, of k
    constructor
    · apply grid.horizontal (.adjacent i k ik_dist_eq_one)
      exact grid.vertical (.top_left i) (.sides k)
    aesop
  use of i, 1
  rw [← ik_eq]
  constructor
  · apply grid.horizontal (.top_left i) (.top_bottom i)
  aesop

private theorem stable_generator_braid_rel (i j k : ℕ) (h : Nat.dist j k = 1) :
    stable (FreeMonoid.of i) (of j * of k * of j) := by
  intro c d grid_abcd a' b' ha hb
  rw [BraidMonoidInf.singleton_eq ha]
  rcases BraidMonoidInf.alternating_length_three_eq h hb with rfl | rfl
  · use c, d
  rcases splittable_vertically grid_abcd (of j * of k) (of j) rfl with
    ⟨u, c₁, c₂, g1, g2, rfl⟩
  rcases splittable_vertically g1 (of j) (of k) rfl with ⟨m, u₁, u₂, g3, g4, rfl⟩
  rcases trichotomous_dist i j with ij_ge_two_apart | ij_one_apart | ij_eq
  · have ⟨hu₁, hm⟩ := generator_generator_apart g3 ij_ge_two_apart
    rw [hm] at g4
    rcases trichotomous_dist i k with ik_ge_two_apart | ik_one_apart | ik_eq
    · have ⟨hu₂, hu⟩ := generator_generator_apart g4 ik_ge_two_apart
      rw [hu] at g2
      have ⟨c₂, d⟩ := generator_generator_apart g2 ij_ge_two_apart
      use of k * of j * of k, of i
      constructor
      · apply grid.horizontal (.separated i k ik_ge_two_apart)
          (.horizontal (.separated i j ij_ge_two_apart)
          (.separated i k ik_ge_two_apart))
      aesop
    · have ⟨hu₂, hu⟩ := generator_generator_close g4 ik_one_apart
      rw [hu] at g2
      rcases splittable_horizontally g2 (of i) (of k) rfl with ⟨n, d₁, d₂, g5, g6, hd⟩
      have ⟨hn, hd₁⟩ := generator_generator_apart g5 ij_ge_two_apart
      rw [hn] at g6
      rw [Nat.dist_comm] at h
      have ⟨hc₂, hd₂⟩ := generator_generator_close g6 h
      use of k * of i * of j * of k * of i, of i * of k * of j
      constructor
      · apply grid.horizontal (.adjacent i k ik_one_apart) (.horizontal
          (.vertical (.separated i j ij_ge_two_apart) (.adjacent k j h))
          (.vertical (.adjacent i k ik_one_apart)
          (.horizontal (.vertical (.top_left k) (.sides j))
          (.vertical (.top_bottom i) (.separated j i _)))))
        rw [Nat.dist_comm] at ij_ge_two_apart
        exact ij_ge_two_apart
      constructor
      · rw [hu₁, hu₂, hc₂]
        simp only [BraidMonoidInf.mk_mul, ← mul_assoc]
        rw [Nat.dist_comm] at ik_one_apart h
        rw [BraidMonoidInf.comm_rw _ i j ij_ge_two_apart, BraidMonoidInf.braid_rw_self j k h,
          BraidMonoidInf.braid_rw _ k i ik_one_apart, BraidMonoidInf.comm_rw _ i j ij_ge_two_apart]
      grind
    rw [Nat.dist_comm] at h
    aesop
  · have ⟨hu₁, hm⟩ := generator_generator_close g3 ij_one_apart
    rw [hm] at g4
    rcases splittable_horizontally g4 (of i) (of j) rfl with ⟨n, u₃, u₄, g5, g6, hu⟩
    rcases trichotomous_dist i k with ik_ge_two_apart | ik_one_apart | ik_eq
    · have ⟨hn, hu₃⟩ := generator_generator_apart g5 ik_ge_two_apart
      rw [hn] at g6
      have ⟨hu₂, hu₄⟩ := generator_generator_close g6 h
      use of k * of j * of i * of k * of j, of i * of j * of k
      constructor
      · apply grid.horizontal (.separated i k ik_ge_two_apart)
          (.horizontal (.adjacent i j ij_one_apart)
          (.vertical (.separated i k ik_ge_two_apart) (.adjacent j k h)))
      rw [hu₁, hu₂]
      rw [hu] at g2
      rcases splittable_horizontally g2 _ _ rfl with ⟨n₁, d₁, d₂, g7, g8, hd⟩
      rw [hu₃] at g7
      rw [hu₄] at g8
      rcases splittable_horizontally g8 _ _ rfl with ⟨n₂, d₃, d₄, g9, g10, hd₂⟩
      have ⟨hn₁, hd₁⟩ := generator_generator_close g7 ij_one_apart
      rw [hn₁] at g9
      rcases splittable_vertically g9 _ _ rfl with ⟨n₃, n₄, n₅, g11, g12, hn₂⟩
      have ⟨hn₄, hn₃⟩ := generator_generator_same g11
      rw [hn₃] at g12
      have ⟨hn₅, hd₃⟩ := one_word g12
      rw [hn₂, hn₄, hn₅, one_mul] at g10
      rw [Nat.dist_comm] at ik_ge_two_apart
      have ⟨hc₂, hd₄⟩ := generator_generator_apart g10 ik_ge_two_apart
      rw [hd, hd₁, hd₂, hd₃, hd₄, hc₂]
      constructor
      · simp only [BraidMonoidInf.mk_mul, ← mul_assoc]
        rw [Nat.dist_comm] at ik_ge_two_apart
        rw [BraidMonoidInf.comm_rw _ i k ik_ge_two_apart,
            BraidMonoidInf.braid_rw _ i j ij_one_apart, BraidMonoidInf.braid_rw_self j k h,
          BraidMonoidInf.comm_rw _ k i]
        rw [Nat.dist_comm]; assumption
      aesop
    · apply (@Nat.dist_no_triangle i j k 1 (by aesop)).elim
      aesop
    rw [ik_eq] at g5
    have ⟨hn, hu₃⟩ := generator_generator_same g5
    rw [hn] at g6
    have ⟨hu₂, hu₄⟩ := generator_one g6
    use of j * of i, 1
    rw [← ik_eq]
    constructor
    · apply grid.horizontal (.top_left i)
        (.horizontal (.top_bottom j) (.top_bottom i))
    rw [hu, hu₃, hu₄, one_mul] at g2
    have ⟨hc₂, hd⟩ := generator_generator_same g2
    aesop
  rw [ij_eq] at g3
  have ⟨hu₁, hm⟩ := generator_generator_same g3
  rw [hm] at g4
  have ⟨hu₂, hu⟩ := one_generator g4
  rw [hu] at g2
  have ⟨hc₂, hd⟩ := one_generator g2
  rw [hu₁, hu₂, hd, hc₂]
  rw [ij_eq]
  use of k * of j, 1
  constructor
  · apply grid.horizontal (.adjacent j k h)
    apply grid.horizontal (.vertical (.top_left j) (.sides k))
    apply grid.vertical (.top_bottom k) (.top_left k)
  exact ⟨rfl, rfl⟩

private theorem stable_generator_elem_braid_rels {w y : FreeMonoid ℕ} (h : braid_monoid_rels_inf w y) :
    ∀ a, stable (of a) w := by
  rcases h
  · exact fun a ↦ stable_generator_braid_rel a _ _ dist_succ
  exact fun a ↦ stable_generator_comm_rel a _ _ (or_dist_iff.mpr (Or.inl (by assumption)))

private theorem stable_generator_elem_braid_rels_symm {w y : FreeMonoid ℕ} (h : braid_monoid_rels_inf y w) :
    ∀ a, stable (of a) w := by
  rcases h
  · intro a
    apply stable_generator_braid_rel
    rw [Nat.dist_comm]
    exact dist_succ
  exact fun a => stable_generator_comm_rel a _ _ (by grind [Nat.dist])

private theorem stable_generator_elem_braid_rels_both {w y : FreeMonoid ℕ}
    (h : braid_monoid_rels_inf y w ∨ braid_monoid_rels_inf w y) :
    ∀ a, stable (of a) w := by
  cases h with
  | inl h => apply stable_generator_elem_braid_rels_symm h
  | inr h => apply stable_generator_elem_braid_rels h

private theorem stable_first_refl_second_one_step_both (ih : ∀ (u v a b : FreeMonoid ℕ), n ≥ u.length + a.length → grid u v a b →
    ∀ (u' v' : FreeMonoid ℕ), BraidMonoidInf.mk u = BraidMonoidInf.mk u' →
    BraidMonoidInf.mk v = BraidMonoidInf.mk v' → ∃ a' b', grid u' v' a' b' ∧
    BraidMonoidInf.mk a = BraidMonoidInf.mk a' ∧ BraidMonoidInf.mk b = BraidMonoidInf.mk b')
    (br : braid_monoid_rels_inf f g ∨ braid_monoid_rels_inf g f) (gr : grid e (i * g * j) c d) (len : n + 1 ≥ e.length + c.length) :
    ∃ a' b', grid e (i * f * j) a' b' ∧
    BraidMonoidInf.mk c = BraidMonoidInf.mk a' ∧ BraidMonoidInf.mk d = BraidMonoidInf.mk b' := by
  rcases splittable_vertically gr _ _ rfl with ⟨u₁, d₄, d₃, first_grid, grid_right, d_is⟩
  rcases splittable_vertically first_grid _ _ rfl with ⟨u, d₁, d₂, grid_left, grid_middle, d₄_is⟩
  cases u
  · use d₁ * f * d₃, 1
    have ⟨rfl, hu₁⟩ := one_word grid_middle
    rw [hu₁] at grid_right
    have ⟨hd₃, rfl⟩ := one_word grid_right
    constructor
    · exact grid.horizontal (.horizontal grid_left (top_bottom_word f)) grid_right
    constructor
    · rw [d_is, d₄_is]
      simp only [BraidMonoidInf.mk_mul]
      congr 2
      rcases br with h1 | h2
      · symm
        apply BraidMonoidInf.sound (ConGen.Rel.of _ _ h1)
      apply BraidMonoidInf.sound (ConGen.Rel.of _ _ h2)
    rfl
  rename_i head tail
  rcases splittable_horizontally grid_middle _ _ rfl with
      ⟨mid, a₁, a₂, gr_top_middle, gr_bottom_middle, rfl⟩
  have fg : BraidMonoidInf.mk g = BraidMonoidInf.mk f := by
    rcases br with h1 | h2
    · symm
      apply PresentedMonoid.sound
      apply ConGen.Rel.of _ _ h1
    apply PresentedMonoid.sound
    apply ConGen.Rel.of _ _ h2
  have := stable_generator_elem_braid_rels_both br head mid a₁ gr_top_middle (of head) f rfl
    fg
  rcases this with ⟨mid', a₁', top_middle_fact⟩
  have H_len : n ≥ tail.length + d₂.length := by
    rw [diag_length_eq gr] at len
    have H1 : (g * j).length + d.length ≤ n + 1 := Nat.le_trans (by simp) len
    rw [← (diag_length_eq (.horizontal (.vertical gr_top_middle gr_bottom_middle)
      grid_right))] at H1
    have : (of head * tail).length + (d₂ * d₃).length > tail.length +
        (d₂ * d₃).length := by simp
    have : tail.length + (d₂ * d₃).length ≥ tail.length + d₂.length := by simp
    linarith
  rcases ih _ _ d₂ a₂ H_len gr_bottom_middle tail mid' rfl top_middle_fact.2.1 with
    ⟨d₂', a₂', bottom_middle_fact⟩
  have H_len : n ≥ (a₁ * a₂).length + d₃.length := by
    rw [diag_length_eq grid_right]
    rw [diag_length_eq gr] at len
    simp only [length_mul] at len
    have : g.length > 0 ∧ f.length > 0 := by
      rcases br with h1 | h2
      · symm
        exact braid_monoid_rels_inf.length_pos h1
      exact braid_monoid_rels_inf.length_pos h2
    linarith [len, this]
  have H_st : BraidMonoidInf.mk (a₁ * a₂) = BraidMonoidInf.mk (a₁' * a₂') :=
    PresentedMonoid.sound <| ConGen.Rel.mul (PresentedMonoid.exact top_middle_fact.2.2)
    (PresentedMonoid.exact bottom_middle_fact.2.2)
  rcases ih (a₁ * a₂) j  d₃ d H_len grid_right _ _ H_st
      rfl with ⟨d₃', c', right_fact⟩
  use  d₁ * d₂' * d₃', c'
  constructor
  · exact grid.horizontal (.horizontal grid_left
      (.vertical top_middle_fact.1 bottom_middle_fact.1)) right_fact.1
  constructor
  · rw [d_is, d₄_is]
    simp only [BraidMonoidInf.mk_mul]
    aesop
  exact right_fact.2.2

-- a grid is stable when the first equivalence is by reflexivity (i.e. a'=a, but b' may not equal b)
private theorem stable_first_refl (ih : ∀ (a b c d : FreeMonoid ℕ), n ≥ a.length + c.length → grid a b c d →
    ∀ (a' b' : FreeMonoid ℕ), BraidMonoidInf.mk a = BraidMonoidInf.mk a' →
    BraidMonoidInf.mk b = BraidMonoidInf.mk b' → ∃ c' d', grid a' b' c' d' ∧
    BraidMonoidInf.mk c = BraidMonoidInf.mk c' ∧ BraidMonoidInf.mk d = BraidMonoidInf.mk d')
    (b_is : BraidMonoidInf.mk x = BraidMonoidInf.mk y) :
    ∀ (c : FreeMonoid ℕ), n + 1 ≥ a.length + c.length →
    ∀ (d : FreeMonoid ℕ), grid a x c d → ∃ a' b', grid a y a' b' ∧
    BraidMonoidInf.mk c = BraidMonoidInf.mk a' ∧ BraidMonoidInf.mk d = BraidMonoidInf.mk b' := by
  apply PresentedMonoid.rel_induction_rw (PresentedMonoid.exact b_is)
  · intro _ c _ d _
    use c, d
  · intro _ _ _ _ br _ len _ gr
    exact stable_first_refl_second_one_step_both ih (Or.inr br) gr len
  · intro _ _ _ _ br
    exact fun _ len _ gr => stable_first_refl_second_one_step_both ih (Or.inl br) gr len
  intro g h k ih' d len c gr
  rcases ih'.1 d len c gr with ⟨c₁, d₁, gr', hd, hc⟩
  have len' : n + 1 ≥ a.length + c₁.length := by
      rw [BraidMonoidInf.length_eq hd] at len
      exact len
  rcases ih'.2 c₁ len' d₁ gr' with ⟨c₂, d₂, gr'', hc₁, hd₁⟩
  use c₂, d₂
  exact ⟨gr'', ⟨hd.trans hc₁, hc.trans hd₁⟩⟩

theorem stability (a b : FreeMonoid ℕ) : stable a b := by
  have H1 : ∀ n a b, ∀ c d, n >= a.length + c.length → grid a b c d → ∀ a' b',
      BraidMonoidInf.mk a = BraidMonoidInf.mk a' →
      BraidMonoidInf.mk b = BraidMonoidInf.mk b' → ∃ c' d',
      grid a' b' c' d' ∧ BraidMonoidInf.mk c = BraidMonoidInf.mk c' ∧
      BraidMonoidInf.mk d = BraidMonoidInf.mk d' := by
    intro n
    induction n with
    | zero =>
      intro a _ _ _ length
      have : a.length = 0 := by linarith [length]
      rw [FreeMonoid.length_eq_zero.mp this]
      exact stable_one_word _ _
    | succ n ih =>
      intro a b c d _ _ a₁ b₁ a_is b_is
      revert c; revert d; revert b
      apply PresentedMonoid.rel_induction_rw (PresentedMonoid.exact a_is)
      · intro _ b b_is d c len gr
        exact stable_first_refl ih b_is _ len _ gr
      · intro g i e f br b b_is d c len gr
        have bd_len : n + 1 ≥ b.length + d.length := by
          rw [← diag_length_eq gr]
          exact len
        rcases stable_first_refl_second_one_step_both ih (Or.inr br) (swap gr) bd_len with ⟨a1, b1, swapped_grid, da, cb⟩
        apply swap at swapped_grid
        have b1_len : n + 1 ≥ (e * i * f).length + b1.length := by
          simp only [length_mul] at len
          simp only [length_mul]
          rw [← BraidMonoidInf.length_eq cb, ← BraidMonoidInf.length_eq
              (PresentedMonoid.sound (PresentedMonoid.rels_alone br))]
          assumption
        rcases stable_first_refl ih b_is b1 b1_len a1 swapped_grid with ⟨a2, b2, gr', hb1, ha1⟩
        use a2, b2
        exact ⟨gr', ⟨cb.trans hb1, da.trans ha1⟩⟩
      · intro x y g i br b b_is d c len gr
        have bd_len : n + 1 ≥ b.length + d.length := by
          rw [← diag_length_eq gr]
          exact len
        rcases stable_first_refl_second_one_step_both ih (Or.inl br) (swap gr) bd_len with ⟨a1, b1, swapped_grid, da, cb⟩
        apply swap at swapped_grid
        have b1_len : n + 1 ≥ (g * y * i).length + b1.length := by
          simp only [length_mul] at len
          simp only [length_mul]
          rw [← BraidMonoidInf.length_eq cb, BraidMonoidInf.length_eq
                (PresentedMonoid.sound (PresentedMonoid.rels_alone br))]
          assumption
        rcases stable_first_refl ih b_is b1 b1_len a1 swapped_grid with ⟨a2, b2, gr', hb1, ha1⟩
        use a2, b2
        exact ⟨gr', ⟨cb.trans hb1, da.trans ha1⟩⟩
      intro _ b1 c1 ih b b_is d c len gr
      rcases ih.1 b b_is d c len gr with ⟨d₁, c₁, gr', hc, hd⟩
      have H_len : n + 1 ≥ b1.length + d₁.length := by
        have Hb : b₁.length = b.length := congr_arg BraidMonoidInf.length b_is.symm
        have Hc : c₁.length = d.length := congr_arg BraidMonoidInf.length hd.symm
        rw [← diag_length_eq (swap gr'), Hb, Hc, ← diag_length_eq gr]
        exact len
      rcases ih.2 b₁ rfl c₁ d₁ H_len gr' with ⟨d₂, c₂, gr'', hd₁, hc₁⟩
      use d₂, c₂
      exact ⟨gr'', ⟨hc.trans hd₁, hd.trans hc₁⟩⟩
  exact fun c d => H1 (a.length + c.length) a b c d (Nat.le_refl _)
