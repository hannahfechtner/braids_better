import BraidProject.GridsTwo'
open FreeMonoid Braid Grid DeterminativeSpine

def stable (a b : FreeMonoid ℕ) := ∀ c d, grid a b c d → ∀ a' b',
  BraidMonoidInf.mk a = BraidMonoidInf.mk a' →
  BraidMonoidInf.mk b = BraidMonoidInf.mk b' → ∃ c' d',
    grid a' b' c' d' ∧ BraidMonoidInf.mk c = BraidMonoidInf.mk c' ∧
    BraidMonoidInf.mk d = BraidMonoidInf.mk d'

theorem stable_apart (i j k : ℕ) (h : j.dist k >= 2) :
    stable (FreeMonoid.of i) (FreeMonoid.of j * FreeMonoid.of k) := by
  intro c d grid_abcd a' b' ha' hb'
  rw [BraidMonoidInf.singleton_eq ha']
  rcases BraidMonoidInf.pair_eq h hb' with ⟨rfl⟩ | ⟨rfl⟩
  · use c, d
  rcases splittable_vertically grid_abcd (of j) (of k) rfl with ⟨u, c₁, c₂, g1, g2, rfl⟩
  rcases trichotomous_dist i j with ij_ge_two_apart | ij_one_apart | ij_eq
  · have ⟨hc₁, hu⟩ := generator_generator_apart g1 ij_ge_two_apart
    rw [hu] at g2
    rcases trichotomous_dist i k with ik_ge_two_apart | ik_one_apart | ik_eq
    · have ⟨hc₂, hd⟩ := generator_generator_apart g2 ik_ge_two_apart
      use of k * of j, of i
      rw [hd, hc₁, hc₂]
      exact ⟨grid.horizontal (grid.separated i k ik_ge_two_apart)
        (grid.separated i j ij_ge_two_apart),
        ⟨PresentedMonoid.sound (BraidMonoidInf.comm_rel h), rfl⟩⟩
    · use of k * of i * of j, of i * of k
      constructor
      · rw [Nat.dist_comm] at h
        have H := (grid.vertical (grid.separated i j ij_ge_two_apart)
          (grid.separated k j h))
        exact grid.horizontal (grid.adjacent i k ik_one_apart) H
      have ⟨hc₂, hd⟩ := generator_generator_close g2 ik_one_apart
      rw [hc₁, hc₂, hd]
      constructor
      · apply PresentedMonoid.sound
        have : PresentedMonoid.rel braid_rels_m_inf (of j * (of k * of i))
            (of k * (of j * of i)) := by
          rw [← mul_assoc, ← mul_assoc]
          apply ConGen.Rel.mul
          · exact BraidMonoidInf.comm_rel h
          exact ConGen.Rel.refl _
        apply this.trans
        rw [mul_assoc]
        apply ConGen.Rel.mul
        · exact ConGen.Rel.refl _
        apply BraidMonoidInf.comm_rel
        rw [Nat.dist_comm] at ij_ge_two_apart
        exact ij_ge_two_apart
      rfl
    rw [ik_eq] at g2
    have ⟨hc₂, hd⟩ := generator_generator_same g2
    rw [hc₁, hd, hc₂, ik_eq]
    use of j, 1
    exact ⟨grid.horizontal (grid.top_left k) (grid.top_bottom j), ⟨by rw [mul_one], rfl⟩⟩
  · have ⟨hc₁, hu⟩ := generator_generator_close g1 ij_one_apart
    rw [hu] at g2
    rw [hc₁]
    rcases splittable_horizontally g2 _ _ rfl with ⟨m, d₁, d₂, g3, g4, hd⟩
    rcases trichotomous_dist i k with ik_ge_two_apart | ik_one_apart | ik_eq
    · use of k * of j * of i, of i * of j
      constructor
      · have := grid.horizontal (grid.separated i k ik_ge_two_apart) (grid.adjacent i j ij_one_apart)
        exact this
      have ⟨hm, hd₁⟩ := generator_generator_apart g3 ik_ge_two_apart
      rw [hm] at g4
      rcases trichotomous_dist j k with jk_ge_two_apart | jk_one_apart | jk_eq
      · have ⟨hc₂, hd₂⟩ := generator_generator_apart g4 jk_ge_two_apart
        rw [hc₂, hd, hd₁, hd₂]
        constructor
        · have : BraidMonoidInf.mk (of j * of i * of k) = BraidMonoidInf.mk (of j * of k * of i) := by
            rw [mul_assoc, mul_assoc]
            apply PresentedMonoid.sound
            apply ConGen.Rel.mul (ConGen.Rel.refl _) (BraidMonoidInf.comm_rel _)
            aesop
          apply this.trans
          apply PresentedMonoid.sound
          apply ConGen.Rel.mul (BraidMonoidInf.comm_rel _) (ConGen.Rel.refl _)
          aesop
        rfl
      · aesop
      aesop
    · use of k * of i * of j * of i * of k, of i * of j * of k * of i
      constructor
      · apply grid.horizontal (grid.adjacent i k ik_one_apart)
        apply grid.vertical (grid.adjacent i j ij_one_apart)
        rw [Nat.dist_comm] at h ik_one_apart
        apply grid.horizontal (grid.separated k j h)
        exact (grid.adjacent k i ik_one_apart)
      have ⟨hm, hd₁⟩ := generator_generator_close g3 ik_one_apart
      rw [hm] at g4
      rcases splittable_vertically g4 _ _ rfl with ⟨n, c₃, c₄, g5, g6, hc₂⟩
      rw [hc₂]
      have ⟨hc₃, hn⟩ := generator_generator_apart g5 h
      rw [hn] at g6
      rw [Nat.dist_comm] at ij_one_apart
      have ⟨hc₄, hd₂⟩ := generator_generator_close g6 ij_one_apart
      rw [hc₃, hc₄, hd, hd₁, hd₂]
      constructor
      · rw [← mul_assoc, ← mul_assoc]
        have : BraidMonoidInf.mk (of j * of i * of k * of i * of j) =
            BraidMonoidInf.mk (of j * of k * of i * of k * of j) := by
          apply PresentedMonoid.sound
          apply ConGen.Rel.mul _ (ConGen.Rel.refl _)
          rw [mul_assoc, mul_assoc]
          apply ConGen.Rel.mul (ConGen.Rel.refl _)
          apply BraidMonoidInf.braid_rel ik_one_apart
        apply this.trans
        have : BraidMonoidInf.mk (of j * of k * of i * of k * of j) =
            BraidMonoidInf.mk (of k * of j * of i * of k * of j) := by
          apply PresentedMonoid.sound
          apply ConGen.Rel.mul _ (ConGen.Rel.refl _)
          apply ConGen.Rel.mul _ (ConGen.Rel.refl _)
          apply ConGen.Rel.mul _ (ConGen.Rel.refl _)
          apply BraidMonoidInf.comm_rel
          assumption
        apply this.trans
        have : BraidMonoidInf.mk (of k * of j * of i * of k * of j) =
            BraidMonoidInf.mk (of k * of j * of i * of j * of k) := by
          rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
          apply PresentedMonoid.sound
          apply ConGen.Rel.mul (ConGen.Rel.refl _)
          apply ConGen.Rel.mul (ConGen.Rel.refl _)
          apply ConGen.Rel.mul (ConGen.Rel.refl _)
          apply BraidMonoidInf.comm_rel
          rw [Nat.dist_comm]
          assumption
        apply this.trans
        apply PresentedMonoid.sound
        apply ConGen.Rel.mul _ (ConGen.Rel.refl _)
        rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
        apply ConGen.Rel.mul (ConGen.Rel.refl _)
        apply BraidMonoidInf.braid_rel
        aesop
      apply PresentedMonoid.sound
      rw [← mul_assoc]
      apply ConGen.Rel.mul _ (ConGen.Rel.refl _)
      rw [mul_assoc, mul_assoc]
      apply ConGen.Rel.mul (ConGen.Rel.refl _)
      apply BraidMonoidInf.comm_rel
      rw [Nat.dist_comm]
      assumption
    rw [← ik_eq, Nat.dist_comm] at h
    aesop
  rw [ij_eq] at g1
  have ⟨hc₁, hu⟩ := generator_generator_same g1
  rw [hu] at g2
  have ⟨hc₂, hd⟩ := one_generator g2
  rw [hc₁, hc₂, hd]
  rw [← ij_eq]
  rcases trichotomous_dist i k with ik_ge_two_apart | ik_one_apart | ik_eq
  · use of k, 1
    constructor
    · exact grid.horizontal (grid.separated i k ik_ge_two_apart) (grid.top_left i)
    aesop
  · use of k * of i, of k
    constructor
    · apply grid.horizontal (grid.adjacent i k ik_one_apart)
      exact grid.vertical (grid.top_left i) (grid.sides k)
    aesop
  use of i, 1
  rw [← ik_eq]
  constructor
  · apply grid.horizontal (grid.top_left i) (grid.top_bottom i)
  aesop

theorem stable_close (i j k : ℕ) (h : Nat.dist j k = 1) :
    stable (FreeMonoid.of i) (of j * of k * of j) := by
  intro c d grid_abcd a' b' ha hb
  rw [BraidMonoidInf.singleton_eq ha]
  rcases BraidMonoidInf.triplet_eq h hb with rfl | rfl
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
      · apply grid.horizontal (grid.separated i k ik_ge_two_apart)
          (grid.horizontal (grid.separated i j ij_ge_two_apart)
          (grid.separated i k ik_ge_two_apart))
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
      · apply grid.horizontal (grid.adjacent i k ik_one_apart) (grid.horizontal
          (grid.vertical (grid.separated i j ij_ge_two_apart) (grid.adjacent k j h))
          (grid.vertical (grid.adjacent i k ik_one_apart)
          (grid.horizontal (grid.vertical (grid.top_left k) (grid.sides j))
          (grid.vertical (grid.top_bottom i) (grid.separated j i _)))))
        rw [Nat.dist_comm] at ij_ge_two_apart
        exact ij_ge_two_apart
      constructor
      · rw [hu₁, hu₂, hc₂]
        apply PresentedMonoid.sound
        have H1 : PresentedMonoid.rel braid_rels_m_inf (of j * (of k * of i) * (of j * of k))
            ((of j * of k * of j) * (of i * of k)) := by
          conv => lhs; rw [← mul_assoc, ← mul_assoc, mul_assoc _ (of i)]
          conv => rhs; rw [← mul_assoc, mul_assoc _ (of j)]
          exact ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _) (BraidMonoidInf.comm_rel ij_ge_two_apart))
            (ConGen.Rel.refl _)
        have H3 : PresentedMonoid.rel braid_rels_m_inf ((of k * of j * of k) * (of i * of k))
            (of k * of j * (of i * of k * of i)) := by
          conv => lhs; rw [mul_assoc]
          apply ConGen.Rel.mul (ConGen.Rel.refl _)
          rw [← mul_assoc]
          exact ConGen.Rel.symm (BraidMonoidInf.braid_rel ik_one_apart)
        have H4 : PresentedMonoid.rel braid_rels_m_inf (of k * of j * (of i * of k * of i))
            (of k * of i * of j * of k * of i) := by
          rw [← mul_assoc, ← mul_assoc, mul_assoc (of k) (of j), mul_assoc (of k) (of i)]
          exact ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _)
            (ConGen.Rel.symm (BraidMonoidInf.comm_rel ij_ge_two_apart))) (ConGen.Rel.refl _))
            (ConGen.Rel.refl _)
        apply H1.trans
        apply ConGen.Rel.trans _ H4
        apply ConGen.Rel.trans _ H3
        apply ConGen.Rel.mul (ConGen.Rel.symm (BraidMonoidInf.braid_rel h)) (ConGen.Rel.refl _)
      aesop
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
      · apply grid.horizontal (grid.separated i k ik_ge_two_apart)
          (grid.horizontal (grid.adjacent i j ij_one_apart)
          (grid.vertical (grid.separated i k ik_ge_two_apart) (grid.adjacent j k h)))
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
      · rw [Nat.dist_comm] at ik_ge_two_apart
        apply PresentedMonoid.sound
        have H1 : PresentedMonoid.rel braid_rels_m_inf (of j * of i * (of k * of j) * of i)
            (of j * of k * (of i * of j * of i)) := by
          rw [← mul_assoc, ← mul_assoc (of j * of k), ← mul_assoc (of j * of k), mul_assoc _ (of i),
            mul_assoc _ (of k)]
          exact ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _)
            (BraidMonoidInf.comm_rel ik_ge_two_apart)) (ConGen.Rel.refl _)) (ConGen.Rel.refl _)
        have H2 := ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl (of j)) (ConGen.Rel.refl (of k)))
            (BraidMonoidInf.braid_rel ij_one_apart)
        have H3 : PresentedMonoid.rel braid_rels_m_inf (of j * of k * (of j * of i * of j))
            (of k * of j * of k * of i * of j) := by
          conv => lhs; rw [mul_assoc (of j) (of i), ← mul_assoc (of j * of k)]
          conv => rhs; rw [mul_assoc _ (of i)]
          exact ConGen.Rel.mul (BraidMonoidInf.braid_rel h) (ConGen.Rel.refl _)
        have H4 : PresentedMonoid.rel braid_rels_m_inf (of k * of j * of k * of i * of j)
            (of k * of j * of i * of k * of j) := by
          conv => rhs; rw [mul_assoc _ (of i)]
          rw [mul_assoc _ (of k)]
          exact ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _)
            (ConGen.Rel.symm (BraidMonoidInf.comm_rel ik_ge_two_apart))) (ConGen.Rel.refl _)
        exact H1.trans (H2.trans (H3.trans H4))
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
    · apply grid.horizontal (grid.top_left i)
        (grid.horizontal (grid.top_bottom j) (grid.top_bottom i))
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
  · apply grid.horizontal (grid.adjacent j k h)
    apply grid.horizontal (grid.vertical (grid.top_left j) (grid.sides k))
    apply grid.vertical (grid.top_bottom k) (grid.top_left k)
  exact ⟨rfl, rfl⟩

theorem stable_swap : stable a b → stable b a := by
  intro h c d gr b' a' hb ha
  rcases h d c (swap gr) a' b' ha hb with ⟨d', c', gr', hd, hc⟩
  use c', d'
  exact ⟨swap gr', ⟨hc, hd⟩⟩

theorem stable_word_one : stable a 1 := by
  intro c d gr a' b' ha hb
  have ⟨hc, hd⟩ := word_one gr
  rw [hc, hd, BraidMonoidInf.one_of_eq_mk_one hb.symm]
  apply PresentedMonoid.exact at ha
  induction ha with
  | of x y bxy =>
    use 1, y
    constructor
    · exact sides_word y
    exact ⟨rfl, PresentedMonoid.sound (ConGen.Rel.of x y bxy)⟩
  | refl x =>
    use 1, x
    exact ⟨sides_word x, ⟨by rw [hb], rfl⟩⟩
  | symm brxy _ =>
    rename_i x y _
    use 1, x
    exact ⟨sides_word x, ⟨rfl, PresentedMonoid.sound (ConGen.Rel.symm brxy)⟩⟩
  | trans h1 h2 _ _ =>
    rename_i x y z _ _
    use 1, z
    exact ⟨sides_word z, ⟨rfl, PresentedMonoid.sound (ConGen.Rel.trans h1 h2)⟩⟩
  | mul h1 h2 _ _ =>
    rename_i x y z w _ _
    use 1, y * w
    exact ⟨sides_word _, ⟨rfl, PresentedMonoid.sound (ConGen.Rel.mul h1 h2)⟩⟩

theorem stable_one_word : stable 1 v := stable_swap stable_word_one

theorem stable_braid_elem {w y : FreeMonoid ℕ} (h : braid_rels_m_inf w y) :
    ∀ a, stable (of a) w := by
  rcases h
  · exact fun a ↦ stable_close a _ _ dist_succ
  exact fun a ↦ stable_apart a _ _ (or_dist_iff.mpr (Or.inl (by assumption)))

theorem stable_braid_elem_symm {w y : FreeMonoid ℕ} (h : braid_rels_m_inf y w) :
    ∀ a, stable (of a) w := by
  rcases h
  · intro a
    apply stable_close
    rw [Nat.dist_comm]
    exact dist_succ
  exact fun a => stable_apart a _ _ (or_dist_iff.mpr (Or.inr (by assumption)))

theorem reg_helper (ih : ∀ (a b c d : FreeMonoid ℕ),
    n ≥ a.length + c.length →
      grid a b c d →
        ∀ (a' b' : FreeMonoid ℕ),
          BraidMonoidInf.mk a = BraidMonoidInf.mk a' →
            BraidMonoidInf.mk b = BraidMonoidInf.mk b' →
              ∃ c' d',
                grid a' b' c' d' ∧
                  BraidMonoidInf.mk c = BraidMonoidInf.mk c' ∧ BraidMonoidInf.mk d = BraidMonoidInf.mk d')
    (br : braid_rels_m_inf f g) (gr : grid e (i * f * j) c d) (len : n + 1 ≥ e.length + c.length) :
    ∃ a' b', grid e (i * g * j) b' a' ∧
    BraidMonoidInf.mk c = BraidMonoidInf.mk a' ∧ BraidMonoidInf.mk d = BraidMonoidInf.mk b' := by
  rcases splittable_vertically gr _ _ rfl with ⟨u₁, d₄, d₃, first_grid, grid_right, d_is⟩
  have H_split1 := splittable_vertically first_grid _ _ rfl
  rcases H_split1 with ⟨u, d₁, d₂, grid_left, grid_middle, d₄_is⟩
  induction u using FreeMonoid.inductionOn'
  · use d₁ * g * d₃, 1
    have H := one_word grid_middle
    rw [H.2] at grid_right
    rw [H.1] at d₄_is
    have H := one_word grid_right
    rw [H.1] at grid_right
    rw [H.1]
    constructor
    · exact grid.horizontal (grid.horizontal grid_left (top_bottom_word g)) grid_right
    constructor
    · rw [d_is, d₄_is]
      apply PresentedMonoid.sound
      exact ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _) (ConGen.Rel.of _ _ br))
        (ConGen.Rel.refl _)
    simp_all
  rename_i head tail ih_bad
  have H_split := splittable_horizontally_of_grid grid_middle _ _ rfl
  rcases H_split with ⟨mid, a₁, a₂, gr_top_middle, gr_bottom_middle, u₁_is⟩
  have H := stable_braid_elem br head a₁ mid gr_top_middle (of head) g rfl
    (PresentedMonoid.sound (ConGen.Rel.of _ _ br))
  rcases H with ⟨a₁', mid', top_middle_fact⟩
  have H_len : n ≥ tail.length + d₂.length := by
    have two : e.length + d.length = (i * f * j).length + c.length := by
      have H := grid_diag_length_eq gr
      simp only [length_mul] at H
      simp only [length_mul]
      exact H
    rw [two] at len
    have H3 : (i * f * j).length + c.length >= (f * j).length + c.length := by simp
    have H35 : (f * j).length + c.length <= n + 1 := Nat.le_trans H3 len
    have H4 : (f * j).length + c.length = (of head * tail).length + (d₂ * d₃).length := by
      rw [u₁_is] at grid_right
      have H := grid_diag_length_eq (grid.horizontal
        (grid.vertical gr_top_middle gr_bottom_middle) grid_right)
      simp only [length_mul] at H
      simp only [length_mul]
      exact H.symm
    have H45 : (of head * tail).length + (d₂ * d₃).length <= n + 1 := by
      rw [H4] at H35
      exact H35
    have H5 : (of head * tail).length + (d₂ * d₃).length > tail.length +
        (d₂ * d₃).length := by simp
    have H6 : tail.length + (d₂ * d₃).length >= tail.length + d₂.length := by simp
    exact Nat.le_of_lt_succ (Nat.lt_of_le_of_lt H6 (Nat.lt_of_lt_of_le H5 H45))
  rcases ih _ _ a₂ d₂ H_len gr_bottom_middle tail mid' rfl top_middle_fact.2.2 with
    ⟨a₂', d₂', bottom_middle_fact⟩
  rw [u₁_is] at grid_right
  have H_len : n ≥ (a₁ * a₂).length + d₃.length := by
    have one : (a₁ * a₂).length + d₃.length = j.length + c.length := by
      have H := grid_diag_length_eq grid_right
      simp only [length_mul] at H
      simp only [length_mul]
      exact H
    rw [one]
    have two : e.length + d.length = (i * f * j).length + c.length := by
      have H := grid_diag_length_eq gr
      simp only [length_mul] at H
      simp only [length_mul]
      exact H
    rw [two] at len
    simp only [length_mul] at len
    -- why on earth does this not work here???
    -- have H : f.length > 0 := by
    --   rcases br
    --     · simp
    --     simp
    linarith [len, length_pos br]
  have H_st : BraidMonoidInf.mk (a₁ * a₂) = BraidMonoidInf.mk (a₁' * a₂') :=
    PresentedMonoid.sound <| ConGen.Rel.mul (PresentedMonoid.exact top_middle_fact.2.1)
    (PresentedMonoid.exact bottom_middle_fact.2.1)
  rcases ih (a₁ * a₂) j  c d₃ H_len grid_right _ _ H_st rfl with ⟨c', d₃', right_fact⟩
  use c', d₁ * d₂' * d₃'
  constructor
  · exact grid.horizontal (grid.horizontal grid_left
      (grid.vertical top_middle_fact.1 bottom_middle_fact.1)) right_fact.1
  constructor
  · exact right_fact.2.1
  rw [d_is, d₄_is]
  exact PresentedMonoid.sound <| ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl d₁)
    (PresentedMonoid.exact bottom_middle_fact.right.right)) (PresentedMonoid.exact right_fact.2.2)

theorem symm_helper (ih : ∀ (u v a b : FreeMonoid ℕ), n ≥ u.length + b.length → grid u v a b →
    ∀ (u' v' : FreeMonoid ℕ), BraidMonoidInf.mk u = BraidMonoidInf.mk u' →
    BraidMonoidInf.mk v = BraidMonoidInf.mk v' → ∃ a' b', grid u' v' a' b' ∧
    BraidMonoidInf.mk a = BraidMonoidInf.mk a' ∧ BraidMonoidInf.mk b = BraidMonoidInf.mk b')
    (br : braid_rels_m_inf f g) (gr : grid e (i * g * j) c d) (len : n + 1 ≥ e.length + c.length) :
    ∃ a' b', grid e (i * f * j) a' b' ∧
    BraidMonoidInf.mk c = BraidMonoidInf.mk a' ∧ BraidMonoidInf.mk d = BraidMonoidInf.mk b' := by
  have H_split := splittable_vertically_of_grid gr _ _ rfl
  rcases H_split with ⟨u₁, d₄, d₃, first_grid, grid_right, d_is⟩
  have H_split1 := splittable_vertically_of_grid first_grid _ _ rfl
  rcases H_split1 with ⟨u, d₁, d₂, grid_left, grid_middle, d₄_is⟩
  induction u using FreeMonoid.inductionOn'
  · use 1, d₁ * f * d₃
    have H := word_side_side _ _ _ grid_middle
    rw [H.1] at grid_right
    rw [H.2] at d₄_is
    have H := word_side_side _ _ _ grid_right
    rw [H.1] at grid_right
    rw [H.1]
    constructor
    · exact grid.horizontal (grid.horizontal grid_left (grid_top_bottom_word f)) grid_right
    constructor
    · rfl
    rw [d_is, d₄_is]
    exact PresentedMonoid.sound <| ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _)
      (ConGen.Rel.symm (ConGen.Rel.of _ _ br))) (ConGen.Rel.refl _)
  rename_i head tail ih_bad
  have H_split := splittable_horizontally_of_grid grid_middle _ _ rfl
  rcases H_split with ⟨mid, a₁, a₂, gr_top_middle, gr_bottom_middle, u₁_is⟩
  have H := stable_braid_elem_symm br head a₁ mid gr_top_middle (of head) f rfl
    (PresentedMonoid.sound (ConGen.Rel.symm (ConGen.Rel.of _ _ br)))
  rcases H with ⟨a₁', mid', top_middle_fact⟩
  have H_len : n ≥ tail.length + d₂.length := by
    have two : e.length + d.length = (i * g * j).length + c.length := by
      have H := grid_diag_length_eq gr
      simp only [length_mul] at H
      simp only [length_mul]
      exact H
    rw [two] at len
    have H3 : (i * g * j).length + c.length >= (g * j).length + c.length := by simp
    have H35 : (g * j).length + c.length <= n + 1 := Nat.le_trans H3 len
    have H4 : (g * j).length + c.length = (of head * tail).length + (d₂ * d₃).length := by
      rw [u₁_is] at grid_right
      have H := grid_diag_length_eq (grid.horizontal
        (grid.vertical gr_top_middle gr_bottom_middle) grid_right)
      simp only [length_mul] at H
      simp only [length_mul]
      exact H.symm
    have H45 : (of head * tail).length + (d₂ * d₃).length <= n + 1 := by
      rw [H4] at H35
      exact H35
    have H5 : (of head * tail).length + (d₂ * d₃).length > tail.length +
        (d₂ * d₃).length := by simp
    have H6 : tail.length + (d₂ * d₃).length >= tail.length + d₂.length := by simp
    exact Nat.le_of_lt_succ (Nat.lt_of_le_of_lt H6 (Nat.lt_of_lt_of_le H5 H45))
  rcases ih _ _ a₂ d₂ H_len gr_bottom_middle tail mid' rfl top_middle_fact.2.2 with
    ⟨a₂', d₂', bottom_middle_fact⟩
  rw [u₁_is] at grid_right
  have H_len : n ≥ (a₁ * a₂).length + d₃.length := by
    have one : (a₁ * a₂).length + d₃.length = j.length + c.length := by
      have H := grid_diag_length_eq grid_right
      simp only [length_mul] at H
      simp only [length_mul]
      exact H
    rw [one]
    have two : e.length + d.length = (i * g * j).length + c.length := by
      have H := grid_diag_length_eq gr
      simp only [length_mul] at H
      simp only [length_mul]
      exact H
    rw [two] at len
    simp at len
    have H : g.length > 0 := by
      rcases br
      · simp
      simp
    linarith [len, H]
  have H_st : BraidMonoidInf.mk (a₁ * a₂) = BraidMonoidInf.mk (a₁' * a₂') :=
    PresentedMonoid.sound <| ConGen.Rel.mul (PresentedMonoid.exact top_middle_fact.2.1)
    (PresentedMonoid.exact bottom_middle_fact.2.1)
  rcases ih (a₁ * a₂) j  c d₃ H_len grid_right _ _ H_st rfl with ⟨c', d₃', right_fact⟩
  use c', d₁ * d₂' * d₃'
  constructor
  · exact grid.horizontal (grid.horizontal grid_left
      (grid.vertical top_middle_fact.1 bottom_middle_fact.1)) right_fact.1
  constructor
  · exact right_fact.2.1
  rw [d_is, d₄_is]
  apply PresentedMonoid.sound <| ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl d₁)
    (PresentedMonoid.exact bottom_middle_fact.right.right)) (PresentedMonoid.exact right_fact.2.2)

-- a grid is stable when only the second element moves
theorem stable_second (ih : ∀ (u v a b : FreeMonoid ℕ), n ≥ u.length + a.length → grid u v a b →
    ∀ (u' v' : FreeMonoid ℕ), BraidMonoidInf.mk u = BraidMonoidInf.mk u' →
    BraidMonoidInf.mk v = BraidMonoidInf.mk v' → ∃ a' b', grid u' v' a' b' ∧
    BraidMonoidInf.mk a = BraidMonoidInf.mk a' ∧ BraidMonoidInf.mk b = BraidMonoidInf.mk b')
    (b_is : BraidMonoidInf.mk f = BraidMonoidInf.mk i) :
    ∀ (d : FreeMonoid ℕ), n + 1 ≥ a.length + d.length →
    ∀ (c : FreeMonoid ℕ), grid a f d c → ∃ a' b', grid a i b' a' ∧
    BraidMonoidInf.mk c = BraidMonoidInf.mk a' ∧ BraidMonoidInf.mk d = BraidMonoidInf.mk b' := by
  apply PresentedMonoid.rel_induction_rw (PresentedMonoid.exact b_is)
  · intro _ d _ c _
    use c, d
  · intro _ _ _ _ br
    exact fun _ len _ gr => reg_helper ih br gr len
  · intro _ _ _ _ br
    exact fun _ len _ gr => symm_helper ih br gr len
  · intro g h k l d len c gr
    rcases l.1 d len c gr with ⟨c₁, d₁, first_fact⟩
    have len' : n + 1 ≥ a.length + d₁.length := by
      rw [BraidMonoidInf.length_eq first_fact.2.2] at len
      exact len
    rcases l.2 d₁ len' c₁ first_fact.1 with ⟨c₂, d₂, second_fact⟩
    use c₂, d₂
    exact ⟨second_fact.1, ⟨first_fact.2.1.trans second_fact.2.1,
      first_fact.2.2.trans second_fact.2.2⟩⟩

theorem stability (a b : FreeMonoid ℕ) : stable a b := by
  have H1 : ∀ t a b (c d : FreeMonoid ℕ), t ≥ a.length + c.length →
    grid a b c d → ∀ a' b',
    BraidMonoidInf.mk a = BraidMonoidInf.mk a' →
    BraidMonoidInf.mk b = BraidMonoidInf.mk b' → ∃ c' d',
      grid a' b' c' d' ∧ BraidMonoidInf.mk c = BraidMonoidInf.mk c' ∧
      BraidMonoidInf.mk d = BraidMonoidInf.mk d' := by
    intro t
    induction t with
    | zero =>
      intro a b c d length
      have : a.length = 0 := by linarith [length]
      rw [FreeMonoid.length_eq_zero.mp this]
      exact stable_one_word _ _
    | succ n ih =>
      intro a b c d len gr_abcd a₁ b₁ a_is b_is
      revert b; revert c; revert d
      apply PresentedMonoid.rel_induction_rw (PresentedMonoid.exact a_is)
      · intro a b a_is
        sorry
      · sorry
      · sorry
      sorry
  exact fun c d => H1 (a.length + c.length) a b c d (by simp)

theorem stability (a b : FreeMonoid ℕ) : stable a b := by
  have H1 : ∀ t a b  c d, t ≥ a.length + c.length → grid a b c d → ∀ a' b',
      BraidMonoidInf.mk a = BraidMonoidInf.mk a' →
      BraidMonoidInf.mk b = BraidMonoidInf.mk b' → ∃ c' d',
      grid a' b' c' d' ∧ BraidMonoidInf.mk c = BraidMonoidInf.mk c' ∧
      BraidMonoidInf.mk d = BraidMonoidInf.mk d' := by
    intro t
    induction t with
    | zero =>
      intro a b c d length
      have : a.length = 0 := by linarith [length]
      rw [FreeMonoid.length_eq_zero.mp this]
      exact stable_one_word _ _
    | succ n ih =>
      intro a b c d len gr_abcd a₁ b₁ a_is b_is
      revert d; revert c; revert b
      apply PresentedMonoid.rel_induction_rw (PresentedMonoid.exact a_is)
      · intro a b b_is
        sorry
      · intro a2 b2 c2 d2 br2 b3 b3_is c3 len d3 gr
        have easy_len : n + 1 ≥ b3.length + d3.length := by
          rw [← diag_length_eq gr]
          exact len
        rcases reg_helper ih br2 (swap gr) easy_len with ⟨a1, b1, swapped_grid, da, cb⟩
        apply swap at swapped_grid
        have easy_len2 : n + 1 ≥ (c2 * b2 * d2).length + b1.length := by
          simp only [length_mul] at len
          simp only [length_mul]
          rw [← BraidMonoidInf.length_eq cb]
          rw [← BraidMonoidInf.length_eq (PresentedMonoid.sound (PresentedMonoid.rel_alone br2))]
          exact len
        rcases stable_second ih b3_is b1 easy_len2 a1 swapped_grid with ⟨a2, b2, second_fact⟩
        use b2, a2
        exact ⟨second_fact.1, ⟨cb.trans second_fact.2.2, da.trans second_fact.2.1⟩⟩
      · intro _ _ g i br b b_is d len c gr
        have easy_len : n + 1 ≥ b.length + c.length := by
          sorry
        rcases symm_helper ih br (swap gr) easy_len with ⟨a1, b1, swapped_grid, da, cb⟩
        apply swap at swapped_grid
        rename_i x x2
        have easy_len2 : n + 1 ≥ (g * x2 * i).length + b1.length := by
          simp only [length_mul] at len
          simp only [length_mul]
          rw [← BraidMonoidInf.length_eq da, BraidMonoidInf.length_eq (PresentedMonoid.sound (PresentedMonoid.rel_alone br))]
          assumption
        rcases stable_second ih b_is b1 easy_len2 a1 swapped_grid with ⟨a2, b2, second_fact⟩
        use b2, a2
        exact ⟨second_fact.1, ⟨cb.trans second_fact.2.2, da.trans second_fact.2.1⟩⟩
      · intro ha1 hb1 hc1 ih b b_is d len c gr
        rcases ih.1 b b_is d len c gr with ⟨c₁, d₁, first_fact⟩
        have H_len : n + 1 ≥ hb1.length + d₁.length := by
          have Hb : b₁.length = b.length := (congr_arg BraidMonoidInf.length b_is).symm
          have Hc : c₁.length = c.length := (congr_arg BraidMonoidInf.length first_fact.2.1).symm
          rw [← diag_length_eq (swap first_fact.1), Hb, Hc, ← grid_diag_length_eq gr]
          exact len
        rcases ih.2 b₁ rfl d₁ H_len c₁ first_fact.1 with ⟨c₂, d₂, second_fact⟩
        use c₂, d₂
        exact ⟨second_fact.1, ⟨first_fact.2.1.trans second_fact.2.1,
          first_fact.2.2.trans second_fact.2.2⟩⟩
  exact fun c d => H1 (u.length + c.length) u v c d (by simp)
