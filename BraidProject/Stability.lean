import BraidProject.GridsTwo
open FreeMonoid'

def stable (u v : FreeMonoid' ℕ) := ∀ a b, grid u v a b → ∀ u' v',
  BraidMonoidInf_mk u = BraidMonoidInf_mk u' →
  BraidMonoidInf_mk v = BraidMonoidInf_mk v' → ∃ a' b',
    grid u' v' a' b' ∧ BraidMonoidInf_mk a = BraidMonoidInf_mk a' ∧
    BraidMonoidInf_mk b = BraidMonoidInf_mk b'

theorem stable_far_apart (i j k : ℕ) (h : Nat.dist j k >= 2) :
    stable (FreeMonoid'.of i) (FreeMonoid'.of j * FreeMonoid'.of k) := by
  intro a b grid_uvab u' v' u_eq v_eq
  rw [singleton_eq u_eq]
  rcases pair_eq h v_eq with ⟨one, two, three, four⟩
  · use a, b
  rename_i working_h
  rw [working_h]
  rcases splittable_vertically_of_grid grid_uvab (of j) (of k) rfl with ⟨u, d, f, h1, h2, rfl⟩
  rcases trichotomous_dist i j
  · rcases trichotomous_dist i k
    · rename_i hij hik
      have ud := helpier_ij h1 _ _ (or_dist_iff.mp hij) rfl rfl
      rw [ud.1] at h2
      have af := helpier_ij h2 _ _ (or_dist_iff.mp hik) rfl rfl
      rw [ud.2, af.1, af.2]
      use of i, of k * of j
      exact ⟨grid.horizontal (grid.separated i k (or_dist_iff.mp hik))
        (grid.separated i j (or_dist_iff.mp hij)),
        ⟨rfl, PresentedMonoid.sound (BraidMonoidInf.comm h)⟩⟩
    rename_i last_two
    rcases last_two
    · rename_i one two
      have ud := helpier_ij h1 _ _ (or_dist_iff.mp one) rfl rfl
      rw [ud.1] at h2
      rw [ud.2]
      use of i * of k, of k * of i * of j
      constructor
      · rw [Nat.dist_comm] at h
        have H := (grid.vertical (grid.separated i j (or_dist_iff.mp one))
          (grid.separated k j (or_dist_iff.mp h)))
        exact grid.horizontal (grid.adjacent i k two) H
      have H := helpier_close h2 i k two rfl rfl
      constructor
      · rw [H.1]
      rw [H.2]
      apply PresentedMonoid.sound
      rw [mul_assoc]
      have H1 : PresentedMonoid.rel braid_rels_m_inf (of j * (of k * of i)) (of k * (of j * of i))
          := by
        rw [← mul_assoc, ← mul_assoc]
        apply Con'Gen.Rel.mul
        · exact BraidMonoidInf.comm h
        exact Con'Gen.Rel.refl _
      apply H1.trans
      apply Con'Gen.Rel.mul
      · exact Con'Gen.Rel.refl _
      exact BraidMonoidInf.comm (by rw [Nat.dist_comm] at one; exact one)
    rename_i hij hik
    have ud := helpier_ij h1 _ _ (or_dist_iff.mp hij) rfl rfl
    rw [ud.1, hik] at h2
    have af := helpier_eq h2 _ rfl rfl
    rw [af.1, af.2, hik, ud.2]
    use 1, of j
    exact ⟨grid.horizontal (grid.top_left k) (grid.top_bottom j), ⟨rfl, by rw [mul_one]⟩⟩
  rename_i last_two
  rcases last_two
  · rcases trichotomous_dist i k
    · rename_i one two
      use of i * of j, of k * of j * of i
      constructor
      · apply grid.horizontal (grid.separated i k (or_dist_iff.mp two)) (grid.adjacent i j one)
      have ud := helpier_close h1 i j one rfl rfl
      rw [ud.1] at h2
      rw [ud.2]
      have H_split := splittable_horizontally_of_grid h2 (of i) (of j) rfl
      rcases H_split with ⟨u₁, c₁, c₂, ha, hb, hc⟩
      have c₁u₁ := helpier_ij ha _ _ (or_dist_iff.mp two) rfl rfl
      rw [c₁u₁.2] at hb
      have c₂f := helpier_ij hb _ _ (or_dist_iff.mp h) rfl rfl
      rw [c₁u₁.1, c₂f.1] at hc
      rw [hc, c₂f.2]
      constructor
      · rfl
      apply PresentedMonoid.sound
      have H1 : PresentedMonoid.rel braid_rels_m_inf (of j * of i * of k) (of j * of k * of i) := by
        rw [mul_assoc, mul_assoc]
        apply Con'Gen.Rel.mul (Con'Gen.Rel.refl _) (BraidMonoidInf.comm two)
      exact H1.trans <| Con'Gen.Rel.mul (BraidMonoidInf.comm h) (Con'Gen.Rel.refl _)
    rename_i last_two
    rcases last_two
    · rename_i hij hik
      have ud := helpier_close h1 _ _ hij rfl rfl
      rw [ud.2]
      rw [ud.1] at h2
      have H_split := splittable_horizontally_of_grid h2 (of i) (of j) rfl
      rcases H_split with ⟨u₁, c₁, c₂, ha, hb, hc⟩
      have c₁u₁ := helpier_close ha _ _ hik rfl rfl
      rw [c₁u₁.2] at hb
      have second_split := splittable_vertically_of_grid hb (of k) (of i) rfl
      rcases second_split with ⟨u₂, d₁, d₂, ha, hb, hc⟩
      have u₂d₁ := helpier_ij ha _ _ (or_dist_iff.mp h) rfl rfl
      rw [u₂d₁.1] at hb
      have c₂d₂ := helpier_close hb j i
      rw [Nat.dist_comm] at hij
      specialize c₂d₂ hij rfl rfl
      use of i * of j * of k * of i, of k * of i * of j * of i * of k
      constructor
      · rw [Nat.dist_comm] at hij
        apply grid.horizontal (grid.adjacent i k hik) (grid.vertical (grid.adjacent i j hij)
          (grid.horizontal (grid.separated k j
          (or_dist_iff.mp (by rw [Nat.dist_comm] at h; exact h)))
          (grid.adjacent k i (by rw [Nat.dist_comm] at hik; exact hik))))
      constructor
      · rename_i a_is
        rw [a_is, c₁u₁.1, c₂d₂.1]
        rw [mul_assoc, mul_assoc, mul_assoc]
        apply PresentedMonoid.sound
        apply Con'Gen.Rel.mul
        · exact Con'Gen.Rel.refl _
        rw [← mul_assoc, ← mul_assoc]
        apply Con'Gen.Rel.mul
        · apply BraidMonoidInf.comm
          rw [Nat.dist_comm] at h
          exact h
        exact Con'Gen.Rel.refl _
      rw [hc, c₂d₂.2, u₂d₁.2]
      apply PresentedMonoid.sound
      have H1 : PresentedMonoid.rel braid_rels_m_inf (of j * of i * (of k * (of i * of j)))
          ((of j * of k) * of i * (of k * of j)) := by
        rw [mul_assoc, mul_assoc, mul_assoc]
        apply Con'Gen.Rel.mul (Con'Gen.Rel.refl _)
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
        exact Con'Gen.Rel.mul (BraidMonoidInf.braid hik) (Con'Gen.Rel.refl _)
      have H2 : PresentedMonoid.rel braid_rels_m_inf ((of j * of k) * of i * (of k * of j))
          (of k * (of j * of i * of j) * of k) := by
        conv => lhs; rw [mul_assoc]
        conv => rhs; rw [← mul_assoc, ← mul_assoc, mul_assoc, mul_assoc]
        exact Con'Gen.Rel.mul (BraidMonoidInf.comm h) (Con'Gen.Rel.mul (Con'Gen.Rel.refl _)
          (Con'Gen.Rel.symm (BraidMonoidInf.comm h)))
      have H3 : PresentedMonoid.rel braid_rels_m_inf (of k * (of j * of i * of j) * of k)
          (of k * of i * of j * of i * of k) := by
        --why does apply work here, but not exact? somehow apply must be doing some mul_assoc rewrites?
        apply Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl _) (BraidMonoidInf.braid hij))
          (Con'Gen.Rel.refl _)
      exact (H1.trans H2).trans H3
    rename_i one two
    rw [two, Nat.dist_comm k j] at one
    rw [one] at h
    linarith [h]
  rcases trichotomous_dist i k
  · rename_i one two
    use 1, (of k * 1)
    rw [one]
    constructor
    · apply grid.horizontal _ (grid.top_left j)
      apply grid.separated
      rw [← one]
      exact or_dist_iff.mp two
    rw [one] at h1
    have ud := helpier_eq h1 _ rfl rfl
    rw [ud.1] at h2
    have af := i_top_bottom h2 _ rfl rfl
    rw [ud.2, af.1, af.2, mul_one, one_mul]
    exact ⟨rfl, rfl⟩
  rename_i last_two
  rcases last_two
  · rename_i one two
    rw [← one, two] at h
    linarith [h]
  rename_i one two
  rw [← one, ← two] at h
  simp at h

theorem stable_close (i j k : ℕ) (h : Nat.dist j k = 1) :
    stable (FreeMonoid'.of i) (of j * of k * of j) := by
  intro a b grid_uvab u' v' u_eq v_eq
  rw [singleton_eq u_eq]
  rcases triplet_eq h v_eq with ⟨one, two, three, four⟩
  · use a, b
  rename_i working_h
  rw [working_h]
  rcases splittable_vertically_of_grid grid_uvab (of j * of k) (of j) rfl with
    ⟨u, d, f, h2, h3, rfl⟩
  rcases splittable_vertically_of_grid h2 (of j) (of k) rfl with ⟨v, e, g, h0, h1, rfl⟩
  rcases trichotomous_dist i j
  · rename_i hij
    have ve := helpier_ij h0 _ _ (or_dist_iff.mp hij) rfl rfl
    rw [ve.1] at h1
    rcases trichotomous_dist i k
    · rename_i hik
      have ug := helpier_ij h1 _ _ (or_dist_iff.mp hik) rfl rfl
      rw [ug.1] at h3
      have af := helpier_ij h3 _ _ (or_dist_iff.mp hij) rfl rfl
      use of i, of k * of j * of k
      constructor
      · apply grid.horizontal (grid.separated i k (or_dist_iff.mp hik))
          (grid.horizontal (grid.separated i j (or_dist_iff.mp hij))
          (grid.separated i k (or_dist_iff.mp hik)))
      constructor
      · rw [af.1]
      rw [ve.2, ug.2, af.2]
      apply PresentedMonoid.sound
      exact BraidMonoidInf.braid h
    rename_i hik
    rcases hik
    · rename_i hik
      have ug := helpier_close h1 _ _ hik rfl rfl
      rw [ug.1] at h3
      have H_split := splittable_horizontally_of_grid h3 (of i) (of k) rfl
      rcases H_split with ⟨w, c₁, c₂, ha, hb, hc⟩
      have c₁w := helpier_ij ha _ _ (or_dist_iff.mp hij) rfl rfl
      rw [c₁w.2] at hb
      have c₂f := helpier_close hb _ _ (by rw [Nat.dist_comm] at h; exact h) rfl rfl
      use of i * of k * of j, of k * of i * of j * of k * of i
      constructor
      · apply grid.horizontal (grid.adjacent i k hik) (grid.horizontal
        (grid.vertical (grid.separated i j _) (grid.adjacent k j _))
        (grid.vertical (grid.adjacent i k hik)
        (grid.horizontal (grid.vertical (grid.top_left k) (grid.sides j))
        (grid.vertical (grid.top_bottom i) (grid.separated j i (or_dist_iff.mp _))))))
        · exact or_dist_iff.mp hij
        · rw [Nat.dist_comm] at h
          exact h
        rw [Nat.dist_comm] at hij
        exact hij
      constructor
      · rw [hc, c₁w.1, c₂f.1, mul_assoc]
      rw [ve.2, ug.2, c₂f.2]
      apply PresentedMonoid.sound
      have H1 : PresentedMonoid.rel braid_rels_m_inf (of j * (of k * of i) * (of j * of k))
          ((of j * of k * of j) * (of i * of k)) := by
        conv => lhs; rw [← mul_assoc, ← mul_assoc, mul_assoc _ (of i)]
        conv => rhs; rw [← mul_assoc, mul_assoc _ (of j)]
        exact Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl _) (BraidMonoidInf.comm hij))
          (Con'Gen.Rel.refl _)
      have H3 : PresentedMonoid.rel braid_rels_m_inf ((of k * of j * of k) * (of i * of k))
          (of k * of j * (of i * of k * of i)) := by
        conv => lhs; rw [mul_assoc]
        apply Con'Gen.Rel.mul (Con'Gen.Rel.refl _)
        rw [← mul_assoc]
        exact Con'Gen.Rel.symm (BraidMonoidInf.braid hik)
      have H4 : PresentedMonoid.rel braid_rels_m_inf (of k * of j * (of i * of k * of i))
          (of k * of i * of j * of k * of i) := by
        rw [← mul_assoc, ← mul_assoc, mul_assoc (of k) (of j), mul_assoc (of k) (of i)]
        exact Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl _)
          (Con'Gen.Rel.symm (BraidMonoidInf.comm hij))) (Con'Gen.Rel.refl _)) (Con'Gen.Rel.refl _)
      exact H1.trans ((Con'Gen.Rel.mul (BraidMonoidInf.braid h) (Con'Gen.Rel.refl _)).trans
        (H3.trans H4))
    rename_i k_is
    rw [k_is, Nat.dist_comm, h] at hij
    linarith [hij]
  rename_i hij
  rcases hij
  · rename_i hij
    have ve := helpier_close h0 _ _ hij rfl rfl
    rw [ve.1] at h1
    have H_split := splittable_horizontally_of_grid h1 (of i) (of j) rfl
    rcases H_split with ⟨u₁, c₁, c₂, ha, hb, hc⟩
    rcases trichotomous_dist i k
    · rename_i hik
      have c₁u₁ := helpier_ij ha _ _ (or_dist_iff.mp hik) rfl rfl
      rw [c₁u₁.2] at hb
      have c₂g := helpier_close hb _ _ h rfl rfl
      rw [ve.2, c₂g.2]
      rw [hc, c₁u₁.1, c₂g.1] at h3
      have H_split := splittable_horizontally_of_grid h3 _ _ rfl
      rcases H_split with ⟨u₂, d₁, d₂, hd, he, hf⟩
      have d₁u₂ := helpier_close hd _ _ hij rfl rfl
      rw [d₁u₂.2] at he
      have H_split := splittable_horizontally_of_grid he _ _ rfl
      rcases H_split with ⟨u₃, e₁, e₂, hg, hh, hi⟩
      have H_split := splittable_vertically_of_grid hg _ _ rfl
      rcases H_split with ⟨u₄, f₁, f₂, hj, hk, hl⟩
      have u₄f₁ := helpier_eq hj _ rfl rfl
      rw [u₄f₁.1] at hk
      have e₁f₂ := i_top_bottom hk i rfl rfl
      rw [u₄f₁.2, e₁f₂.2, one_mul] at hl
      rw [hl] at hh
      have e₂f := helpier_ij hh _ _
        (or_dist_iff.mp (by rw [Nat.dist_comm] at hik; exact hik)) rfl rfl
      rw [hf, d₁u₂.1, hi, e₁f₂.1, e₂f.1, e₂f.2]
      use of i * of j * of k, of k * of j * of i * of k * of j
      constructor
      -- again, why does exact not work here?
      · apply grid.horizontal (grid.separated i k (or_dist_iff.mp hik))
          (grid.horizontal (grid.adjacent i j hij)
          (grid.vertical (grid.separated i k (or_dist_iff.mp hik)) (grid.adjacent j k h)))
      constructor
      · rw [one_mul, mul_assoc]
      apply PresentedMonoid.sound
      have H1 : PresentedMonoid.rel braid_rels_m_inf (of j * of i * (of k * of j) * of i)
          (of j * of k * (of i * of j * of i)) := by
        rw [← mul_assoc, ← mul_assoc (of j * of k), ← mul_assoc (of j * of k), mul_assoc _ (of i),
          mul_assoc _ (of k)]
        exact Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl _)
          (BraidMonoidInf.comm hik)) (Con'Gen.Rel.refl _)) (Con'Gen.Rel.refl _)
      have H2 := Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl (of j)) (Con'Gen.Rel.refl (of k)))
          (BraidMonoidInf.braid hij)
      have H3 : PresentedMonoid.rel braid_rels_m_inf (of j * of k * (of j * of i * of j))
          (of k * of j * of k * of i * of j) := by
        conv => lhs; rw [mul_assoc (of j) (of i), ← mul_assoc (of j * of k)]
        conv => rhs; rw [mul_assoc _ (of i)]
        exact Con'Gen.Rel.mul (BraidMonoidInf.braid h) (Con'Gen.Rel.refl _)
      have H4 : PresentedMonoid.rel braid_rels_m_inf (of k * of j * of k * of i * of j)
          (of k * of j * of i * of k * of j) := by
        conv => rhs; rw [mul_assoc _ (of i)]
        rw [mul_assoc _ (of k)]
        exact Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl _)
          (Con'Gen.Rel.symm (BraidMonoidInf.comm hik))) (Con'Gen.Rel.refl _)
      exact H1.trans (H2.trans (H3.trans H4))
    rename_i hik
    rcases hik
    · rename_i hik
      rcases or_dist_iff_eq.mp h
      · rename_i jk
        rcases or_dist_iff_eq.mp hij
        · rename_i ij
          rw [← jk, ← ij, Nat.dist_two] at hik
          linarith [hik]
        rename_i ij
        rw [jk.symm.trans ij] at hik
        simp at hik
      rename_i jk
      rcases or_dist_iff_eq.mp hij
      · rename_i ij
        have H : i = k := by linarith [ij, jk]
        rw [H] at hik
        simp at hik
      rename_i ij
      rw [← jk] at ij
      rw [← ij, Nat.dist_comm, Nat.dist_two] at hik
      linarith [hik]
    rename_i k_is
    rw [← k_is] at h
    rw [← k_is] at ha
    have c₁u₁ := helpier_eq ha _ rfl rfl
    rw [c₁u₁.2] at hb
    have c₂g := i_side_side hb _ rfl rfl
    rw [hc, c₁u₁.1, c₂g.1, one_mul] at h3
    have af := helpier_eq h3 _ rfl rfl
    rw [af.1, af.2, ve.2, c₂g.2, ← k_is, mul_one, mul_one]
    use 1, of j * of i
    constructor
    · apply grid.horizontal (grid.top_left i)
        (grid.horizontal (grid.top_bottom j) (grid.top_bottom i))
    exact ⟨rfl, rfl⟩
  rename_i j_is
  rw [← j_is] at h0
  have ve := helpier_eq h0 _ rfl rfl
  rw [ve.1] at h1
  have ug := i_top_bottom h1 _ rfl rfl
  rw [ug.1] at h3
  have af := i_top_bottom h3 _ rfl rfl
  rw [ve.2, one_mul, ug.2, af.1, af.2, j_is]
  rcases trichotomous_dist i k
  · rename_i hik
    rw [j_is, h] at hik
    linarith [hik]
  rename_i hik
  rcases hik
  · rename_i _
    use 1, of k * of j
    constructor
    · apply grid.horizontal (grid.adjacent j k h) (grid.horizontal
        (grid.vertical (grid.top_left j) (grid.sides k))
        (grid.vertical (grid.top_bottom k) (grid.top_left k)))
    exact ⟨rfl, rfl⟩
  rename_i k_is
  rw [j_is.symm.trans k_is]
  use 1, of k * of k
  constructor
  · apply grid.horizontal (grid.top_left k)
      (grid.horizontal (grid.top_bottom k) (grid.top_bottom k))
  exact ⟨rfl, rfl⟩

--use this to derive stable_second_one from stable_first_one, or vice versa.
-- for now, keeping both long ways as they use different methods.

theorem stable_swap : stable u v → stable v u := by
  intro h c d gr v' u' v_is u_is
  rcases h d c (grid_swap gr) u' v' u_is v_is with ⟨a1, b1, fact⟩
  use b1, a1
  exact ⟨grid_swap fact.1, ⟨fact.2.2, fact.2.1⟩⟩

theorem stable_first_one : stable 1 v := by
  intro a b griddy new_u new_v nu nv
  induction v using FreeMonoid'.inductionOn'
  · use 1, 1
    constructor
    · rw [one_of_eq_mk_one nu.symm, one_of_eq_mk_one nv.symm]
      exact grid.empty
    rw [(all_ones griddy rfl rfl).1, (all_ones griddy rfl rfl).2]
    exact ⟨rfl, rfl⟩
  rw [one_of_eq_mk_one nu.symm]
  unfold BraidMonoidInf_mk at nv
  rename_i c d e
  have Ha : a = 1 := (word_side_side _ _ _ griddy).1
  have Hb : b = of c * d := (word_side_side _ _ _ griddy).2
  apply PresentedMonoid.exact at nv
  revert nv
  generalize h : of c * d = k
  intro nv
  rw [Ha, Hb]
  induction nv with
  | of x y _ =>
    rename_i br
    use 1, y
    constructor
    · exact grid_top_bottom_word _
    · rw [h]
      exact ⟨rfl, PresentedMonoid.sound (Con'Gen.Rel.of x y br)⟩
  | refl x =>
    use 1, x
    exact  ⟨grid_top_bottom_word _, ⟨rfl, by rw [h]⟩⟩
  | symm one _ =>
    rename_i z _ _
    use 1, z
    constructor
    · exact grid_top_bottom_word _
    constructor
    · rfl
    rw [h]
    exact PresentedMonoid.sound (Con'Gen.Rel.symm one)
  | trans one two _ =>
    rename_i o _ _
    rw [h]
    use 1, o
    exact
      ⟨grid_top_bottom_word o, ⟨rfl, PresentedMonoid.sound (Con'Gen.Rel.trans one two)⟩⟩
  | mul one two _ _ =>
    rename_i n _ p _ _
    rw [h]
    use 1, n * p
    exact ⟨grid_top_bottom_word (n * p), ⟨rfl, PresentedMonoid.sound (Con'Gen.Rel.mul one two)⟩⟩

theorem stable_second_one : stable a 1 := by
  intro c d gr u v nu nv
  rw [(word_top_bottom _ _ _ gr).2]
  have Hc : c = a := (word_top_bottom _ _ _ gr).1
  rw [Hc]
  rw [← Hc] at nu
  apply PresentedMonoid.exact at nu
  rw [one_of_eq_mk_one nv.symm]
  induction nu
  · rename_i e f g
    use f, 1
    constructor
    · exact grid_sides_word f
    constructor
    · rw [← Hc]
      exact PresentedMonoid.sound (Con'Gen.Rel.of e f g)
    rfl
  · rename_i e
    use e, 1
    exact ⟨grid_sides_word _, ⟨by rw [Hc], rfl⟩⟩
  · rename_i e f g _
    use e, 1
    exact ⟨grid_sides_word _, ⟨by rw [← Hc]; exact PresentedMonoid.sound (Con'Gen.Rel.symm g), rfl⟩⟩
  · rename_i e f g i j _ _
    use g, 1
    constructor
    · exact grid_sides_word _
    constructor
    · rw [← Hc]
      exact PresentedMonoid.sound <| i.trans j
    rfl
  · rename_i e f i j k l _ _
    use (f * j), 1
    constructor
    · exact grid_sides_word _
    constructor
    · rw [← Hc]
      exact PresentedMonoid.sound (Con'Gen.Rel.mul k l)
    rfl

theorem stable_braid_elem {w y : FreeMonoid' ℕ} (h : braid_rels_m_inf w y) :
    ∀ a, stable (of a) w := by
  rcases h
  · exact fun a ↦ stable_close a _ _ dist_succ
  exact fun a ↦ stable_far_apart a _ _ (or_dist_iff.mpr (Or.inl (by assumption)))

theorem stable_braid_elem_symm {w y : FreeMonoid' ℕ} (h : braid_rels_m_inf y w) :
    ∀ a, stable (of a) w := by
  rcases h
  · intro a
    apply stable_close
    rw [Nat.dist_comm]
    exact dist_succ
  exact fun a => stable_far_apart a _ _ (or_dist_iff.mpr (Or.inr (by assumption)))

theorem reg_helper (ih : ∀ (u v a b : FreeMonoid' ℕ), n ≥ u.length + b.length → grid u v a b →
    ∀ (u' v' : FreeMonoid' ℕ), BraidMonoidInf_mk u = BraidMonoidInf_mk u' →
    BraidMonoidInf_mk v = BraidMonoidInf_mk v' → ∃ a' b', grid u' v' a' b' ∧
    BraidMonoidInf_mk a = BraidMonoidInf_mk a' ∧ BraidMonoidInf_mk b = BraidMonoidInf_mk b')
    (br : braid_rels_m_inf f g) (gr : grid e (i * f * j) c d) (len : n + 1 ≥ e.length + d.length) :
    ∃ a' b', grid e (i * g * j) a' b' ∧
    BraidMonoidInf_mk c = BraidMonoidInf_mk a' ∧ BraidMonoidInf_mk d = BraidMonoidInf_mk b' := by
  rcases splittable_vertically_of_grid gr _ _ rfl with ⟨u₁, d₄, d₃, first_grid, grid_right, d_is⟩
  have H_split1 := splittable_vertically_of_grid first_grid _ _ rfl
  rcases H_split1 with ⟨u, d₁, d₂, grid_left, grid_middle, d₄_is⟩
  induction u using FreeMonoid'.inductionOn'
  · use 1, d₁ * g * d₃
    have H := word_side_side _ _ _ grid_middle
    rw [H.1] at grid_right
    rw [H.2] at d₄_is
    have H := word_side_side _ _ _ grid_right
    rw [H.1] at grid_right
    rw [H.1]
    constructor
    · exact grid.horizontal (grid.horizontal grid_left (grid_top_bottom_word g)) grid_right
    constructor
    · rfl
    rw [d_is, d₄_is]
    apply PresentedMonoid.sound
    exact Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl _) (Con'Gen.Rel.of _ _ br))
      (Con'Gen.Rel.refl _)
  rename_i head tail ih_bad
  have H_split := splittable_horizontally_of_grid grid_middle _ _ rfl
  rcases H_split with ⟨mid, a₁, a₂, gr_top_middle, gr_bottom_middle, u₁_is⟩
  have H := stable_braid_elem br head a₁ mid gr_top_middle (of head) g rfl
    (PresentedMonoid.sound (Con'Gen.Rel.of _ _ br))
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
    linarith [len, braid_length_pos br]
  have H_st : BraidMonoidInf_mk (a₁ * a₂) = BraidMonoidInf_mk (a₁' * a₂') :=
    PresentedMonoid.sound <| Con'Gen.Rel.mul (PresentedMonoid.exact top_middle_fact.2.1)
    (PresentedMonoid.exact bottom_middle_fact.2.1)
  rcases ih (a₁ * a₂) j  c d₃ H_len grid_right _ _ H_st rfl with ⟨c', d₃', right_fact⟩
  use c', d₁ * d₂' * d₃'
  constructor
  · exact grid.horizontal (grid.horizontal grid_left
      (grid.vertical top_middle_fact.1 bottom_middle_fact.1)) right_fact.1
  constructor
  · exact right_fact.2.1
  rw [d_is, d₄_is]
  exact PresentedMonoid.sound <| Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl d₁)
    (PresentedMonoid.exact bottom_middle_fact.right.right)) (PresentedMonoid.exact right_fact.2.2)

theorem symm_helper (ih : ∀ (u v a b : FreeMonoid' ℕ), n ≥ u.length + b.length → grid u v a b →
    ∀ (u' v' : FreeMonoid' ℕ), BraidMonoidInf_mk u = BraidMonoidInf_mk u' →
    BraidMonoidInf_mk v = BraidMonoidInf_mk v' → ∃ a' b', grid u' v' a' b' ∧
    BraidMonoidInf_mk a = BraidMonoidInf_mk a' ∧ BraidMonoidInf_mk b = BraidMonoidInf_mk b')
    (br : braid_rels_m_inf f g) (gr : grid e (i * g * j) c d) (len : n + 1 ≥ e.length + d.length) :
    ∃ a' b', grid e (i * f * j) a' b' ∧
    BraidMonoidInf_mk c = BraidMonoidInf_mk a' ∧ BraidMonoidInf_mk d = BraidMonoidInf_mk b' := by
  have H_split := splittable_vertically_of_grid gr _ _ rfl
  rcases H_split with ⟨u₁, d₄, d₃, first_grid, grid_right, d_is⟩
  have H_split1 := splittable_vertically_of_grid first_grid _ _ rfl
  rcases H_split1 with ⟨u, d₁, d₂, grid_left, grid_middle, d₄_is⟩
  induction u using FreeMonoid'.inductionOn'
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
    exact PresentedMonoid.sound <| Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl _)
      (Con'Gen.Rel.symm (Con'Gen.Rel.of _ _ br))) (Con'Gen.Rel.refl _)
  rename_i head tail ih_bad
  have H_split := splittable_horizontally_of_grid grid_middle _ _ rfl
  rcases H_split with ⟨mid, a₁, a₂, gr_top_middle, gr_bottom_middle, u₁_is⟩
  have H := stable_braid_elem_symm br head a₁ mid gr_top_middle (of head) f rfl
    (PresentedMonoid.sound (Con'Gen.Rel.symm (Con'Gen.Rel.of _ _ br)))
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
  have H_st : BraidMonoidInf_mk (a₁ * a₂) = BraidMonoidInf_mk (a₁' * a₂') :=
    PresentedMonoid.sound <| Con'Gen.Rel.mul (PresentedMonoid.exact top_middle_fact.2.1)
    (PresentedMonoid.exact bottom_middle_fact.2.1)
  rcases ih (a₁ * a₂) j  c d₃ H_len grid_right _ _ H_st rfl with ⟨c', d₃', right_fact⟩
  use c', d₁ * d₂' * d₃'
  constructor
  · exact grid.horizontal (grid.horizontal grid_left
      (grid.vertical top_middle_fact.1 bottom_middle_fact.1)) right_fact.1
  constructor
  · exact right_fact.2.1
  rw [d_is, d₄_is]
  apply PresentedMonoid.sound <| Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl d₁)
    (PresentedMonoid.exact bottom_middle_fact.right.right)) (PresentedMonoid.exact right_fact.2.2)

-- a grid is stable when only the second element moves
theorem stable_second (ih : ∀ (u v a b : FreeMonoid' ℕ), n ≥ u.length + b.length → grid u v a b →
    ∀ (u' v' : FreeMonoid' ℕ), BraidMonoidInf_mk u = BraidMonoidInf_mk u' →
    BraidMonoidInf_mk v = BraidMonoidInf_mk v' → ∃ a' b', grid u' v' a' b' ∧
    BraidMonoidInf_mk a = BraidMonoidInf_mk a' ∧ BraidMonoidInf_mk b = BraidMonoidInf_mk b')
    (b_is : BraidMonoidInf_mk f = BraidMonoidInf_mk i) :
    ∀ (d : FreeMonoid' ℕ), n + 1 ≥ a.length + d.length →
    ∀ (c : FreeMonoid' ℕ), grid a f c d → ∃ a' b', grid a i a' b' ∧
    BraidMonoidInf_mk c = BraidMonoidInf_mk a' ∧ BraidMonoidInf_mk d = BraidMonoidInf_mk b' := by
  induction ((PresentedMonoid.mine4_cg _).mpr (PresentedMonoid.exact b_is)) with
  | refl =>
    intro d _ c _
    use c, d
  | reg _ _ br => exact fun _ len _ gr => reg_helper ih br gr len
  | symm _ _ br => exact fun _ len _ gr => symm_helper ih br gr len
  | trans j k l m =>
    intro d len c gr
    specialize l (PresentedMonoid.sound ((PresentedMonoid.mine4_cg braid_rels_m_inf).mp j))
      d len c gr
    rcases l with ⟨c₁, d₁, first_fact⟩
    have len' : n + 1 ≥ a.length + d₁.length := by
      rw [braid_length_eq first_fact.2.2] at len
      exact len
    specialize m (PresentedMonoid.sound ((PresentedMonoid.mine4_cg braid_rels_m_inf).mp k))
      d₁ len' c₁ first_fact.1
    rcases m with ⟨c₂, d₂, second_fact⟩
    use c₂, d₂
    exact ⟨second_fact.1, ⟨first_fact.2.1.trans second_fact.2.1,
      first_fact.2.2.trans second_fact.2.2⟩⟩

theorem stability (u v : FreeMonoid' ℕ) : stable u v := by
  have H1 : ∀ t u v, ∀ a b, t >= u.length + b.length → grid u v a b → ∀ u' v',
      BraidMonoidInf_mk u = BraidMonoidInf_mk u' →
      BraidMonoidInf_mk v = BraidMonoidInf_mk v' → ∃ a' b',
      grid u' v' a' b' ∧ BraidMonoidInf_mk a = BraidMonoidInf_mk a' ∧
      BraidMonoidInf_mk b = BraidMonoidInf_mk b' := by
    intro t
    induction t with
    | zero =>
      intro u _ _ _ length
      have H : u.length = 0 := by linarith [length]
      rw [FreeMonoid'.eq_one_of_length_eq_zero H]
      exact stable_first_one _ _
    | succ n ih =>
      intro a b c d e f a₁ b₁ a_is b_is
      revert c; revert d; revert b
      induction ((PresentedMonoid.mine4_cg _).mpr (PresentedMonoid.exact a_is)) with
      | refl => exact fun b b_is => stable_second ih b_is
      | reg e f br =>
        intro b b_is d len c gr
        rename_i g i
        have easy_len : n + 1 ≥ b.length + c.length := by
          rw [← grid_diag_length_eq gr]
          exact len
        rcases reg_helper ih br (grid_swap gr) easy_len with ⟨a1, b1, swapped_grid, da, cb⟩
        apply grid_swap at swapped_grid
        have easy_len2 : n + 1 ≥ (e * i * f).length + a1.length := by
          simp only [length_mul] at len
          simp only [length_mul]
          rw [← braid_length_eq da]
          have H_ig : i.length = g.length := by
            have H2 := braid_length_eq a_is
            simp only [length_mul, add_left_inj, add_right_inj] at H2
            exact H2.symm
          rw [H_ig]
          assumption
        rcases stable_second ih b_is a1 easy_len2 b1 swapped_grid with ⟨a2, b2, second_fact⟩
        use a2, b2
        exact ⟨second_fact.1, ⟨cb.trans second_fact.2.1, da.trans second_fact.2.2⟩⟩
      | symm g i br =>
        intro b b_is d len c gr
        have easy_len : n + 1 ≥ b.length + c.length := by
          rw [← grid_diag_length_eq gr]
          exact len
        rcases symm_helper ih br (grid_swap gr) easy_len with ⟨a1, b1, swapped_grid, da, cb⟩
        apply grid_swap at swapped_grid
        rename_i x _
        have easy_len2 : n + 1 ≥ (g * x * i).length + a1.length := by
          simp only [length_mul] at len
          simp only [length_mul]
          rw [← braid_length_eq da]
          rename_i x1
          have H_ig : x.length = x1.length := by
            have H2 := braid_length_eq a_is
            simp only [length_mul, add_left_inj, add_right_inj] at H2
            exact H2.symm
          rw [H_ig]
          assumption
        rcases stable_second ih b_is a1 easy_len2 b1 swapped_grid with ⟨a2, b2, second_fact⟩
        use a2, b2
        exact ⟨second_fact.1, ⟨cb.trans second_fact.2.1, da.trans second_fact.2.2⟩⟩
      | trans ha1 hb1 hc1 hd1 =>
        rename_i f g _
        intro b b_is d len c gr
        specialize hc1 (PresentedMonoid.sound ((PresentedMonoid.mine4_cg braid_rels_m_inf).mp ha1))
          b b_is d len c gr
        rcases hc1 with ⟨c₁, d₁, first_fact⟩
        have H_len : n + 1 >= g.length + d₁.length := by
          have H1 : g.length = f.length := braid_length_eq
            (PresentedMonoid.sound ((PresentedMonoid.mine4_cg braid_rels_m_inf).mp ha1)).symm
          have H2 : d₁.length = d.length := braid_length_eq first_fact.2.2.symm
          rw [H1, H2]
          exact len
        specialize hd1 (PresentedMonoid.sound ((PresentedMonoid.mine4_cg braid_rels_m_inf).mp hb1))
          b₁ rfl d₁ H_len c₁ first_fact.1
        rcases hd1 with ⟨c₂, d₂, second_fact⟩
        use c₂, d₂
        exact ⟨second_fact.1, ⟨first_fact.2.1.trans second_fact.2.1,
          first_fact.2.2.trans second_fact.2.2⟩⟩
  exact fun c d => H1 (u.length + d.length) u v c d (Nat.le_refl _)
