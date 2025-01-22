import BraidProject.BraidMonoid

open PresentedMonoid

namespace BraidMonoid -- end this

def rel (n : ℕ):= PresentedMonoid.rel (braid_rels_m n)

protected def mk (n : ℕ) := PresentedMonoid.mk (braid_rels_m n)

theorem mul_mk {n : ℕ} {a b : FreeMonoid' (Fin n)} : BraidMonoid.mk n (a * b) =
    BraidMonoid.mk n a * BraidMonoid.mk n b :=
  rfl

theorem mk_one {n : ℕ} : BraidMonoid.mk n 1 = 1 := rfl

instance {n : ℕ} : Monoid (BraidMonoid n) := by unfold BraidMonoid; infer_instance

theorem sound : BraidMonoid.rel n a b → BraidMonoid.mk n a = BraidMonoid.mk n b :=
  PresentedMonoid.sound

theorem exact : BraidMonoid.mk n a = BraidMonoid.mk n b → BraidMonoid.rel n a b := by
  sorry

theorem refl : BraidMonoid.rel n a a := PresentedMonoid.refl
theorem reg : ∀ c d, BraidMonoid.rel n a b → BraidMonoid.rel n (c * a * d) (c * b * d) :=
  fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left h)
theorem symm : ∀ c d, BraidMonoid.rel n a b → BraidMonoid.rel n (c * b * d) (c * a * d) :=
  fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left (PresentedMonoid.swap h))
theorem concat : BraidMonoid.rel n a b → BraidMonoid.rel n c d →
  BraidMonoid.rel n (a * c) (b * d) := PresentedMonoid.mul
theorem append_left : BraidMonoid.rel n c d →
  BraidMonoid.rel n (a * c) (a * d) := PresentedMonoid.append_left
theorem append_right : BraidMonoid.rel n a b →
  BraidMonoid.rel n (a * c) (b * c) := PresentedMonoid.append_right

theorem refl_mk : BraidMonoid.mk n a = BraidMonoid.mk n a := BraidMonoid.sound (refl)
theorem reg_mk : ∀ c d, BraidMonoid.mk n a = BraidMonoid.mk n b → BraidMonoid.mk n (c * a * d) =
    BraidMonoid.mk n (c * b * d) :=
  fun _ _ h => BraidMonoid.sound (reg _ _ (PresentedMonoid.exact h))
theorem symm_mk : ∀ c d, BraidMonoid.mk n a = BraidMonoid.mk n b → BraidMonoid.mk n (c * b * d) =
    BraidMonoid.mk n (c * a * d) :=
  fun _ _ h => BraidMonoid.sound (reg _ _ (PresentedMonoid.exact h.symm))
theorem concat_mk : BraidMonoid.mk n a = BraidMonoid.mk n b →
    BraidMonoid.mk n c = BraidMonoid.mk n d →
    BraidMonoid.mk n (a * c) = BraidMonoid.mk n (b * d) :=
  fun h1 h2 => BraidMonoid.sound (concat (BraidMonoid.exact h1) (BraidMonoid.exact h2))
theorem append_left_mk : BraidMonoid.mk n c = BraidMonoid.mk n d →
    BraidMonoid.mk n (a * c) = BraidMonoid.mk n (a * d) :=
  fun h => BraidMonoid.sound (append_left (BraidMonoid.exact h))
theorem append_right_mk : BraidMonoid.mk n a = BraidMonoid.mk n b →
    BraidMonoid.mk n (a * c) = BraidMonoid.mk n (b * c) :=
  fun h => BraidMonoid.sound (append_right (BraidMonoid.exact h))

theorem comm {j k : Fin n} (h1 : n >= 3) (h : j - k >= (⟨2, h1⟩ : Fin n)) :
    BraidMonoid.mk n (FreeMonoid'.of j * FreeMonoid'.of k) = BraidMonoid.mk n (FreeMonoid'.of k * FreeMonoid'.of j) := by
  apply PresentedMonoid.sound
  -- rcases or_dist_iff.mp h
  -- · apply PresentedMonoid.rel_alone
  --   apply braid_rels_m_inf.separated
  --   assumption
  apply PresentedMonoid.symm_alone
  have hjk : j<=k := by sorry
  have H := braid_rels_multi.separated j k hjk
  have H3 : ∃ (l : ℕ), n = l.succ.succ := by sorry
  unfold braid_rels_m
  rcases H3 with ⟨l, hl⟩
  sorry

theorem comm_rel {j k : Fin n} (h1 : n≥ 3) (h : j - k >= ⟨2, h1⟩) :
    BraidMonoid.rel n (FreeMonoid'.of j * FreeMonoid'.of k) (FreeMonoid'.of k * FreeMonoid'.of j) := by sorry
  -- rcases or_dist_iff.mp h
  -- · apply PresentedMonoid.rel_alone
  --   apply braid_rels_m_inf.separated
  --   assumption
  -- apply PresentedMonoid.symm_alone
  -- apply braid_rels_m_inf.separated
  -- assumption

-- theorem braid {j k : ℕ} (h : j.dist k = 1) :
--     BraidMonoid.mk n (of j * of k * of j) = BraidMonoid.mk n (of k * of j * of k) := by
--   apply PresentedMonoid.sound
--   rcases or_dist_iff_eq.mp h
--   · apply PresentedMonoid.rel_alone
--     rename_i k_is
--     rw [← k_is]
--     exact braid_rels_m_inf.adjacent _
--   apply PresentedMonoid.symm_alone
--   rename_i j_is
--   rw [← j_is]
--   exact braid_rels_m_inf.adjacent _

-- theorem braid_rel {j k : ℕ} (h : j.dist k = 1) :
--     BraidMonoid.rel n (of j * of k * of j) (of k * of j * of k) := by
--   rcases or_dist_iff_eq.mp h
--   · apply PresentedMonoid.rel_alone
--     rename_i k_is
--     rw [← k_is]
--     exact braid_rels_m_inf.adjacent _
--   apply PresentedMonoid.symm_alone
--   rename_i j_is
--   rw [← j_is]
--   exact braid_rels_m_inf.adjacent _
