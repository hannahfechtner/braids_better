import BraidProject.BraidMonoidInf

open PresentedMonoid

namespace Braid

open FreeMonoid in
inductive braid_rels_multi {n : ℕ} : FreeMonoid (Fin (n + 2)) → FreeMonoid (Fin (n + 2)) → Prop
  | adjacent (i : Fin (n + 1)) :
      braid_rels_multi (of i.castSucc * of i.succ * of i.castSucc)
                       (of i.succ * of i.castSucc * of i.succ)
  | separated (i j : Fin n) (h : i ≤ j) :
      braid_rels_multi (of i.castSucc.castSucc * of j.succ.succ)
                       (of j.succ.succ * of i.castSucc.castSucc)

def braid_monoid_rels_fin : (n : ℕ) → (FreeMonoid (Fin n) → FreeMonoid (Fin n) → Prop)
  | 0     => (λ _ _ => False)
  | 1     => (λ _ _ => False)
  | n + 2 => @braid_rels_multi n

/-- this is the braid monoid with n strands. those strands are numbered 0 to n-1.
the generators are numbered 0 to n-2 -/
def BraidMonoidFin (n : ℕ) := PresentedMonoid (braid_monoid_rels_fin n.pred)

instance (n : ℕ) : Monoid (BraidMonoidFin n) := by unfold BraidMonoidFin; infer_instance

namespace BraidMonoidFin

def rel (n : ℕ):= PresentedMonoid.rel (braid_monoid_rels_fin n)

protected def of (n : ℕ) := PresentedMonoid.of (braid_monoid_rels_fin n)

protected def mk (n : ℕ) := PresentedMonoid.mk (braid_monoid_rels_fin n)

theorem mul_mk {n : ℕ} {a b : FreeMonoid (Fin n)} : BraidMonoidFin.mk n (a * b) =
    BraidMonoidFin.mk n a * BraidMonoidFin.mk n b := rfl

theorem mk_one {n : ℕ} : BraidMonoidFin.mk n 1 = 1 := rfl

instance {n : ℕ} : Monoid (BraidMonoidFin n) := by unfold BraidMonoidFin; infer_instance

theorem sound (h : BraidMonoidFin.rel n a b) : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b :=
  PresentedMonoid.sound h

theorem exact (h : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b ) : BraidMonoidFin.rel n a b :=
  Quotient.exact h

-- theorem refl : BraidMonoidFin.rel n a a := PresentedMonoid.refl
-- theorem reg : ∀ c d, BraidMonoidFin.rel n a b → BraidMonoidFin.rel n (c * a * d) (c * b * d) :=
--   fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left h)
-- theorem symm : ∀ c d, BraidMonoidFin.rel n a b → BraidMonoidFin.rel n (c * b * d) (c * a * d) :=
--   fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left (PresentedMonoid.symm h))
theorem concat : BraidMonoidFin.rel n a b → BraidMonoidFin.rel n c d →
  BraidMonoidFin.rel n (a * c) (b * d) := PresentedMonoid.mul
-- theorem append_left : BraidMonoidFin.rel n c d →
--   BraidMonoidFin.rel n (a * c) (a * d) := PresentedMonoid.append_left
-- theorem append_right : BraidMonoidFin.rel n a b →
--   BraidMonoidFin.rel n (a * c) (b * c) := PresentedMonoid.append_right

-- theorem refl_mk : BraidMonoidFin.mk n a = BraidMonoidFin.mk n a := BraidMonoidFin.sound (refl)
-- theorem reg_mk : ∀ c d, BraidMonoidFin.mk n a = BraidMonoidFin.mk n b → BraidMonoidFin.mk n (c * a * d) =
--     BraidMonoidFin.mk n (c * b * d) :=
--   fun _ _ h => BraidMonoidFin.sound (reg _ _ (PresentedMonoid.exact h))
-- theorem symm_mk : ∀ c d, BraidMonoidFin.mk n a = BraidMonoidFin.mk n b → BraidMonoidFin.mk n (c * b * d) =
--     BraidMonoidFin.mk n (c * a * d) :=
--   fun _ _ h => BraidMonoidFin.sound (reg _ _ (PresentedMonoid.exact h.symm))
theorem concat_mk : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b →
    BraidMonoidFin.mk n c = BraidMonoidFin.mk n d →
    BraidMonoidFin.mk n (a * c) = BraidMonoidFin.mk n (b * d) :=
  fun h1 h2 => BraidMonoidFin.sound (concat (BraidMonoidFin.exact h1) (BraidMonoidFin.exact h2))
-- theorem append_left_mk : BraidMonoidFin.mk n c = BraidMonoidFin.mk n d →
--     BraidMonoidFin.mk n (a * c) = BraidMonoidFin.mk n (a * d) :=
--   fun h => BraidMonoidFin.sound (append_left (BraidMonoidFin.exact h))
-- theorem append_right_mk : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b →
--     BraidMonoidFin.mk n (a * c) = BraidMonoidFin.mk n (b * c) :=
--   fun h => BraidMonoidFin.sound (append_right (BraidMonoidFin.exact h))

-- theorem comm {j k : Fin n} (h1 : n >= 3) (h : j - k >= (⟨2, h1⟩ : Fin n)) :
--     BraidMonoidFin.mk n (FreeMonoid.of j * FreeMonoid.of k) = BraidMonoidFin.mk n (FreeMonoid.of k * FreeMonoid.of j) := by
--   apply PresentedMonoid.sound
--   -- rcases or_dist_iff.mp h
--   -- · apply PresentedMonoid.rel_alone
--   --   apply braid_rels_m_inf.separated
--   --   assumption
--   apply PresentedMonoid.symm_alone
--   have hjk : j<=k := by sorry
--   have H := braid_rels_multi.separated j k hjk
--   have H3 : ∃ (l : ℕ), n = l.succ.succ := by sorry
--   unfold braid_monoid_rels_fin
--   rcases H3 with ⟨l, hl⟩
--   sorry

-- theorem comm_rel {j k : Fin n} (h1 : n≥ 3) (h : j - k >= ⟨2, h1⟩) :
--     BraidMonoidFin.rel n (FreeMonoid.of j * FreeMonoid.of k) (FreeMonoid.of k * FreeMonoid.of j) := by sorry
  -- rcases or_dist_iff.mp h
  -- · apply PresentedMonoid.rel_alone
  --   apply braid_rels_m_inf.separated
  --   assumption
  -- apply PresentedMonoid.symm_alone
  -- apply braid_rels_m_inf.separated
  -- assumption

-- theorem braid {j k : ℕ} (h : j.dist k = 1) :
--     BraidMonoidFin.mk n (of j * of k * of j) = BraidMonoidFin.mk n (of k * of j * of k) := by
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
--     BraidMonoidFin.rel n (of j * of k * of j) (of k * of j * of k) := by
--   rcases or_dist_iff_eq.mp h
--   · apply PresentedMonoid.rel_alone
--     rename_i k_is
--     rw [← k_is]
--     exact braid_rels_m_inf.adjacent _
--   apply PresentedMonoid.symm_alone
--   rename_i j_is
--   rw [← j_is]
--   exact braid_rels_m_inf.adjacent _

open Braid
theorem toBraidGroup_helper (n : ℕ) : ∀ (a b : FreeMonoid (Fin (n.pred))),
    (Braid.braid_monoid_rels_fin (n.pred)) a b → ((FreeMonoid.lift fun a => σₙ a) a : BraidGroupFin n)=
    (FreeMonoid.lift fun a => σₙ a) b := by
  repeat
    rcases n
    · exact fun _ _ h => h.elim
    rename_i n
  intro a b h
  rcases h
  · rename_i j
    simp only [map_mul, Nat.pred_succ]
    apply BraidGroupFin.braid
    unfold Nat.dist
    aesop
  simp only [map_mul, Nat.pred_succ]
  apply BraidGroupFin.comm
  unfold Nat.dist Fin.castSucc Fin.castAdd Fin.castLE Fin.succ
  simp only
  omega

def toBraidGroup {n : ℕ} : (BraidMonoidFin n) →* (BraidGroupFin n) := PresentedMonoid.toMonoid _ (toBraidGroup_helper _)

end BraidMonoidFin
