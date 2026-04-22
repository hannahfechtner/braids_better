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

def braid_monoid_rels_fin : (n : ℕ) → (FreeMonoid (Fin n.pred) → FreeMonoid (Fin n.pred) → Prop)
  | 0     => (λ _ _ => False)
  | 1     => (λ _ _ => False)
  | 2     => (λ _ _ => False)
  | n + 3 => @braid_rels_multi n

/-- this is the braid monoid with n strands. those strands are numbered 0 to n-1.
the generators are numbered 0 to n-2 -/
def BraidMonoidFin (n : ℕ) := PresentedMonoid (braid_monoid_rels_fin n)

instance (n : ℕ) : Monoid (BraidMonoidFin n) := by unfold BraidMonoidFin; infer_instance

namespace BraidMonoidFin

def rel (n : ℕ):= PresentedMonoid.rel (braid_monoid_rels_fin n)

protected def of (n : ℕ) := PresentedMonoid.of (braid_monoid_rels_fin n)

protected def mk (n : ℕ) : FreeMonoid (Fin n.pred) →ₙ* BraidMonoidFin n := PresentedMonoid.mk (braid_monoid_rels_fin n)

theorem mul_mk {n : ℕ} {a b : FreeMonoid (Fin n.pred)} : BraidMonoidFin.mk n (a * b) =
    BraidMonoidFin.mk n a * BraidMonoidFin.mk n b := rfl

theorem mk_one {n : ℕ} : BraidMonoidFin.mk n 1 = 1 := rfl

instance {n : ℕ} : Monoid (BraidMonoidFin n) := by unfold BraidMonoidFin; infer_instance

theorem sound (h : BraidMonoidFin.rel n a b) : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b :=
  PresentedMonoid.sound h

theorem exact (h : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b ) : BraidMonoidFin.rel n a b :=
  Quotient.exact h

@[induction_eliminator]
theorem inductionOn {n : ℕ} {P : BraidMonoidFin n → Prop} (h : ∀ a, P (BraidMonoidFin.mk n a)) (b):
  P b := Quot.ind h b


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

open FreeMonoid in
theorem braid_monoid_rels_fin_rec
    {P : ∀ {n : ℕ}, FreeMonoid (Fin n.pred) → FreeMonoid (Fin n.pred) → Prop}
    {n : ℕ} {a b : FreeMonoid (Fin n.pred)}
    (h : braid_monoid_rels_fin n a b)
    (adj : ∀ {k : ℕ} (i : Fin (k + 1)), P (n := k + 3)
          (of i.castSucc * of i.succ * of i.castSucc)
          (of i.succ * of i.castSucc * of i.succ))
    (sep : ∀ {k : ℕ} (i j : Fin k) (hij : i ≤ j), P (n := k + 3)
          (of i.castSucc.castSucc * of j.succ.succ)
          (of j.succ.succ * of i.castSucc.castSucc)) :
    P a b := by
  cases n with
  | zero => cases h
  | succ n => cases n with
    | zero =>  cases h
    | succ n => cases n with
      | zero => cases h
      | succ k =>
          simp only [braid_monoid_rels_fin] at h
          cases h with
          | adjacent i => apply adj
          | separated i j h => apply sep; assumption

private theorem reverse_eq_of_rels {n : ℕ} (a b : FreeMonoid (Fin n.pred)) (h : braid_monoid_rels_fin n a b) :
    mk (braid_monoid_rels_fin n) a.reverse = mk (braid_monoid_rels_fin n) b.reverse := by
  apply braid_monoid_rels_fin_rec h
  · exact fun id_eq ↦ sound (rels_alone (braid_rels_multi.adjacent id_eq))
  exact fun i j hij ↦ Eq.symm (sound (rels_alone (braid_rels_multi.separated i j hij)))


def reverse_braid : BraidMonoidFin n → BraidMonoidFin n :=
  PresentedMonoid.lift_of_mul (fun x => mk (braid_monoid_rels_fin n) <| FreeMonoid.reverse x)
  (fun h1 h2 => by simp [FreeMonoid.reverse_mul, h1, h2]) reverse_eq_of_rels

@[simp]
theorem reverse_braid_one {n : ℕ} : reverse_braid (1 : BraidMonoidFin n) = 1 := rfl

@[simp]
theorem reverse_braid_mk : reverse_braid (BraidMonoidFin.mk n a) =
  BraidMonoidFin.mk n (FreeMonoid.reverse a) := rfl

@[simp]
theorem reverse_braid_mul {a b : BraidMonoidFin n} : reverse_braid (a * b) =
    reverse_braid b * reverse_braid a := by
  induction a with | h a1 =>
  induction b with | h b1 =>
  rw [← BraidMonoidFin.mul_mk]
  grind [reverse_braid_mk, FreeMonoid.reverse_mul]

@[simp]
theorem reverse_reverse : reverse_braid (reverse_braid a) = a := by
  induction a
  rw [reverse_braid_mk, reverse_braid_mk, FreeMonoid.reverse_reverse]

theorem rel_reverse_reverse_iff : PresentedMonoid.rel (braid_monoid_rels_fin n) a1.reverse b1.reverse ↔
  PresentedMonoid.rel (braid_monoid_rels_fin n) a1 b1 := by
  have : ∀ a1 b1, PresentedMonoid.rel (braid_monoid_rels_fin n) a1 b1 →
      PresentedMonoid.rel (braid_monoid_rels_fin n) a1.reverse b1.reverse := by
    intro a1 b1 h
    induction h with
    | of _ _ h =>
      apply braid_monoid_rels_fin_rec h
      · exact fun {k} i ↦ rels_alone (braid_rels_multi.adjacent i)
      exact fun {k} i j hij ↦ symm_alone (braid_rels_multi.separated i j hij)
    | refl _ => exact PresentedMonoid.refl
    | symm _ h => exact ConGen.Rel.symm h
    | trans _ _ h1 h2 => exact h1.trans h2
    | mul _ _ h1 h2 =>
      rw [FreeMonoid.reverse_mul, FreeMonoid.reverse_mul]
      exact PresentedMonoid.mul h2 h1
  grind [FreeMonoid.reverse_reverse]

theorem reverse_eq_reverse_iff : a = b ↔ reverse_braid a = reverse_braid b := by
  constructor
  · intro h
    rw [h]
  intro h
  induction a ; induction b
  simp only [reverse_braid_mk] at h
  exact PresentedMonoid.sound (rel_reverse_reverse_iff.mp (PresentedMonoid.exact h))

open Braid
theorem toBraidGroup_helper (n : ℕ) : ∀ (a b : FreeMonoid (Fin n.pred)),
    (Braid.braid_monoid_rels_fin n) a b → ((FreeMonoid.lift fun a => σₙ a) a : BraidGroupFin n)=
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
