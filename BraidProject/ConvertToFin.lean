import BraidProject.BraidMonoidFin
import Mathlib.Data.Fin.Basic
import BraidProject.BraidMonoidInf
import BraidProject.Additions.Nat

open Braid

theorem braid_rels_multi_of_separated {i j n : ℕ} {i_n : i < n + 2} {j_n : j < n + 2} (apart : i + 2 ≤ j) :
    @braid_rels_multi n [⟨i, i_n⟩, ⟨j, j_n⟩] [⟨j, j_n⟩, ⟨i, i_n⟩] := by
  have i_is : Fin.mk i i_n = (Fin.mk i (by linarith)).castSucc.castSucc := rfl
  have j_is : Fin.mk j j_n = (Fin.mk (j - 2) (by grind)).succ.succ := by grind
  rw [i_is, j_is]
  exact braid_rels_multi.separated _ _ ((congrArg (fun _a => _a)
      (propext Fin.le_iff_val_le_val)).mpr (Nat.le_sub_of_add_le apart))

theorem braid_monoid_rels_fin_of_inf (n: ℕ) (a b: FreeMonoid ℕ) (holds_in_inf : braid_monoid_rels_inf a b)
    (bounded_a: ∀ (x : ℕ), x ∈ a → x < n) (bounded_b: ∀ (x : ℕ), x ∈ b → x < n) :
    braid_monoid_rels_fin n (FreeMonoid.mapNatToFin n a bounded_a) (FreeMonoid.mapNatToFin n b bounded_b) := by
  induction holds_in_inf
  · rename_i i
    have : ∃ k, n = Nat.succ (Nat.succ k) := by  -- because it's bigger than n+1
      have : i+1 < n :=
        bounded_b (i + 1) (FreeMonoid.mem_mul.mpr (Or.inr FreeMonoid.mem_of_self))
      use (Nat.pred (Nat.pred n))
      grind [Nat.pred_eq_sub_one, Nat.succ_eq_add_one]
    rcases this with ⟨k, hk⟩
    subst hk
    have : i + 1 < k + 2 :=
      bounded_a (i + 1) (FreeMonoid.mem_mul.mpr (Or.inl (FreeMonoid.mem_mul.mpr
        (Or.inr (FreeMonoid.mem_of.mpr (Eq.refl (i + 1)))))))
    apply braid_rels_multi.adjacent (Fin.castPred ⟨i, by linarith⟩ _)
    grind [Fin.last]
  rename_i i j apart
  have : ∃ k, n = Nat.succ (Nat.succ k) := by
    have := bounded_a j (FreeMonoid.mem_mul.mpr (Or.inr FreeMonoid.mem_of_self))
    use (Nat.pred (Nat.pred n))
    repeat rw [Nat.succ_pred]
    all_goals grind [Nat.pred_zero, Nat.zero_or_one_of_pred_eq_zero]
  rcases this with ⟨k, hk⟩
  subst hk
  exact braid_rels_multi_of_separated apart

theorem BraidMonoidFin.eq_of_BraidMonoidInf_eq (n : ℕ) (a b : FreeMonoid ℕ) (bounded_a: ∀ x, x ∈ a → x < n)
    (bounded_b: ∀ x, x ∈ b→ x < n) (h : BraidMonoidInf.mk a = BraidMonoidInf.mk b) :
    BraidMonoidFin.mk _ (FreeMonoid.mapNatToFin n a bounded_a) = BraidMonoidFin.mk _ (FreeMonoid.mapNatToFin n b bounded_b) := by
  apply PresentedMonoid.exact at h
  induction h with
  | of x y old =>
    apply BraidMonoidFin.sound
    apply PresentedMonoid.rels_alone
    apply braid_monoid_rels_fin_of_inf n
    cases old with
    | adjacent i => exact braid_monoid_rels_inf.adjacent i
    | separated i j hij => exact braid_monoid_rels_inf.separated i j hij
  | refl x => rfl
  | symm _ ih => exact (ih bounded_b bounded_a).symm
  | trans _ _ ih1 ih2 =>
    specialize ih1 bounded_a
    rename_i a b c ab _
    have bounded_d : ∀ x, x ∈ b → x < n := by
      intro x hb
      apply bounded_a x
      apply FreeMonoid.mem_symbols.mp
      have : a.symbols = b.symbols :=
          congrArg BraidMonoidInf.generators (BraidMonoidInf.sound ab)
      rw [this]
      exact FreeMonoid.mem_symbols.mpr hb
    exact (ih1 bounded_d).trans (ih2 bounded_d bounded_b)
  | mul _ _ ih1 ih2 =>
    specialize ih1 (by aesop) (by aesop)
    specialize ih2 (by aesop) (by aesop)
    rw [FreeMonoid.mapNatToFin_mul, FreeMonoid.mapNatToFin_mul]
    · exact BraidMonoidFin.concat_mk ih1 ih2
    any_goals aesop

theorem BraidMonoidFin.eq_of_BraidMonoidInf_eq' {x y : FreeMonoid (Fin n)}
    (h : BraidMonoidInf.mk ((FreeMonoid.map fun i ↦ ↑i) x) =
    BraidMonoidInf.mk ((FreeMonoid.map fun i ↦ ↑i) y))
    : BraidMonoidFin.mk _ x = BraidMonoidFin.mk _ y := by
  rw [← FreeMonoid.mapNatToFin_map_val x, ← FreeMonoid.mapNatToFin_map_val y]
  exact BraidMonoidFin.eq_of_BraidMonoidInf_eq n _ _ _ _ h

theorem BraidMonoidFin.toBraidMonoidInf_helper (n : ℕ) : ∀ (a b : FreeMonoid (Fin n)),
    braid_monoid_rels_fin n a b →
    (FreeMonoid.lift fun a => BraidMonoidInf.of a.1) a =
    (FreeMonoid.lift fun a => BraidMonoidInf.of a.1) b := by
  repeat
    rcases n
    · exact fun _ _ h => h.elim
    rename_i n
  intro a b h
  rcases h
  · rename_i j
    simp only [map_mul]
    apply BraidMonoidInf.braid_mk
    unfold Nat.dist
    aesop
  simp only [map_mul]
  apply BraidMonoidInf.comm_mk
  unfold Nat.dist Fin.castSucc Fin.castAdd Fin.castLE Fin.succ
  simp only
  omega

def BraidMonoidFin.toBraidMonoidInf {n : ℕ} : (BraidMonoidFin n) →* BraidMonoidInf :=
  PresentedMonoid.toMonoid _ (BraidMonoidFin.toBraidMonoidInf_helper _)

@[simp]
theorem BraidMonoidFin.toBraidMonoidInf_of {n : ℕ} (i : Fin n.pred) :
    BraidMonoidFin.toBraidMonoidInf (BraidMonoidFin.of _ i) = BraidMonoidInf.of i.1 := PresentedMonoid.toMonoid.of _ _

@[simp] theorem BraidMonoidFin.toBraidMonoidInf_map_word {n : ℕ} (w : FreeMonoid (Fin n.pred)) :
    BraidMonoidFin.toBraidMonoidInf (BraidMonoidFin.mk _ w) =
    BraidMonoidInf.mk (FreeMonoid.map (fun i => i.1) w) := by
  induction w with
  | one => simp; rfl
  | of x => simp; rfl
  | mul x y _ _ => simp; grind [BraidMonoidFin.mk]

def BraidMonoidFin.toBraidMonoidInf_injective {n : ℕ} : Function.Injective (@BraidMonoidFin.toBraidMonoidInf n) := by
  intro x y h
  unfold BraidMonoidFin at x y
  induction x with | h x =>
  induction y with | h y =>
  rw [← BraidMonoidFin.mk, BraidMonoidFin.toBraidMonoidInf_map_word, BraidMonoidFin.toBraidMonoidInf_map_word] at h
  exact BraidMonoidFin.eq_of_BraidMonoidInf_eq' h

theorem braid_monoid_rels_inf_of_fin {x y : FreeMonoid (Fin n)} (br : braid_monoid_rels_fin n x y) :
    braid_monoid_rels_inf ((FreeMonoid.map fun i ↦ ↑i) x) ((FreeMonoid.map fun i ↦ ↑i) y) := by
  cases n with
  | zero => exact br.elim
  | succ n =>
    cases n with
    | zero => exact br.elim
    | succ n =>
      rcases br with h1 | h2
      · exact braid_monoid_rels_inf.adjacent ↑h1
      rename_i j j_is
      refine braid_monoid_rels_inf.separated (↑h2) (j + 1 + 1) <| Nat.add_le_add_right j_is 2

theorem BraidMonoidInf.eq_of_BraidMonoidFin_eq (n : ℕ) (a b : FreeMonoid (Fin n))
    (h : BraidMonoidFin.mk _ a = BraidMonoidFin.mk _ b) :
    BraidMonoidInf.mk (FreeMonoid.map (λ i : Fin n => i.val) a) =
    BraidMonoidInf.mk (FreeMonoid.map (λ i : Fin n => i.val) b) := by
  induction (BraidMonoidFin.exact h) with
  | of x y br =>
    exact BraidMonoidInf.sound <| PresentedMonoid.rels_alone (braid_monoid_rels_inf_of_fin br)
  | refl x => rfl
  | symm _ ih =>
    exact (ih h.symm).symm
  | trans xy yz ih1 ih2 =>
    exact (ih1 (BraidMonoidFin.sound xy)).trans (ih2 (BraidMonoidFin.sound yz))
  | mul wx yz ih1 ih2 =>
    rw [map_mul, map_mul, map_mul]
    exact BraidMonoidInf.concat_mk (ih1 (BraidMonoidFin.sound wx)) (ih2 (BraidMonoidFin.sound yz))
