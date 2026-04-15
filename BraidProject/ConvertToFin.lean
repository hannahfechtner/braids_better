import BraidProject.BraidMonoidFin
import Mathlib.Data.Fin.Basic
import BraidProject.BraidMonoid
import BraidProject.Additions.Nat


theorem braid_rel_def_is_good {i j n : ℕ} {i_n : i < n + 2} {j_n : j < n + 2} (apart : i + 2 ≤ j) :
    @BraidMonoid.braid_rels_multi n [⟨i, i_n⟩, ⟨j, j_n⟩] [⟨j, j_n⟩, ⟨i, i_n⟩] := by
  have i_is : Fin.mk i i_n = (Fin.mk i (by linarith)).castSucc.castSucc := rfl
  have j_is : Fin.mk j j_n = (Fin.mk (j - 2) (by grind)).succ.succ := by grind
  rw [i_is, j_is]
  exact BraidMonoid.braid_rels_multi.separated _ _ ((congrArg (fun _a => _a)
      (propext Fin.le_iff_val_le_val)).mpr (Nat.le_sub_of_add_le apart))

def FreeMonoid.mapNatToFin (n : ℕ) (a : FreeMonoid ℕ) (bound : ∀ x ∈ a, x<n) : FreeMonoid (Fin n) :=
  (FreeMonoid.pmap Fin.mk a) bound

@[simp]
theorem FreeMonoid.mapNatToFin_empty {n h} : FreeMonoid.mapNatToFin n 1 h = 1 := rfl

theorem FreeMonoid.mapNatToFin_singleton (a : ℕ) (b : FreeMonoid ℕ)
    (bounded_a : ∀ x, x ∈ FreeMonoid.of a → x < n) (bounded_b : ∀ x, x ∈ b → x < n)
    (bounded_ab : ∀ x ∈ FreeMonoid.of a * b, x < n) : FreeMonoid.mapNatToFin n (FreeMonoid.of a * b) bounded_ab =
    FreeMonoid.mapNatToFin n (FreeMonoid.of a) bounded_a * FreeMonoid.mapNatToFin n b bounded_b := by
  rfl

theorem FreeMonoid.mapNatToFin_mul (a b : FreeMonoid ℕ) (bounded_a : ∀ x∈ a, x < n) (bounded_b : ∀ x∈ b, x < n) (bounded_ab : ∀ x∈ a * b, x < n) :
    FreeMonoid.mapNatToFin n (a * b) bounded_ab = FreeMonoid.mapNatToFin n a bounded_a  *  FreeMonoid.mapNatToFin n b bounded_b := by
  induction a using FreeMonoid.inductionOn'
  · grind [one_mul, FreeMonoid.mapNatToFin_empty]
  rename_i ha ta ihta
  have bounded_ha : ∀ x, x ∈ FreeMonoid.of ha → x < n :=
    fun t h => bounded_a t (FreeMonoid.mem_mul.mpr (Or.inl h))
  have bounded_ta : ∀ x, x ∈ ta → x < n :=
    fun t h => bounded_a t (FreeMonoid.mem_mul.mpr (Or.inr h))
  have bounded_tab : ∀ x, x ∈ ta * b → x < n := fun t h => bounded_ab t
      ((congrArg (fun _a => t ∈ _a) (mul_assoc (FreeMonoid.of ha) ta b)).mpr
      ((congrArg id (propext FreeMonoid.mem_mul)).mpr (Or.inr h)))
  rw [FreeMonoid.mapNatToFin_singleton ha ta bounded_ha bounded_ta]
  conv => rhs; rw [mul_assoc]
  rw [← ihta bounded_ta bounded_tab]
  rfl

theorem FreeMonoid.lt_of_mem_map_val {n : ℕ} (u : FreeMonoid (Fin n)) (x : ℕ)
    (h : x ∈ FreeMonoid.map (fun i => ↑i) u) : x < n := by
  rcases FreeMonoid.mem_map.mp h with ⟨a, ha⟩
  rw [← ha.2]
  exact a.isLt

theorem FreeMonoid.mapNatToFin_map_val (u : FreeMonoid (Fin n)) :
    FreeMonoid.mapNatToFin n (FreeMonoid.map (fun i => i.val) u) (FreeMonoid.lt_of_mem_map_val u) = u := by
  induction u using FreeMonoid.inductionOn'
  · simp only [map_one]
    rw [FreeMonoid.mapNatToFin_empty]
  rename_i h t iht
  have : FreeMonoid.map (fun i => i.val) (FreeMonoid.of h * t) = FreeMonoid.of h.val * FreeMonoid.map (fun i => i.val) (t) := rfl
  simp only [this]
  rw [FreeMonoid.mapNatToFin_singleton h _ (by grind [FreeMonoid.mem_of]) (by grind), iht]
  rfl

theorem braid_rel_inf_to_fin_helper (n: ℕ) (a b: FreeMonoid ℕ) (holds_in_inf : braid_monoid_rels_inf a b)
    (bounded_a: ∀ (x : ℕ), x ∈ a → x < n) (bounded_b: ∀ (x : ℕ), x ∈ b → x < n) :
    BraidMonoid.braid_monoid_rels_fin n (FreeMonoid.mapNatToFin n a bounded_a) (FreeMonoid.mapNatToFin n b bounded_b) := by
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
    apply BraidMonoid.braid_rels_multi.adjacent (Fin.castPred ⟨i, by linarith⟩ _)
    grind [Fin.last]
  rename_i i j apart
  have : ∃ k, n = Nat.succ (Nat.succ k) := by
    have := bounded_a j (FreeMonoid.mem_mul.mpr (Or.inr FreeMonoid.mem_of_self))
    use (Nat.pred (Nat.pred n))
    repeat rw [Nat.succ_pred]
    all_goals grind [Nat.pred_zero, Nat.zero_or_one_of_pred_eq_zero]
  rcases this with ⟨k, hk⟩
  subst hk
  exact braid_rel_def_is_good apart

theorem braid_rel_inf_to_fin (n : ℕ) (a b : FreeMonoid ℕ) (bounded_a: ∀ x, x ∈ a → x < n)
    (bounded_b: ∀ x, x ∈ b→ x < n) (h : BraidMonoidInf.mk a = BraidMonoidInf.mk b) :
    BraidMonoid.mk _ (FreeMonoid.mapNatToFin n a bounded_a) = BraidMonoid.mk _ (FreeMonoid.mapNatToFin n b bounded_b) := by
  apply PresentedMonoid.exact at h
  induction h with
  | of x y old =>
    apply BraidMonoid.sound
    apply PresentedMonoid.rels_alone
    apply braid_rel_inf_to_fin_helper n
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
    · exact BraidMonoid.concat_mk ih1 ih2
    any_goals aesop

theorem braid_rel_inf_to_fin' {x y : FreeMonoid (Fin n)}
    (h : BraidMonoidInf.mk ((FreeMonoid.map fun i ↦ ↑i) x) =
    BraidMonoidInf.mk ((FreeMonoid.map fun i ↦ ↑i) y))
    : BraidMonoid.mk _ x = BraidMonoid.mk _ y := by
  rw [← FreeMonoid.mapNatToFin_map_val x, ← FreeMonoid.mapNatToFin_map_val y]
  exact braid_rel_inf_to_fin n _ _ _ _ h

theorem toBraidMonoidInf_helper (n : ℕ) : ∀ (a b : FreeMonoid (Fin n)),
    (BraidMonoid.braid_monoid_rels_fin n) a b →
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
    apply BraidMonoidInf.braid
    unfold Nat.dist
    aesop
  simp only [map_mul]
  apply BraidMonoidInf.comm
  unfold Nat.dist Fin.castSucc Fin.castAdd Fin.castLE Fin.succ
  simp only
  omega

def inclusion {n : ℕ} : (BraidMonoid.BraidMonoidFin n) →* BraidMonoidInf := PresentedMonoid.toMonoid _ (toBraidMonoidInf_helper _)

@[simp]
theorem inclusion_of {n : ℕ} (i : Fin n.pred) :
    inclusion (BraidMonoid.of _ i) = BraidMonoidInf.of i.1 := PresentedMonoid.toMonoid.of _ _

@[simp] theorem inclusion_map_word {n : ℕ} (w : FreeMonoid (Fin n.pred)) :
    inclusion (BraidMonoid.mk _ w) =
    BraidMonoidInf.mk (FreeMonoid.map (fun i => i.1) w) := by
  induction w with
  | one => simp; rfl
  | of x => simp; rfl
  | mul x y _ _ => simp; grind [BraidMonoid.mk]

def inclusion_injective {n : ℕ} : Function.Injective (@inclusion n) := by
  intro x y h
  unfold BraidMonoid.BraidMonoidFin at x y
  induction x with | h x =>
  induction y with | h y =>
  rw [← BraidMonoid.mk, inclusion_map_word, inclusion_map_word] at h
  exact braid_rel_inf_to_fin' h
