import BraidProject.PresentedMonoid_mine
import Mathlib.Data.Nat.Dist
import BraidProject.Additions.NatDist
import BraidProject.Additions.FreeMonoid
import Mathlib.Algebra.FreeMonoid.Symbols

open FreeMonoid

inductive braid_rels_multi {n : ℕ} : FreeMonoid (Fin (n + 2)) → FreeMonoid (Fin (n + 2)) → Prop
  | adjacent (i : Fin (n + 1)) : braid_rels_multi (of i.castSucc * of i.succ * of i.castSucc)
                                                 (of i.succ * of i.castSucc * of i.succ)
  | separated (i j : Fin n) (h : i ≤ j) : braid_rels_multi (of i.castSucc.castSucc * of j.succ.succ)
                                                          (of j.succ.succ * of i.castSucc.castSucc)

def braid_rels_m : (n : ℕ) → (FreeMonoid (Fin n) → FreeMonoid (Fin n) → Prop)
  | 0     => (λ _ _ => False)
  | 1     => (λ _ _ => False)
  | n + 2 => @braid_rels_multi n

def BraidMonoid (n : ℕ) := PresentedMonoid (braid_rels_m n.pred)

instance (n : ℕ) : Monoid (BraidMonoid n) := by unfold BraidMonoid; infer_instance


-- for the braid with infinitely many strands
inductive braid_rels_m_inf : FreeMonoid ℕ → FreeMonoid ℕ → Prop
  | adjacent (i : ℕ): braid_rels_m_inf (of i * of (i+1) * of i) (of (i+1) * of i * of (i+1))
  | separated (i j : ℕ) (h : i +2 ≤ j) : braid_rels_m_inf (of i * of j) (of j * of i)

theorem length_pos {f g : FreeMonoid ℕ} (h : braid_rels_m_inf f g) : f.length > 0 ∧ g.length > 0 := by
  rcases h
  all_goals grind [length_mul, length_of]

open PresentedMonoid

def BraidMonoidInf := PresentedMonoid braid_rels_m_inf

namespace BraidMonoidInf

def rel := PresentedMonoid.rel braid_rels_m_inf

protected def mk : FreeMonoid ℕ → BraidMonoidInf := PresentedMonoid.mk (braid_rels_m_inf)

instance : Monoid BraidMonoidInf := by unfold BraidMonoidInf; infer_instance

theorem mk_mul : BraidMonoidInf.mk (a * b) = BraidMonoidInf.mk a * BraidMonoidInf.mk b :=
  rfl

theorem mk_one : BraidMonoidInf.mk 1 = 1 := rfl

@[induction_eliminator]
protected theorem inductionOn {δ : BraidMonoidInf → Prop} (q : BraidMonoidInf)
    (h : ∀ a, δ (BraidMonoidInf.mk a)) : δ q :=
  Quotient.ind h q

-- define the length of elements of the braid monoid
def length : BraidMonoidInf → ℕ :=
  PresentedMonoid.lift_of_mul (FreeMonoid.length)
  (fun h1 h2 => by rw [length_mul, length_mul, h1, h2]) (fun _ _ h => by
  induction h with
  | adjacent i => simp only [length_mul, length_of, Nat.reduceAdd]
  | separated i j _ => simp only [length_mul, length_of, Nat.reduceAdd])

@[simp]
theorem length_one : length 1 = 0 := rfl

@[simp]
theorem length_mk : length (BraidMonoidInf.mk a) = a.length := rfl

@[simp]
theorem length_mul {a b : BraidMonoidInf} : length (a * b) = length a + length b := by
  induction a; induction b
  rw [← mk_mul, length_mk, length_mk, length_mk, FreeMonoid.length_mul]

theorem length_eq (h : BraidMonoidInf.mk a = BraidMonoidInf.mk b) : a.length = b.length :=
  congr_arg length h

theorem one_of_eq_mk_one {a : FreeMonoid ℕ}
    (h : BraidMonoidInf.mk a = BraidMonoidInf.mk (1 : FreeMonoid ℕ)) :
    a = (1 : FreeMonoid ℕ) := FreeMonoid.length_eq_zero.mp (congrArg length h)

/-- the set of generators appearing in a braid word -/
def generators : BraidMonoidInf → Finset ℕ :=
  PresentedMonoid.lift_of_mul (FreeMonoid.symbols)
  (fun ih1 ih2 => by rw [symbols_mul, symbols_mul, ih1, ih2])
  (fun a b h => by induction h with
  | adjacent i =>
    ext x
    simp only [symbols_mul, symbols_of, Finset.union_assoc, Finset.mem_union, Finset.mem_singleton]
    tauto
  | separated i j h =>
    simp only [symbols_mul, symbols_of]
    exact Finset.union_comm _ _)

@[simp]
theorem generators_one : generators 1 = ∅ := rfl

@[simp]
theorem generators_mk : generators (BraidMonoidInf.mk a) = FreeMonoid.symbols a :=
  rfl

@[simp]
theorem generators_mul : generators (a * b) =
    generators a ∪ generators b := by
  induction a
  induction b
  rw [← mk_mul, generators_mk, generators_mk, generators_mk,
    symbols_mul]

private theorem reverse_eq_of_rels (a b : FreeMonoid ℕ) (h : braid_rels_m_inf a b) :
    mk braid_rels_m_inf a.reverse = mk braid_rels_m_inf b.reverse := by
  induction h with
  | adjacent i =>
    simp only [reverse_mul, reverse_of]
    exact PresentedMonoid.sound (PresentedMonoid.rels_alone (braid_rels_m_inf.adjacent i))
  | separated i j h =>
    simp only [reverse_mul, reverse_of]
    exact PresentedMonoid.sound (PresentedMonoid.symm_alone (braid_rels_m_inf.separated _ _ h))

def reverse_braid : BraidMonoidInf → BraidMonoidInf :=
  PresentedMonoid.lift_of_mul (fun x => mk braid_rels_m_inf <| FreeMonoid.reverse x)
  (fun h1 h2 => by simp [reverse_mul, h1, h2]) reverse_eq_of_rels

@[simp]
theorem reverse_braid_one : reverse_braid 1 = 1 := rfl

@[simp]
theorem reverse_braid_mk : reverse_braid (BraidMonoidInf.mk a) =
  BraidMonoidInf.mk (FreeMonoid.reverse a) := rfl

@[simp]
theorem reverse_braid_mul : reverse_braid (a * b) = reverse_braid b * reverse_braid a := by
  induction a with
  | h a1 =>
  induction b with
  | h b1 =>
  rw [← mk_mul]
  repeat rw [reverse_braid_mk]
  rw [← mk_mul]
  exact congr_arg _ reverse_mul

@[simp]
theorem length_reverse_eq_length : length (reverse_braid a) = length a := by
  induction a with
  | h a1 =>
  simp only [reverse_braid_mk, length_mk, length_reverse]

theorem exact : mk braid_rels_m_inf a = mk braid_rels_m_inf b →
    PresentedMonoid.rel braid_rels_m_inf a b := Quotient.exact

@[simp]
theorem reverse_reverse : reverse_braid (reverse_braid a) = a := by
  induction a
  rw [reverse_braid_mk, reverse_braid_mk, FreeMonoid.reverse_reverse]

theorem rel_reverse_reverse_iff : PresentedMonoid.rel braid_rels_m_inf a1.reverse b1.reverse ↔
  PresentedMonoid.rel braid_rels_m_inf a1 b1 := by
  have H : ∀ a1 b1, PresentedMonoid.rel braid_rels_m_inf a1 b1 →
      PresentedMonoid.rel braid_rels_m_inf a1.reverse b1.reverse := by
    intro a1 b1 h
    induction h with
    | of _ _ h =>
      exact braid_rels_m_inf.rec (fun _ => PresentedMonoid.rels_alone (braid_rels_m_inf.adjacent _))
        (fun i j h => PresentedMonoid.symm_alone (braid_rels_m_inf.separated i j h)) h
    | refl _ => exact PresentedMonoid.refl
    | symm _ h => exact ConGen.Rel.symm h
    | trans _ _ h1 h2 => exact h1.trans h2
    | mul _ _ h1 h2 =>
      rw [reverse_mul, reverse_mul]
      exact PresentedMonoid.mul h2 h1
  constructor
  · grind [FreeMonoid.reverse_reverse]
  exact H _ _

theorem reverse_eq_reverse_iff : a = b ↔ reverse_braid a = reverse_braid b := by
  constructor
  · intro h
    rw [h]
  intro h
  induction a ; induction b
  simp only [reverse_braid_mk] at h
  apply PresentedMonoid.sound
  exact rel_reverse_reverse_iff.mp (PresentedMonoid.exact h)

theorem singleton_eq (h : BraidMonoidInf.mk (of i) = BraidMonoidInf.mk a) : a = of i := by
  have h1 := congrArg generators h
  apply congrArg length at h
  rw [length_mk, length_mk, length_of] at h
  rw [generators_mk, symbols_of] at h1
  rcases length_eq_one.mp h.symm with ⟨b, rfl⟩
  rw [generators_mk, symbols_of, Finset.singleton_inj] at h1
  rw [h1]

theorem pair_eq {j k : ℕ} (h : BraidMonoidInf.mk (of j * of k) = BraidMonoidInf.mk v') :
    v' = (FreeMonoid.of j * FreeMonoid.of k) ∨ v' = (FreeMonoid.of k * FreeMonoid.of j) := by
  have h1 := h
  apply congrArg length at h
  apply congrArg generators at h1
  rcases length_eq_two.mp h.symm with ⟨c, d, rfl⟩
  simp only [generators_mk, symbols_mul, symbols_of] at h1
  have : j ∈ ({c} ∪ {d} : Finset ℕ) := by grind
  simp only [Finset.mem_union, Finset.mem_singleton] at this
  rcases this with ⟨one, two, rfl⟩
  · have : k ∈ ({j} ∪ {d} : Finset ℕ) := by grind
    grind
  have : k ∈ ({c} ∪ {d} : Finset ℕ) := by grind
  grind

theorem triplet_eq {j k : ℕ} (h : j.dist k = 1) : ⟦(of j * of k * of j)⟧ =
   (⟦v'⟧ : BraidMonoidInf) → v' = (of j * of k * of j) ∨ v' = (of k * of j * of k) := by
  have H : ∀ t, (t = (FreeMonoid.of j * FreeMonoid.of k * FreeMonoid.of j) ∨ t = of k * of j * of k) →
      rel t v' → v' = (of j * of k * of j) ∨ v' = (of k * of j * of k) := by
    intro t t_is rel_holds
    revert t_is
    apply rel_induction_rw rel_holds
    · exact fun a t_is => t_is
    · intro a b c d br_ab t_is
      rcases br_ab with i | far
      · have t_is' := t_is
        have cd_length : c.length = 0 ∧ d.length = 0 := by
          rcases t_is with one | two
          · apply congrArg FreeMonoid.length at one
            simp only [FreeMonoid.length_mul, FreeMonoid.length_of, Nat.reduceAdd] at one
            constructor
            · linarith [one]
            linarith [one]
          apply congrArg FreeMonoid.length at two
          simp only [FreeMonoid.length_mul, FreeMonoid.length_of, Nat.reduceAdd] at two
          constructor
          · linarith [two]
          linarith [two]
        have c_is := length_eq_zero.mp cd_length.1
        have d_is := length_eq_zero.mp cd_length.2
        rw [c_is, d_is, one_mul, mul_one]
        rw [c_is, d_is, one_mul, mul_one] at t_is'
        rcases t_is' with one | two
        · right
          rw [(FreeMonoid.parts_eq (FreeMonoid.parts_eq one).2).1, (FreeMonoid.parts_eq one).1]
        left
        rw [(FreeMonoid.parts_eq (FreeMonoid.parts_eq two).2).1, (FreeMonoid.parts_eq two).1]
      rename_i j1 h1
      exfalso
      have : (j = far ∧ k = j1) ∨ (j = j1 ∧ k = far) := by
        by_cases c_is : c = 1
        · rw [c_is, one_mul] at t_is
          rcases t_is with one | two
          · left
            rw [(FreeMonoid.parts_eq (FreeMonoid.parts_eq one).2).1, (FreeMonoid.parts_eq one).1]
            exact ⟨rfl, rfl⟩
          right
          rw [(FreeMonoid.parts_eq (FreeMonoid.parts_eq two).2).1, (FreeMonoid.parts_eq two).1]
          exact ⟨rfl, rfl⟩
        rcases FreeMonoid.neq_one c_is with ⟨a, b, habc⟩
        rw [habc] at t_is
        repeat rw [mul_assoc] at t_is
        rcases t_is with one | two
        · have H2 := congr_arg FreeMonoid.length (FreeMonoid.parts_eq one).2
          simp only [FreeMonoid.length_mul, FreeMonoid.length_of, Nat.reduceAdd] at H2
          have b_length_zero : b.length = 0 := by linarith [H2]
          have d_length_zero : d.length = 0 := by linarith [H2]
          have b_is : b = 1 := length_eq_zero.mp b_length_zero
          have d_is : d = 1 := length_eq_zero.mp d_length_zero
          rw [b_is, d_is, one_mul, mul_one] at one
          have H3 := (FreeMonoid.parts_eq one).2
          rw [(FreeMonoid.parts_eq H3).1, FreeMonoid.of_injective (FreeMonoid.parts_eq H3).2]
          right
          exact ⟨rfl, rfl⟩
        have H2 := congr_arg FreeMonoid.length (FreeMonoid.parts_eq two).2
        simp only [FreeMonoid.length_mul, FreeMonoid.length_of, Nat.reduceAdd] at H2
        have b_length_zero : b.length = 0 := by linarith [H2]
        have d_length_zero : d.length = 0 := by linarith [H2]
        have b_is : b = 1 := length_eq_zero.mp b_length_zero
        have d_is : d = 1 := length_eq_zero.mp d_length_zero
        rw [b_is, d_is, one_mul, mul_one] at two
        have H3 := (FreeMonoid.parts_eq two).2
        rw [(FreeMonoid.parts_eq H3).1, FreeMonoid.of_injective (FreeMonoid.parts_eq H3).2]
        left
        exact ⟨rfl, rfl⟩
      grind [Nat.dist]
    · intro a b c d br_ab t_is
      rcases br_ab with i | far
      · have t_is' := t_is
        have cd_length : c.length = 0 ∧ d.length = 0 := by
          rcases t_is with one | two
          · apply congrArg FreeMonoid.length at one
            simp only [FreeMonoid.length_mul, FreeMonoid.length_of, Nat.reduceAdd] at one
            constructor
            · linarith [one]
            linarith [one]
          apply congrArg FreeMonoid.length at two
          simp only [FreeMonoid.length_mul, FreeMonoid.length_of, Nat.reduceAdd] at two
          constructor
          · linarith [two]
          linarith [two]
        have c_is := length_eq_zero.mp cd_length.1
        have d_is := length_eq_zero.mp cd_length.2
        rw [c_is, d_is, one_mul, mul_one]
        rw [c_is, d_is, one_mul, mul_one] at t_is'
        rcases t_is' with one | two
        · right
          rw [(FreeMonoid.parts_eq one).1, (FreeMonoid.parts_eq (FreeMonoid.parts_eq one).2).1]
        left
        rw [(FreeMonoid.parts_eq two).1, (FreeMonoid.parts_eq (FreeMonoid.parts_eq two).2).1]
      rename_i j1 h1
      exfalso
      have H : (j = far ∧ k = j1) ∨ (j = j1 ∧ k = far) := by
        by_cases c_is : c = 1
        · rw [c_is, one_mul] at t_is
          rcases t_is with h1 | h2
          · right
            rw [(FreeMonoid.parts_eq (FreeMonoid.parts_eq h1).2).1, (FreeMonoid.parts_eq h1).1]
            exact ⟨rfl, rfl⟩
          left
          rw [(FreeMonoid.parts_eq (FreeMonoid.parts_eq h2).2).1, (FreeMonoid.parts_eq h2).1]
          exact ⟨rfl, rfl⟩
        rcases FreeMonoid.neq_one c_is with ⟨a, b, rfl⟩
        repeat rw [mul_assoc] at t_is
        rcases t_is with h1 | h2
        · have := congr_arg FreeMonoid.length (FreeMonoid.parts_eq h1).2
          simp only [FreeMonoid.length_mul, FreeMonoid.length_of, Nat.reduceAdd] at this
          have b_is : b = 1 := length_eq_zero.mp (by linarith [this])
          have d_is : d = 1 := length_eq_zero.mp (by linarith [this])
          rw [b_is, d_is, one_mul, mul_one] at h1
          rw [(FreeMonoid.parts_eq (FreeMonoid.parts_eq h1).2).1,
            FreeMonoid.of_injective (FreeMonoid.parts_eq (FreeMonoid.parts_eq h1).2).2]
          left
          exact ⟨rfl, rfl⟩
        have := congr_arg FreeMonoid.length (FreeMonoid.parts_eq h2).2
        simp only [FreeMonoid.length_mul, FreeMonoid.length_of, Nat.reduceAdd] at this
        have b_is : b = 1 := length_eq_zero.mp (by linarith [this])
        have d_is : d = 1 := length_eq_zero.mp (by linarith [this])
        rw [b_is, d_is, one_mul, mul_one] at h2
        rw [(FreeMonoid.parts_eq (FreeMonoid.parts_eq h2).2).1,
          FreeMonoid.of_injective (FreeMonoid.parts_eq (FreeMonoid.parts_eq h2).2).2]
        right
        exact ⟨rfl, rfl⟩
      grind [Nat.dist]
    exact fun _ _ _ n d_is => n.2 (n.1 d_is)
  intro rel_holds
  apply BraidMonoidInf.exact at rel_holds
  exact H (FreeMonoid.of j * FreeMonoid.of k * FreeMonoid.of j) (Or.inl rfl) rel_holds

theorem sound : BraidMonoidInf.rel a b → BraidMonoidInf.mk a = BraidMonoidInf.mk b :=
  PresentedMonoid.sound

theorem refl : BraidMonoidInf.rel a a := PresentedMonoid.refl
theorem reg : ∀ c d, BraidMonoidInf.rel a b → BraidMonoidInf.rel (c * a * d) (c * b * d) :=
  fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left h)
theorem symm : ∀ c d, BraidMonoidInf.rel a b → BraidMonoidInf.rel (c * b * d) (c * a * d) :=
  fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left (PresentedMonoid.symm h))
theorem concat : BraidMonoidInf.rel a b → BraidMonoidInf.rel c d →
  BraidMonoidInf.rel (a * c) (b * d) := PresentedMonoid.mul
theorem append_left : BraidMonoidInf.rel c d →
  BraidMonoidInf.rel (a * c) (a * d) := PresentedMonoid.append_left
theorem append_right : BraidMonoidInf.rel a b →
  BraidMonoidInf.rel (a * c) (b * c) := PresentedMonoid.append_right

theorem refl_mk : BraidMonoidInf.mk a = BraidMonoidInf.mk a := BraidMonoidInf.sound (refl)
theorem reg_mk : ∀ c d, BraidMonoidInf.mk a = BraidMonoidInf.mk b → BraidMonoidInf.mk (c * a * d) =
    BraidMonoidInf.mk (c * b * d) :=
  fun _ _ h => BraidMonoidInf.sound (reg _ _ (PresentedMonoid.exact h))
theorem symm_mk : ∀ c d, BraidMonoidInf.mk a = BraidMonoidInf.mk b → BraidMonoidInf.mk (c * b * d) =
    BraidMonoidInf.mk (c * a * d) :=
  fun _ _ h => BraidMonoidInf.sound (reg _ _ (PresentedMonoid.exact h.symm))
theorem concat_mk : BraidMonoidInf.mk a = BraidMonoidInf.mk b →
    BraidMonoidInf.mk c = BraidMonoidInf.mk d →
    BraidMonoidInf.mk (a * c) = BraidMonoidInf.mk (b * d) :=
  fun h1 h2 => BraidMonoidInf.sound (concat (BraidMonoidInf.exact h1) (BraidMonoidInf.exact h2))
theorem append_left_mk : BraidMonoidInf.mk c = BraidMonoidInf.mk d →
    BraidMonoidInf.mk (a * c) = BraidMonoidInf.mk (a * d) :=
  fun h => BraidMonoidInf.sound (append_left (BraidMonoidInf.exact h))
theorem append_right_mk : BraidMonoidInf.mk a = BraidMonoidInf.mk b →
    BraidMonoidInf.mk (a * c) = BraidMonoidInf.mk (b * c) :=
  fun h => BraidMonoidInf.sound (append_right (BraidMonoidInf.exact h))

theorem comm {j k : ℕ} (h : j.dist k >= 2) :
    BraidMonoidInf.mk (of j * of k) = BraidMonoidInf.mk (of k * of j) := by
  apply PresentedMonoid.sound
  rcases or_dist_iff.mp h
  · apply PresentedMonoid.rels_alone
    apply braid_rels_m_inf.separated
    assumption
  apply PresentedMonoid.symm_alone
  apply braid_rels_m_inf.separated
  assumption

theorem comm_rel {j k : ℕ} (h : j.dist k >= 2) :
    BraidMonoidInf.rel (of j * of k) (of k * of j) := by
  rcases or_dist_iff.mp h
  · apply PresentedMonoid.rels_alone
    apply braid_rels_m_inf.separated
    assumption
  apply PresentedMonoid.symm_alone
  apply braid_rels_m_inf.separated
  assumption

theorem braid {j k : ℕ} (h : j.dist k = 1) :
    BraidMonoidInf.mk (of j * of k * of j) = BraidMonoidInf.mk (of k * of j * of k) := by
  apply PresentedMonoid.sound
  rcases or_dist_iff_eq.mp h
  · apply PresentedMonoid.rels_alone
    rename_i k_is
    rw [← k_is]
    exact braid_rels_m_inf.adjacent _
  apply PresentedMonoid.symm_alone
  rename_i j_is
  rw [← j_is]
  exact braid_rels_m_inf.adjacent _

theorem braid_rel {j k : ℕ} (h : j.dist k = 1) :
    BraidMonoidInf.rel (of j * of k * of j) (of k * of j * of k) := by
  rcases or_dist_iff_eq.mp h
  · apply PresentedMonoid.rels_alone
    rename_i k_is
    rw [← k_is]
    exact braid_rels_m_inf.adjacent _
  apply PresentedMonoid.symm_alone
  rename_i j_is
  rw [← j_is]
  exact braid_rels_m_inf.adjacent _

theorem comm_rel_eq (i j : ℕ) (h : i.dist j > 1) : BraidMonoidInf.mk (FreeMonoid.of i) * BraidMonoidInf.mk (of j) =
   BraidMonoidInf.mk (of j) * BraidMonoidInf.mk (of i) := by sorry

theorem comm_rel_rw (x i j) (h : i.dist j > 1) : x *  BraidMonoidInf.mk (of i) * BraidMonoidInf.mk (of j) =
   x * BraidMonoidInf.mk (of j) * BraidMonoidInf.mk (of i) := by sorry

theorem braid_rel_eq (i j) (h : i.dist j = 1) : BraidMonoidInf.mk (of i) * .mk (of j) * .mk (of i)=
   .mk (of j) * .mk (of i) * .mk (of j) := by sorry
theorem braid_rel_rw (x i j) (h : i.dist j = 1) : x *  BraidMonoidInf.mk (of i) * .mk (of j) * .mk (of i) =
   x * .mk (of j) * .mk (of i) * .mk (of j) := by sorry
