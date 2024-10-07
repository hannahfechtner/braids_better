import BraidProject.PresentedMonoid_mine
import Mathlib.Data.Nat.Dist
import BraidProject.Nat_Dist_Additions

theorem FreeMonoid'.parts_eq (h : FreeMonoid'.of a * b = FreeMonoid'.of c * d) : a = c ∧ b = d := by
  apply List.append_inj at h
  simp only [toList_of, List.length_singleton, List.cons.injEq, and_true,
    EmbeddingLike.apply_eq_iff_eq, true_implies] at h
  exact h

theorem FreeMonoid'.neq_one {c : FreeMonoid' α} (h : c ≠ 1) : ∃ a b, c = FreeMonoid'.of a * b := by
  induction c using FreeMonoid'.inductionOn'
  · exact (h rfl).elim
  rename_i head tail _
  use head, tail

open FreeMonoid'

inductive braid_rels_multi {n : ℕ} : FreeMonoid' (Fin (n + 2)) → FreeMonoid' (Fin (n + 2)) → Prop
  | adjacent (i : Fin (n + 1)) : braid_rels_multi (of i.castSucc * of i.succ * of i.castSucc)
                                                 (of i.succ * of i.castSucc * of i.succ)
  | separated (i j : Fin n) (h : i ≤ j) : braid_rels_multi (of i.castSucc.castSucc * of j.succ.succ)
                                                          (of j.succ.succ * of i.castSucc.castSucc)

def braid_rels_m : (n : ℕ) → (FreeMonoid' (Fin n) → FreeMonoid' (Fin n) → Prop)
  | 0     => (λ _ _ => False)
  | 1     => (λ _ _ => False)
  | n + 2 => @braid_rels_multi n

def BraidMonoid (n : ℕ) := PresentedMonoid (braid_rels_m n.pred)

instance (n : ℕ) : Monoid (BraidMonoid n) := by unfold BraidMonoid; infer_instance


-- for the braid with infinitely many strands
inductive braid_rels_m_inf : FreeMonoid' ℕ → FreeMonoid' ℕ → Prop
  | adjacent (i : ℕ): braid_rels_m_inf (of i * of (i+1) * of i) (of (i+1) * of i * of (i+1))
  | separated (i j : ℕ) (h : i +2 ≤ j) : braid_rels_m_inf (of i * of j) (of j * of i)

theorem length_pos {f g : FreeMonoid' ℕ} (h : braid_rels_m_inf f g) : f.length > 0 := by
  rcases h
  · simp only [length_mul, length_of, Nat.reduceAdd, gt_iff_lt, Nat.ofNat_pos]
  simp only [length_mul, length_of, Nat.reduceAdd, gt_iff_lt, Nat.ofNat_pos]

open PresentedMonoid

def BraidMonoidInf := PresentedMonoid braid_rels_m_inf

namespace BraidMonoidInf -- end this

def rel := PresentedMonoid.rel braid_rels_m_inf

protected def mk := PresentedMonoid.mk (braid_rels_m_inf)

theorem mul_mk : BraidMonoidInf.mk (a * b) = BraidMonoidInf.mk a * BraidMonoidInf.mk b :=
  rfl

theorem mk_one : BraidMonoidInf.mk 1 = 1 := rfl

instance : Monoid BraidMonoidInf := by unfold BraidMonoidInf; infer_instance

@[induction_eliminator]
protected theorem inductionOn {δ : BraidMonoidInf → Prop} (q : BraidMonoidInf)
    (h : ∀ a, δ (BraidMonoidInf.mk a)) : δ q :=
  Quotient.ind h q

-- define the length of elements of the monoid
def length : BraidMonoidInf → ℕ :=
  PresentedMonoid.lift_of_mul (FreeMonoid'.length)
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
  induction' a ; induction' b
  rw [← mul_mk, length_mk, length_mk, length_mk, FreeMonoid'.length_mul]

theorem length_eq (h : BraidMonoidInf.mk a = BraidMonoidInf.mk b) : a.length = b.length :=
  congr_arg length h

theorem one_of_eq_mk_one {a : FreeMonoid' ℕ}
    (h : BraidMonoidInf.mk a = BraidMonoidInf.mk (1 : FreeMonoid' ℕ)) :
    a = (1 : FreeMonoid' ℕ) := FreeMonoid'.eq_one_of_length_eq_zero (congrArg length h)

private theorem symbols_helper : ∀ (a b : FreeMonoid' ℕ), braid_rels_m_inf a b → a.symbols = b.symbols := by
  intro a b hr
  induction hr
  · ext x
    simp only [symbols_mul, symbols_of, Finset.union_assoc, Finset.mem_union, Finset.mem_singleton]
    tauto
  simp only [symbols_mul, symbols_of]
  exact Finset.union_comm _ _

-- returns the set of generators appearing in a braid word
def braid_generators : BraidMonoidInf → Finset ℕ :=
  PresentedMonoid.lift_of_mul (FreeMonoid'.symbols)
  (fun ih1 ih2 => by rw [symbols_mul, symbols_mul, ih1, ih2]) symbols_helper

@[simp]
theorem braid_generators_one : braid_generators 1 = ∅ := rfl

@[simp]
theorem braid_generators_mk : braid_generators (BraidMonoidInf.mk a) = FreeMonoid'.symbols a :=
  rfl

@[simp]
theorem braid_generators_mul : braid_generators (a * b) =
    braid_generators a ∪ braid_generators b := by
  induction' a
  induction' b
  rw [← mul_mk, braid_generators_mk, braid_generators_mk, braid_generators_mk,
    symbols_mul]

private theorem reverse_helper : ∀ (a b : FreeMonoid' ℕ),
    braid_rels_m_inf a b → (fun x ↦ mk braid_rels_m_inf x.reverse) a =
    (fun x ↦ mk braid_rels_m_inf x.reverse) b := by
  intro a b h
  beta_reduce
  induction h with
  | adjacent i =>
    simp only [reverse_mul, reverse_of]
    -- need a braidmonoidinf version
    exact PresentedMonoid.sound (PresentedMonoid.rel_alone (braid_rels_m_inf.adjacent i))
  | separated i j h =>
    simp only [reverse_mul, reverse_of]
    exact PresentedMonoid.sound (PresentedMonoid.symm_alone (braid_rels_m_inf.separated _ _ h))

def reverse_braid : BraidMonoidInf → BraidMonoidInf :=
  PresentedMonoid.lift_of_mul (fun x => mk braid_rels_m_inf <| FreeMonoid'.reverse x)
  (fun h1 h2 => by simp [reverse_mul, mul_mk, h1, h2]) reverse_helper

@[simp]
theorem reverse_braid_one : reverse_braid 1 = 1 := rfl

@[simp]
theorem reverse_braid_mk : reverse_braid (BraidMonoidInf.mk a) =
  BraidMonoidInf.mk (FreeMonoid'.reverse a) := rfl

@[simp]
theorem reverse_braid_mul : reverse_braid (a * b) = reverse_braid b * reverse_braid a := by
  induction' a with a1
  induction' b with b1
  rw [← mul_mk]
  repeat rw [reverse_braid_mk]
  rw [← mul_mk]
  exact congr_arg _ reverse_mul

@[simp]
theorem length_reverse_eq_length : length (reverse_braid a) = length a := by
  induction' a with a1
  simp only [reverse_braid_mk, length_mk, reverse_length]

theorem exact : mk braid_rels_m_inf a = mk braid_rels_m_inf b →
    PresentedMonoid.rel braid_rels_m_inf a b := Quotient.exact

theorem reverse_reverse : reverse_braid (reverse_braid a) = a := by
  induction a
  rw [reverse_braid_mk, reverse_braid_mk, FreeMonoid'.reverse_reverse]

theorem rel_iff_rel_reverse_reverse : PresentedMonoid.rel braid_rels_m_inf a1.reverse b1.reverse ↔
  PresentedMonoid.rel braid_rels_m_inf a1 b1 := by
  have H : ∀ a1 b1, PresentedMonoid.rel braid_rels_m_inf a1 b1 →
      PresentedMonoid.rel braid_rels_m_inf a1.reverse b1.reverse := by
    intro a1 b1 h
    induction h with
    | of _ _ h =>
      exact braid_rels_m_inf.rec (fun _ => PresentedMonoid.rel_alone (braid_rels_m_inf.adjacent _))
        (fun i j h => PresentedMonoid.symm_alone (braid_rels_m_inf.separated i j h)) h
    | refl _ => exact PresentedMonoid.refl
    | symm _ h => exact Con'Gen.Rel.symm h
    | trans _ _ h1 h2 => exact h1.trans h2
    | mul _ _ h1 h2 =>
      rw [reverse_mul, reverse_mul]
      exact PresentedMonoid.mul h2 h1
  constructor
  · intro h
    have H1 := H _ _ h
    simp only [FreeMonoid'.reverse_reverse] at H1
    exact H1
  exact H _ _

theorem eq_iff_reverse_eq_reverse : a = b ↔ reverse_braid a = reverse_braid b := by
  constructor
  · intro h
    rw [h]
  intro h
  induction' a ; induction' b
  simp only [reverse_braid_mk] at h
  apply PresentedMonoid.sound -- this should be somehow protected in the namespace
  exact rel_iff_rel_reverse_reverse.mp (PresentedMonoid.exact h)

theorem singleton_eq (h : BraidMonoidInf.mk (of i) = BraidMonoidInf.mk a) : a = of i := by
  have h1 := congrArg braid_generators h
  apply congrArg length at h
  rw [length_mk, length_mk, length_of] at h
  rw [braid_generators_mk, symbols_of] at h1
  rcases length_eq_one.mp h.symm with ⟨b, rfl⟩
  rw [braid_generators_mk, symbols_of, Finset.singleton_inj] at h1
  rw [h1]

theorem pair_eq (h : Nat.dist j k >= 2) : BraidMonoidInf.mk (of j * of k) = BraidMonoidInf.mk v' →
    v' = (FreeMonoid'.of j * FreeMonoid'.of k) ∨ v' = (FreeMonoid'.of k * FreeMonoid'.of j) := by
  intro h'
  have h1 := h'
  apply congrArg length at h'
  apply congrArg braid_generators at h1
  rw [length_mk, length_mk] at h'
  simp only [FreeMonoid'.length_mul, length_of, Nat.reduceAdd] at h'
  have h2 := h'.symm
  rcases length_eq_two.mp h'.symm with ⟨c, d, rfl⟩
  simp only [braid_generators_mk, symbols_mul, symbols_of] at h1
  have H1 : j ∈ ({c} ∪ {d} : Finset ℕ) := by
    have H2 : j ∈ ({j} ∪ {k} : Finset ℕ) := Finset.mem_union.mpr
      (Or.inl (Finset.mem_singleton.mpr rfl))
    rw [h1] at H2
    exact H2
  simp only [Finset.mem_union, Finset.mem_singleton] at H1
  rcases H1 with ⟨one, two, rfl⟩
  · left
    rw [mul_right_inj]
    apply congr_arg
    symm
    have H1 : k ∈ ({j} ∪ {d} : Finset ℕ) := by
      have H2 : k ∈ ({j} ∪ {k} : Finset ℕ) := Finset.mem_union.mpr
        (Or.inr (Finset.mem_singleton.mpr rfl))
      rw [h1] at H2
      exact H2
    simp only [Finset.mem_union, Finset.mem_singleton] at H1
    rcases H1 with ⟨three, four, rfl⟩
    · simp only [Finset.union_idempotent, Finset.left_eq_union, Finset.subset_singleton_iff,
      Finset.singleton_ne_empty, Finset.singleton_inj, false_or] at h1
      exact h1.symm
    assumption
  rename_i h_jd
  rw [h_jd]
  rw [h_jd] at h1
  right
  rw [mul_left_inj]
  apply congr_arg
  symm
  have H1 : k ∈ ({c} ∪ {d} : Finset ℕ) := by
    have H2 : k ∈ ({d} ∪ {k} : Finset ℕ) := Finset.mem_union.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))
    rw [h1] at H2
    exact H2
  simp only [Finset.mem_union, Finset.mem_singleton] at H1
  rcases H1 with ⟨three, four, rfl⟩
  · rfl
  rename_i ih
  rw [ih, h_jd] at h
  simp only [Nat.dist_self, ge_iff_le, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero] at h

-- look up what other people do in the library
theorem triplet_eq (h : Nat.dist j k = 1) : BraidMonoidInf.mk (of j * of k * of j) =
    BraidMonoidInf.mk v' → v' = (of j * of k * of j) ∨ v' = (of k * of j * of k) := by
  generalize ht : of j * of k * of j = t
  intro rel_holds
  apply BraidMonoidInf.exact at rel_holds
  -- apply rel_induction_rw rel_holds
  -- · intro a
  --   left
  --   rfl
  -- sorry
  have H : ∀ t, (t = (FreeMonoid'.of j * FreeMonoid'.of k * FreeMonoid'.of j) ∨ t = of k * of j * of k) →
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
          · apply congrArg FreeMonoid'.length at one
            simp only [FreeMonoid'.length_mul, FreeMonoid'.length_of, Nat.reduceAdd] at one
            constructor
            · linarith [one]
            linarith [one]
          apply congrArg FreeMonoid'.length at two
          simp only [FreeMonoid'.length_mul, FreeMonoid'.length_of, Nat.reduceAdd] at two
          constructor
          · linarith [two]
          linarith [two]
        have c_is := eq_one_of_length_eq_zero cd_length.1
        have d_is := eq_one_of_length_eq_zero cd_length.2
        rw [c_is, d_is, one_mul, mul_one]
        rw [c_is, d_is, one_mul, mul_one] at t_is'
        rcases t_is' with one | two
        · right
          rw [(FreeMonoid'.parts_eq (FreeMonoid'.parts_eq one).2).1, (FreeMonoid'.parts_eq one).1]
        left
        rw [(FreeMonoid'.parts_eq (FreeMonoid'.parts_eq two).2).1, (FreeMonoid'.parts_eq two).1]
      rename_i j1 h1
      exfalso
      have H : (j = far ∧ k = j1) ∨ (j = j1 ∧ k = far) := by
        by_cases c_is : c = 1
        · rw [c_is, one_mul] at t_is
          rcases t_is with one | two
          · left
            rw [(FreeMonoid'.parts_eq (FreeMonoid'.parts_eq one).2).1, (FreeMonoid'.parts_eq one).1]
            exact ⟨rfl, rfl⟩
          right
          rw [(FreeMonoid'.parts_eq (FreeMonoid'.parts_eq two).2).1, (FreeMonoid'.parts_eq two).1]
          exact ⟨rfl, rfl⟩
        rcases FreeMonoid'.neq_one c_is with ⟨a, b, habc⟩
        rw [habc] at t_is
        repeat rw [mul_assoc] at t_is
        rcases t_is with one | two
        · have H2 := congr_arg FreeMonoid'.length (FreeMonoid'.parts_eq one).2
          simp only [FreeMonoid'.length_mul, FreeMonoid'.length_of, Nat.reduceAdd] at H2
          have b_length_zero : b.length = 0 := by linarith [H2]
          have d_length_zero : d.length = 0 := by linarith [H2]
          have b_is : b = 1 := eq_one_of_length_eq_zero b_length_zero
          have d_is : d = 1 := eq_one_of_length_eq_zero d_length_zero
          rw [b_is, d_is, one_mul, mul_one] at one
          have H3 := (FreeMonoid'.parts_eq one).2
          rw [(FreeMonoid'.parts_eq H3).1, FreeMonoid'.of_injective (FreeMonoid'.parts_eq H3).2]
          right
          exact ⟨rfl, rfl⟩
        have H2 := congr_arg FreeMonoid'.length (FreeMonoid'.parts_eq two).2
        simp only [FreeMonoid'.length_mul, FreeMonoid'.length_of, Nat.reduceAdd] at H2
        have b_length_zero : b.length = 0 := by linarith [H2]
        have d_length_zero : d.length = 0 := by linarith [H2]
        have b_is : b = 1 := eq_one_of_length_eq_zero b_length_zero
        have d_is : d = 1 := eq_one_of_length_eq_zero d_length_zero
        rw [b_is, d_is, one_mul, mul_one] at two
        have H3 := (FreeMonoid'.parts_eq two).2
        rw [(FreeMonoid'.parts_eq H3).1, FreeMonoid'.of_injective (FreeMonoid'.parts_eq H3).2]
        left
        exact ⟨rfl, rfl⟩
      rcases H with one | two
      · unfold Nat.dist at h
        rw [one.1, one.2, Nat.sub_eq_zero_of_le (le_of_add_le_left h1), zero_add] at h
        rw [((Nat.sub_eq_iff_eq_add (le_of_add_le_left h1)).mp h)] at h1
        linarith [h1]
      unfold Nat.dist at h
      rw [two.1, two.2, Nat.sub_eq_zero_of_le (le_of_add_le_left h1), add_zero] at h
      rw [((Nat.sub_eq_iff_eq_add (le_of_add_le_left h1)).mp h)] at h1
      linarith [h1]
    · intro a b c d br_ab t_is
      rcases br_ab with i | far
      · have t_is' := t_is
        have cd_length : c.length = 0 ∧ d.length = 0 := by
          rcases t_is with one | two
          · apply congrArg FreeMonoid'.length at one
            simp only [FreeMonoid'.length_mul, FreeMonoid'.length_of, Nat.reduceAdd] at one
            constructor
            · linarith [one]
            linarith [one]
          apply congrArg FreeMonoid'.length at two
          simp only [FreeMonoid'.length_mul, FreeMonoid'.length_of, Nat.reduceAdd] at two
          constructor
          · linarith [two]
          linarith [two]
        have c_is := eq_one_of_length_eq_zero cd_length.1
        have d_is := eq_one_of_length_eq_zero cd_length.2
        rw [c_is, d_is, one_mul, mul_one]
        rw [c_is, d_is, one_mul, mul_one] at t_is'
        rcases t_is' with one | two
        · right
          rw [(FreeMonoid'.parts_eq one).1, (FreeMonoid'.parts_eq (FreeMonoid'.parts_eq one).2).1]
        left
        rw [(FreeMonoid'.parts_eq two).1, (FreeMonoid'.parts_eq (FreeMonoid'.parts_eq two).2).1]
      rename_i j1 h1
      exfalso
      have H : (j = far ∧ k = j1) ∨ (j = j1 ∧ k = far) := by
        by_cases c_is : c = 1
        · rw [c_is, one_mul] at t_is
          rcases t_is with one | two
          · right
            rw [(FreeMonoid'.parts_eq (FreeMonoid'.parts_eq one).2).1, (FreeMonoid'.parts_eq one).1]
            exact ⟨rfl, rfl⟩
          left
          rw [(FreeMonoid'.parts_eq (FreeMonoid'.parts_eq two).2).1, (FreeMonoid'.parts_eq two).1]
          exact ⟨rfl, rfl⟩
        rcases FreeMonoid'.neq_one c_is with ⟨a, b, habc⟩
        rw [habc] at t_is
        repeat rw [mul_assoc] at t_is
        rcases t_is with one | two
        · have H2 := congr_arg FreeMonoid'.length (FreeMonoid'.parts_eq one).2
          simp only [FreeMonoid'.length_mul, FreeMonoid'.length_of, Nat.reduceAdd] at H2
          have b_length_zero : b.length = 0 := by linarith [H2]
          have d_length_zero : d.length = 0 := by linarith [H2]
          have b_is : b = 1 := eq_one_of_length_eq_zero b_length_zero
          have d_is : d = 1 := eq_one_of_length_eq_zero d_length_zero
          rw [b_is, d_is, one_mul, mul_one] at one
          have H3 := (FreeMonoid'.parts_eq one).2
          rw [(FreeMonoid'.parts_eq H3).1, FreeMonoid'.of_injective (FreeMonoid'.parts_eq H3).2]
          left
          exact ⟨rfl, rfl⟩
        have H2 := congr_arg FreeMonoid'.length (FreeMonoid'.parts_eq two).2
        simp only [FreeMonoid'.length_mul, FreeMonoid'.length_of, Nat.reduceAdd] at H2
        have b_length_zero : b.length = 0 := by linarith [H2]
        have d_length_zero : d.length = 0 := by linarith [H2]
        have b_is : b = 1 := eq_one_of_length_eq_zero b_length_zero
        have d_is : d = 1 := eq_one_of_length_eq_zero d_length_zero
        rw [b_is, d_is, one_mul, mul_one] at two
        have H3 := (FreeMonoid'.parts_eq two).2
        rw [(FreeMonoid'.parts_eq H3).1, FreeMonoid'.of_injective (FreeMonoid'.parts_eq H3).2]
        right
        exact ⟨rfl, rfl⟩
      rcases H with one | two
      · unfold Nat.dist at h
        rw [one.1, one.2, Nat.sub_eq_zero_of_le (le_of_add_le_left h1), zero_add] at h
        rw [((Nat.sub_eq_iff_eq_add (le_of_add_le_left h1)).mp h)] at h1
        linarith [h1]
      unfold Nat.dist at h
      rw [two.1, two.2, Nat.sub_eq_zero_of_le (le_of_add_le_left h1), add_zero] at h
      rw [((Nat.sub_eq_iff_eq_add (le_of_add_le_left h1)).mp h)] at h1
      linarith [h1]
    exact fun _ _ _ n d_is => n.2 (n.1 d_is)
  specialize H (FreeMonoid'.of j * FreeMonoid'.of k * FreeMonoid'.of j) (Or.inl rfl)
  rw [← ht] at rel_holds
  specialize H rel_holds
  rw [← ht]
  exact H

theorem sound : BraidMonoidInf.rel a b → BraidMonoidInf.mk a = BraidMonoidInf.mk b :=
  PresentedMonoid.sound

theorem refl : BraidMonoidInf.rel a a := PresentedMonoid.refl
theorem reg : ∀ c d, BraidMonoidInf.rel a b → BraidMonoidInf.rel (c * a * d) (c * b * d) :=
  fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left h)
theorem symm : ∀ c d, BraidMonoidInf.rel a b → BraidMonoidInf.rel (c * b * d) (c * a * d) :=
  fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left (PresentedMonoid.swap h))
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
  · apply PresentedMonoid.rel_alone
    apply braid_rels_m_inf.separated
    assumption
  apply PresentedMonoid.symm_alone
  apply braid_rels_m_inf.separated
  assumption

theorem comm_rel {j k : ℕ} (h : j.dist k >= 2) :
    BraidMonoidInf.rel (of j * of k) (of k * of j) := by
  rcases or_dist_iff.mp h
  · apply PresentedMonoid.rel_alone
    apply braid_rels_m_inf.separated
    assumption
  apply PresentedMonoid.symm_alone
  apply braid_rels_m_inf.separated
  assumption

theorem braid {j k : ℕ} (h : j.dist k = 1) :
    BraidMonoidInf.mk (of j * of k * of j) = BraidMonoidInf.mk (of k * of j * of k) := by
  apply PresentedMonoid.sound
  rcases or_dist_iff_eq.mp h
  · apply PresentedMonoid.rel_alone
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
  · apply PresentedMonoid.rel_alone
    rename_i k_is
    rw [← k_is]
    exact braid_rels_m_inf.adjacent _
  apply PresentedMonoid.symm_alone
  rename_i j_is
  rw [← j_is]
  exact braid_rels_m_inf.adjacent _

-- theorem mem_steps_to {n : ℕ}: ∀ (a b : FreeMonoid (Fin (Nat.pred n))),
--     StepsTo (braid_rels_m (Nat.pred n)) a b → (∀ x, x ∈ a ↔ x ∈ b) := by
--   intro a b st x
--   constructor
--   · intro in_a
--     apply FreeMonoid.mem_symbols.mp
--     apply FreeMonoid.mem_symbols.mpr at in_a
--     rw [← generators_helper _ _ st]
--     exact in_a
--   intro in_b
--   apply FreeMonoid.mem_symbols.mp
--   rw [generators_helper _ _ st]
--   exact FreeMonoid.mem_symbols.mpr in_b

-- theorem generators_inf : ∀ (a b : FreeMonoid ℕ),
--     EqvGen (StepsTo (braid_rels_m_inf)) a b → symbols a = symbols b :=
--   fun _ _ eg => EqvGen.rec (fun x y a => generators_helper_inf x y a)
--   (fun x => Eq.refl (symbols x)) (fun _ _ _ a_ih => a_ih.symm)
--   (fun _ _ _ _ _ a_ih a_ih_1 => a_ih.trans a_ih_1) eg

-- theorem mem_steps_to_inf : ∀ (a b : FreeMonoid ℕ),
--     StepsTo (braid_rels_m_inf) a b → (∀ x, x ∈ a ↔ x ∈ b) := by
--   intro a b st x
--   constructor
--   · intro in_a
--     apply FreeMonoid.mem_symbols.mp
--     rw [← generators_helper_inf _ _ st]
--     exact FreeMonoid.mem_symbols.mpr in_a
--   intro in_b
--   apply FreeMonoid.mem_symbols.mp
--   rw [generators_helper_inf _ _ st]
--   exact FreeMonoid.mem_symbols.mpr in_b

-- theorem generators_unique {n : ℕ} {i : Fin n.pred} {s : FreeMonoid (Fin n.pred)} (neq: s ≠ FreeMonoid.of i)
--     : ¬ StepsTo (@braid_rels_m (n.pred)) s (FreeMonoid.of i) := by
--   intro h
--   apply neq
--   have H := f_preserved_length _ _ h
--   have H1 := generators_helper _ _ h
--   rw [FreeMonoid.length_of] at H
--   match length_eq_one.mp H with
--   | ⟨a, ha⟩ =>
--     rw [ha]
--     rw [ha, symbols_of, symbols_of] at H1
--     simp only [Finset.singleton_inj] at H1
--     rw [H1]
