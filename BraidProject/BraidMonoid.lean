import BraidProject.BraidGroup
import BraidProject.PresentedMonoid_mine
import Mathlib.Data.Nat.Dist
import BraidProject.Nat_Dist_Additions

open FreeMonoid'
inductive braid_rels_multi {n : ℕ} : FreeMonoid' (Fin (n + 2)) → FreeMonoid' (Fin (n + 2)) → Prop
  | adjacent (i : Fin (n + 1)): braid_rels_multi (of i.castSucc * of i.succ * of i.castSucc)
                                                 (of i.succ * of i.castSucc * of i.succ)
  | separated (i j : Fin n) (h : i ≤ j): braid_rels_multi (of i.castSucc.castSucc * of j.succ.succ)
                                                          (of j.succ.succ * of i.castSucc.castSucc)

def braid_rels_m : (n : ℕ) → (FreeMonoid' (Fin n) → FreeMonoid' (Fin n) → Prop)
  | 0     => (λ _ _ => False)
  | 1     => (λ _ _ => False)
  | n + 2 => @braid_rels_multi n

-- for the braid with infinitely many strands
inductive braid_rels_m_inf : FreeMonoid' ℕ → FreeMonoid' ℕ → Prop
  | adjacent (i : ℕ): braid_rels_m_inf (of i * of (i+1) * of i) (of (i+1) * of i * of (i+1))
  | separated (i j : ℕ) (h : i +2 ≤ j): braid_rels_m_inf (of i * of j) (of j * of i)

theorem braid_length_pos (h : braid_rels_m_inf f g) : f.length > 0 := by
  rcases h
  · simp only [length_mul, length_of, Nat.reduceAdd, gt_iff_lt, Nat.ofNat_pos]
  simp only [length_mul, length_of, Nat.reduceAdd, gt_iff_lt, Nat.ofNat_pos]

open PresentedMonoid Braid
-- def braid_rels_inf_set : Set (FreeMonoid ℕ × FreeMonoid ℕ) :=
--   λ p => braid_rels_m_inf p.fst p.snd

-- -- notation 3.1.4, first sentence
-- def BraidSetoidRel (n : ℕ) : FreeMonoid (Fin (n)) → FreeMonoid (Fin (n)) → Prop :=
--           RTSClosure (@braid_rels_m n)

-- def BraidSetoidRel_Inf : FreeMonoid ℕ  → FreeMonoid ℕ  → Prop := RTSClosure braid_rels_m_inf

-- --second part of 3.1.4
-- --I should use "of" for this
-- def word_class {n : ℕ} (l : FreeMonoid (Fin (n))) := Quotient.mk (mySetoid_SC (@braid_rels_m n)) l
-- def word_class_inf (l : FreeMonoid ℕ) := Quotient.mk (mySetoid_SC (@braid_rels_m_inf)) l

abbrev BraidMonoid (n : ℕ) : Type := PresentedMonoid (@braid_rels_m n.pred)
def BraidMonoid_Inf := PresentedMonoid braid_rels_m_inf

abbrev BraidMonoid.mk {n : ℕ} := PresentedMonoid.mk (@braid_rels_m n.pred)
def BraidMonoidInf_mk := PresentedMonoid.mk (braid_rels_m_inf)

--has n strands, numbered 0 to n-1. thus there are n-1 generators, numbered 0 to n-2
abbrev BraidWords (n : ℕ) : Type := (FreeMonoid' (Fin n.pred))
abbrev BraidWords_Inf := (FreeMonoid' ℕ)

theorem embed_helper (n : ℕ) : ∀ (a b : FreeMonoid' (Fin (n.pred))),
  (braid_rels_m (n.pred)) a b → ((FreeMonoid'.lift fun a => σ a) a : braid_group n)= (FreeMonoid'.lift fun a => σ a) b := by
  repeat
    rcases n
    · intro _ _ h
      exfalso
      apply h
    rename_i n
  intro a b h
  rcases h
  · rename_i j
    simp only [_root_.map_mul, lift_eval_of, Nat.pred_succ]
    apply braid_group.braid
  simp only [_root_.map_mul, lift_eval_of, Nat.pred_succ]
  apply braid_group.comm
  next ih => exact ih

def embed {n : ℕ} : (BraidMonoid n) →* (braid_group (n)) :=
  toMonoid (fun a => @σ (n.pred) a) (embed_helper n)

-- define the length of elements of the monoid
def braid_length : PresentedMonoid braid_rels_m_inf → ℕ :=
  PresentedMonoid.lift_of_mul (FreeMonoid'.length)
  (fun h1 h2 => by rw [length_mul, length_mul, h1, h2]) (fun _ _ h => by
  induction h with
  | adjacent i => simp only [length_mul, length_of, Nat.reduceAdd]
  | separated i j _ => simp only [length_mul, length_of, Nat.reduceAdd])

theorem one_of_eq_mk_one {a : FreeMonoid ℕ}
    (h : BraidMonoidInf_mk a = (BraidMonoidInf_mk (1 : FreeMonoid' ℕ))) :
    a = (1 : FreeMonoid ℕ) := by
  have H : braid_length (BraidMonoidInf_mk a) = braid_length 1 := congrArg braid_length h
  simp at H
  unfold braid_length at H
  unfold BraidMonoidInf_mk at H
  rw [PresentedMonoid.lift_of_mul_mk] at H
  · exact FreeMonoid'.eq_one_of_length_eq_zero H
  intro _ _ _ _ h1 h2
  rw [length_mul, length_mul, h1, h2]

theorem symbols_helper : ∀ (a b : FreeMonoid' ℕ), braid_rels_m_inf a b → a.symbols = b.symbols := by
  intro a b hr
  induction hr
  · ext x
    simp only [symbols_mul, symbols_of, Finset.union_assoc, Finset.mem_union, Finset.mem_singleton]
    exact ⟨fun h ↦ Or.casesOn h (fun h1 ↦ Or.inr (Or.inl h1)) fun h2 ↦
      Or.casesOn h2 (fun h3 ↦ Or.inl h3) fun h4 ↦ Or.inr (Or.inl h4),
      fun h ↦ Or.casesOn h (fun h1 ↦ Or.inr (Or.inl h1)) fun h2 ↦
        Or.casesOn h2 (fun h3 ↦ Or.inl h3) fun h4 ↦ Or.inr (Or.inl h4)⟩
  simp only [symbols_mul, symbols_of]
  exact Finset.union_comm _ _

-- returns the set of generators appearing in a braid word
def braid_generators : PresentedMonoid braid_rels_m_inf → Finset ℕ :=
  PresentedMonoid.lift_of_mul (FreeMonoid'.symbols)
  (fun ih1 ih2 => by rw [symbols_mul, symbols_mul, ih1, ih2]) symbols_helper

@[simp]
theorem braid_generators_one : braid_generators 1 = ∅ := rfl

@[simp]
theorem braid_generators_mk : braid_generators (mk braid_rels_m_inf a) = FreeMonoid'.symbols a := rfl

@[simp]
theorem braid_generators_mul : braid_generators (a * b) = braid_generators a ∪ braid_generators b := by
  induction' a
  induction' b
  rw [← PresentedMonoid.mul_mk, braid_generators_mk, braid_generators_mk, braid_generators_mk,
    symbols_mul]

theorem reverse_helper : ∀ (a b : FreeMonoid' ℕ),
  braid_rels_m_inf a b → (fun x ↦ mk braid_rels_m_inf x.reverse) a = (fun x ↦ mk braid_rels_m_inf x.reverse) b := by
  intro a b h
  beta_reduce
  induction h with
  | adjacent i =>
    simp only [reverse_mul, reverse_of]
    exact sound (Con'Gen.Rel.of _ _ (braid_rels_m_inf.adjacent i))
  | separated i j h =>
    simp only [reverse_mul, reverse_of]
    exact sound (Con'Gen.Rel.symm (Con'Gen.Rel.of _ _ (braid_rels_m_inf.separated _ _ h)))

def reverse_braid : PresentedMonoid braid_rels_m_inf → PresentedMonoid braid_rels_m_inf :=
  PresentedMonoid.lift_of_mul (fun x => mk braid_rels_m_inf <| FreeMonoid'.reverse x)
  (fun h1 h2 => by simp [reverse_mul, mul_mk, h1, h2]) reverse_helper

@[simp]
theorem reverse_braid_one : reverse_braid 1 = 1 := rfl
@[simp]
theorem reverse_braid_mk : reverse_braid (mk braid_rels_m_inf a) =
  mk braid_rels_m_inf (FreeMonoid'.reverse a) := rfl

@[simp]
theorem reverse_braid_mul : reverse_braid (a * b) = reverse_braid b * reverse_braid a := by
  induction' a with a1
  induction' b with b1
  rw [← mul_mk]
  repeat rw [reverse_braid_mk]
  rw [← mul_mk]
  exact congr_arg _ reverse_mul

@[simp]
theorem braid_length_one : braid_length 1 = 0 := rfl

@[simp]
theorem braid_length_mk : braid_length (mk braid_rels_m_inf a) = a.length := rfl

@[simp]
theorem braid_length_mul {a b : PresentedMonoid braid_rels_m_inf} : braid_length (a * b) = braid_length a + braid_length b := by
  induction' a
  induction' b
  rw [← mul_mk, braid_length_mk, braid_length_mk, braid_length_mk, FreeMonoid'.length_mul]

theorem braid_length_eq (h : BraidMonoidInf_mk a = BraidMonoidInf_mk b) : a.length = b.length := by
  have H := congr_arg braid_length h
  unfold BraidMonoidInf_mk at H
  simp only [braid_length_mk] at H
  exact H

@[simp]
theorem length_reverse_eq_length : braid_length (reverse_braid a) = braid_length a := by
  induction' a with a1
  simp
theorem exact : mk braid_rels_m_inf a = mk braid_rels_m_inf b → PresentedMonoid.rel braid_rels_m_inf a b := by
  apply Quotient.exact

theorem reverse_reverse : reverse_braid (reverse_braid a) = a := by
  induction a
  simp

theorem rel_reverse_reverse_of_rel : Con'Gen.Rel braid_rels_m_inf a1 b1 →
    Con'Gen.Rel braid_rels_m_inf a1.reverse b1.reverse := by
  intro h
  induction h with
  | of _ _ h =>
    exact braid_rels_m_inf.rec (fun _ => Con'Gen.Rel.of _ _ (braid_rels_m_inf.adjacent _))
      (fun i j h => Con'Gen.Rel.symm (Con'Gen.Rel.of _ _ (braid_rels_m_inf.separated i j h))) h
  | refl _ => exact Con'Gen.Rel.refl _
  | symm _ h => exact Con'Gen.Rel.symm h
  | trans _ _ h1 h2 => exact h1.trans h2
  | mul _ _ h1 h2 =>
    simp only [reverse_mul]
    exact Con'Gen.Rel.mul h2 h1

theorem rel_iff_rel_reverse_reverse : Con'Gen.Rel braid_rels_m_inf a1.reverse b1.reverse ↔
  Con'Gen.Rel braid_rels_m_inf a1 b1 := by
  constructor
  · intro h
    have H := rel_reverse_reverse_of_rel h
    simp only [FreeMonoid'.reverse_reverse] at H
    exact H
  apply rel_reverse_reverse_of_rel

theorem eq_iff_reverse_eq_reverse : a = b ↔ reverse_braid a = reverse_braid b := by
  constructor
  · intro h
    rw [h]
  intro h
  induction' a with a1
  induction' b with b1
  simp at h
  apply sound
  apply PresentedMonoid.exact at h
  unfold rel at h
  apply rel_iff_rel_reverse_reverse.mp h


theorem singleton_eq : BraidMonoidInf_mk (of i) = BraidMonoidInf_mk a → a = of i := by
  intro h
  have h1 := h
  apply congrArg braid_length at h
  apply congrArg braid_generators at h1
  erw [braid_length_mk, braid_length_mk] at h
  simp at h
  unfold BraidMonoidInf_mk at h1
  simp at h1
  have h2 := h.symm
  rw [length_eq_one] at h2
  rcases h2 with ⟨b, rfl⟩
  simp at h1
  rw [h1]


theorem pair_eq (h : Nat.dist j k >= 2) : BraidMonoidInf_mk (of j * of k) = BraidMonoidInf_mk v' →
    v' = (FreeMonoid'.of j * FreeMonoid'.of k) ∨ v' = (FreeMonoid'.of k * FreeMonoid'.of j) := by
  intro h'
  have h1 := h'
  apply congrArg braid_length at h'
  apply congrArg braid_generators at h1
  erw [braid_length_mk, braid_length_mk] at h'
  simp at h'
  unfold BraidMonoidInf_mk at h1
  simp at h1
  have h2 := h'.symm
  rcases length_eq_two.mp h'.symm with ⟨c, d, rfl⟩
  rw [symbols_mul, symbols_of, symbols_of] at h1
  have H1 : j ∈ ({c} ∪ {d} : Finset ℕ) := by
    have H2 : j ∈ ({j} ∪ {k} : Finset ℕ) := Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr rfl))
    rw [h1] at H2
    exact H2
  simp at H1
  rcases H1 with ⟨one, two, rfl⟩
  · left
    rw [mul_right_inj]
    apply congr_arg
    symm
    have H1 : k ∈ ({j} ∪ {d} : Finset ℕ) := by
      have H2 : k ∈ ({j} ∪ {k} : Finset ℕ) := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      rw [h1] at H2
      exact H2
    simp at H1
    rcases H1 with ⟨three, four, rfl⟩
    · simp at h1
      exact h1.symm
    rename_i ih
    exact ih
  rename_i h_jd
  rw [h_jd]
  rw [h_jd] at h1
  right
  rw [mul_left_inj]
  apply congr_arg
  symm
  have H1 : k ∈ ({c} ∪ {d} : Finset ℕ) := by
    have H2 : k ∈ ({d} ∪ {k} : Finset ℕ) := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    rw [h1] at H2
    exact H2
  simp at H1
  rcases H1 with ⟨three, four, rfl⟩
  · rfl
  rename_i ih
  rw [ih, h_jd] at h
  simp at h

theorem FreeMonoid'.parts_eq (h : FreeMonoid'.of a * b = FreeMonoid'.of c * d) : a = c ∧ b = d := by
  apply List.append_inj at h
  simp only [toList_of, List.length_singleton, List.cons.injEq, and_true,
    EmbeddingLike.apply_eq_iff_eq, true_implies] at h
  exact h

--maybe i need rcases?
theorem FreeMonoid'.neq_one {c : FreeMonoid' α} (h : c ≠ 1) : ∃ a b, c = of a * b := by
  induction c using FreeMonoid'.inductionOn'
  · exact (h rfl).elim
  rename_i head tail _
  use head, tail

theorem triplet_eq (h : Nat.dist j k = 1) : BraidMonoidInf_mk (of j * of k * of j) = BraidMonoidInf_mk v' →
    v' = (of j * of k * of j) ∨ v' = (of k * of j * of k) := by
  have H : ∀ t, (t = (FreeMonoid'.of j * FreeMonoid'.of k * FreeMonoid'.of j) ∨ t = of k * of j * of k) →
      rel braid_rels_m_inf t v' → v' = (of j * of k * of j) ∨ v' = (of k * of j * of k) := by
    intro t t_is rel_holds
    revert t_is
    induction (mine4_cg _).mpr rel_holds
    · exact fun t_is => t_is
    · rename_i a b c d br_ab
      intro t_is
      rcases br_ab with i | far
      · have t_is' := t_is
        have cd_length : c.length = 0 ∧ d.length = 0 := by
          rcases t_is with one | two
          · apply congrArg length at one
            simp only [length_mul, length_of, Nat.reduceAdd] at one
            constructor
            · linarith [one]
            linarith [one]
          apply congrArg length at two
          simp only [length_mul, length_of, Nat.reduceAdd] at two
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
        · have H2 := congr_arg length (FreeMonoid'.parts_eq one).2
          simp only [length_mul, length_of, Nat.reduceAdd] at H2
          have b_length_zero : b.length = 0 := by linarith [H2]
          have d_length_zero : d.length = 0 := by linarith [H2]
          have b_is : b = 1 := eq_one_of_length_eq_zero b_length_zero
          have d_is : d = 1 := eq_one_of_length_eq_zero d_length_zero
          rw [b_is, d_is, one_mul, mul_one] at one
          have H3 := (FreeMonoid'.parts_eq one).2
          rw [(FreeMonoid'.parts_eq H3).1, FreeMonoid.of_injective (FreeMonoid'.parts_eq H3).2]
          right
          exact ⟨rfl, rfl⟩
        have H2 := congr_arg length (FreeMonoid'.parts_eq two).2
        simp only [length_mul, length_of, Nat.reduceAdd] at H2
        have b_length_zero : b.length = 0 := by linarith [H2]
        have d_length_zero : d.length = 0 := by linarith [H2]
        have b_is : b = 1 := eq_one_of_length_eq_zero b_length_zero
        have d_is : d = 1 := eq_one_of_length_eq_zero d_length_zero
        rw [b_is, d_is, one_mul, mul_one] at two
        have H3 := (FreeMonoid'.parts_eq two).2
        rw [(FreeMonoid'.parts_eq H3).1, FreeMonoid.of_injective (FreeMonoid'.parts_eq H3).2]
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
    · rename_i a b c d br_ab
      intro t_is
      rcases br_ab with i | far
      · have t_is' := t_is
        have cd_length : c.length = 0 ∧ d.length = 0 := by
          rcases t_is with one | two
          · apply congrArg length at one
            simp only [length_mul, length_of, Nat.reduceAdd] at one
            constructor
            · linarith [one]
            linarith [one]
          apply congrArg length at two
          simp only [length_mul, length_of, Nat.reduceAdd] at two
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
        · have H2 := congr_arg length (FreeMonoid'.parts_eq one).2
          simp only [length_mul, length_of, Nat.reduceAdd] at H2
          have b_length_zero : b.length = 0 := by linarith [H2]
          have d_length_zero : d.length = 0 := by linarith [H2]
          have b_is : b = 1 := eq_one_of_length_eq_zero b_length_zero
          have d_is : d = 1 := eq_one_of_length_eq_zero d_length_zero
          rw [b_is, d_is, one_mul, mul_one] at one
          have H3 := (FreeMonoid'.parts_eq one).2
          rw [(FreeMonoid'.parts_eq H3).1, FreeMonoid.of_injective (FreeMonoid'.parts_eq H3).2]
          left
          exact ⟨rfl, rfl⟩
        have H2 := congr_arg length (FreeMonoid'.parts_eq two).2
        simp only [length_mul, length_of, Nat.reduceAdd] at H2
        have b_length_zero : b.length = 0 := by linarith [H2]
        have d_length_zero : d.length = 0 := by linarith [H2]
        have b_is : b = 1 := eq_one_of_length_eq_zero b_length_zero
        have d_is : d = 1 := eq_one_of_length_eq_zero d_length_zero
        rw [b_is, d_is, one_mul, mul_one] at two
        have H3 := (FreeMonoid'.parts_eq two).2
        rw [(FreeMonoid'.parts_eq H3).1, FreeMonoid.of_injective (FreeMonoid'.parts_eq H3).2]
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
    rename_i g l m n
    exact fun d_is => n ((mine4_cg _).mp l) (m ((mine4_cg _).mp g) d_is)
  exact fun h' => H _ (Or.inl rfl) (PresentedMonoid.exact h')
  -- rcases h
  -- have h1 := h'
  -- apply congrArg braid_length at h'
  -- apply congrArg braid_generators at h1
  -- erw [braid_length_mk, braid_length_mk] at h'
  -- simp at h'
  -- unfold BraidMonoidInf_mk at h1
  -- simp at h1
  -- have h2 := h'.symm
  -- rcases FreeMonoid'.length_eq_three h2 with ⟨a, b, c, h_cases⟩
  -- rw [h_cases] at h1
  -- simp [Finset.union_comm] at h1
  -- sorry

theorem BraidMonoidInf.comm {j k : ℕ} (h : j.dist k >= 2) :
    Con'Gen.Rel braid_rels_m_inf (of j * of k) (of k * of j) := by
  rcases or_dist_iff.mp h
  · apply Con'Gen.Rel.of
    apply braid_rels_m_inf.separated
    assumption
  apply Con'Gen.Rel.symm
  apply Con'Gen.Rel.of
  apply braid_rels_m_inf.separated
  assumption

theorem BraidMonoidInf.braid {j k : ℕ} (h : j.dist k = 1) :
    Con'Gen.Rel braid_rels_m_inf (of j * of k * of j) (of k * of j * of k) := by
  rcases or_dist_iff_eq.mp h
  · apply Con'Gen.Rel.of
    rename_i k_is
    rw [← k_is]
    exact braid_rels_m_inf.adjacent _
  apply Con'Gen.Rel.symm
  apply Con'Gen.Rel.of
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
