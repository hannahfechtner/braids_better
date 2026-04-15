import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.FreeGroup.Basic

namespace FreeMonoid

def pmap {p : α → Prop} (f : (a : α) → p a → β ) (l : FreeMonoid (α)):= List.pmap f (toList l)

theorem prod_eq_one {a b : FreeMonoid α} (h : a * b = 1) : a = 1 ∧ b = 1 := by
  have H : FreeMonoid.length (a * b) = 0 := by
    rw [h, length_one]
  rw [FreeMonoid.length_mul] at H
  constructor
  · have H : length a = 0 := by linarith [h]
    exact length_eq_zero.mp H
  have H : length b = 0 := by linarith [h]
  exact length_eq_zero.mp H

theorem prod_eq_of {a b : FreeMonoid α} {i : α} (h : a * b = FreeMonoid.of i) :
    (a = 1 ∧ b = of i) ∨ (a = of i ∧ b = 1) := by
  have H : FreeMonoid.length (a * b) = 1 := by
    rw [h]
    exact FreeMonoid.length_of _
  rw [FreeMonoid.length_mul] at H
  have H2 : length a = 0 ∨ length b = 0 := by
    revert H
    rcases (length a)
    · exact fun _ => Or.inl rfl
    intro H
    right
    linarith [H]
  rcases H2 with a_one | b_one
  · left
    constructor
    · exact length_eq_zero.mp a_one
    rw [length_eq_zero.mp a_one] at h
    exact h
  right
  constructor
  · rw [length_eq_zero.mp b_one, mul_one] at h
    exact h
  exact length_eq_zero.mp b_one

theorem prod_eq_prod {a b c d : FreeMonoid α} (h : a * b = c * d) :
    (∃ m, c = a * m ∧ b = m * d) ∨ (∃ m, a = c * m ∧ d = m * b) :=
  List.append_eq_append_iff.mp h

@[to_additive (attr := simp)]
theorem reverse_one : reverse (1 : FreeMonoid α) = 1 := by
  apply List.reverse_nil

theorem reverse_eq_one : reverse a = 1 ↔ a = 1 := by
  constructor
  · intro h
    rw [← reverse_one, ← h]
    exact reverse_reverse.symm
  intro h
  rw [h, reverse_one]

theorem mem_one_iff : a ∈ (1 : FreeMonoid α) ↔ False := List.mem_nil_iff _

theorem mem_reverse : a ∈ reverse b ↔ a ∈ b := List.mem_reverse

-- though this one is quickly done!
theorem bounded (u : FreeMonoid ℕ) : ∃ k, ∀ x ∈ u, x < k := by
  induction u using FreeMonoid.inductionOn'
  · use 1
    exact fun _ h => (notMem_one h).elim
  rename_i head tail tail_ih
  rcases tail_ih with ⟨old_k, kh⟩
  use Nat.max old_k (head+1)
  intro x x_in
  rcases x_in
  · exact lt_max_of_lt_right Nat.le.refl
  next x_in_tail =>
  exact lt_max_iff.mpr (Or.inl (kh x x_in_tail))

theorem lift_comp {M N : Type*} [Monoid M] [Monoid N] (h : α → M) (g : M →* N) :
    FreeMonoid.lift (g ∘ h) = g.comp (FreeMonoid.lift h) :=
  FreeMonoid.hom_eq_iff.mpr (congrFun rfl)

theorem lift_comp_apply {M N : Type*} [Monoid M] [Monoid N] (h : α → M) (g : M →* N) (a) :
    FreeMonoid.lift (g ∘ h) a = g ((FreeMonoid.lift h) a) := by
  simp [lift_comp h g]

theorem reconstruct_from_projection {L : FreeMonoid (α × β)} {b : β} (h : ∀ x ∈ L, x.2 = b) :
    FreeMonoid.map (fun x ↦ (x, b)) (FreeMonoid.map (fun x ↦ x.1) L) = L := by
  induction L with
  | one => rfl
  | of x => aesop
  | mul x y _ _ => aesop

-- and where do these go
theorem lift_eq_FreeGroup_lift_comp_of {G₁ : Type} [Group G₁] (f : α → G₁) :
    FreeMonoid.lift f = (FreeGroup.lift f).comp (FreeMonoid.lift FreeGroup.of) := by
  rw [← (FreeMonoid.lift_comp FreeGroup.of (FreeGroup.lift f))]
  aesop

theorem lift_eq_FreeGroup_lift_comp_of_apply {G₁ : Type} [Group G₁] (f : α → G₁) (a : FreeMonoid α) :
    FreeMonoid.lift f a = (FreeGroup.lift f) (FreeMonoid.lift FreeGroup.of a) := by
  simpa using congrArg (fun φ : FreeMonoid α →* G₁ => φ a)
    (FreeMonoid.lift_eq_FreeGroup_lift_comp_of (f := f))

/-- if two types are isomorphic, the free monoids over those types are isomorphic -/
@[to_additive /--if two types are isomorphic, the additive free monoids over those types are
isomorphic-/]
def congr_iso {α : Type u_1} {β : Type u_2} (e : α ≃ β) : FreeMonoid α ≃* FreeMonoid β := by
  apply MulEquiv.mk' ⟨FreeMonoid.map e.toFun, FreeMonoid.map e.invFun, _, _⟩
  · simp
  all_goals
  intro x
  simp

/-- given an isomorphism between α and β, convert a relation predicate to
have an underlying type of β -/
@[to_additive /-- given an isomorphism between α and β, convert a relation predicate to
have an underlying type of β -/]
def map_rel (e : α ≃ β) (rel : FreeMonoid α → FreeMonoid α → Prop) :
    FreeMonoid β → FreeMonoid β  → Prop :=
  fun a b ↦ rel (congr_iso e.symm a) (congr_iso e.symm b)

/-- given an isomorphism between α and β, pull back a relation predicate with underlying type β to
one with underlying type α -/
@[to_additive /-- given an isomorphism between α and β, pull back a relation predicate with
underlying type β to one with underlying type α -/]
def comap_rel (e : α ≃ β) (rel : FreeMonoid β → FreeMonoid β → Prop) :
    FreeMonoid α → FreeMonoid α → Prop :=
  fun a b ↦ rel (congr_iso e a) (congr_iso e b)

theorem eq_one_or_has_last_elem (a : FreeMonoid α) : a = 1 ∨ ∃ front last, a = front * of last := by
  induction a using FreeMonoid.inductionOn' with
  | one => left; rfl
  | mul_of b a ih =>
    right
    cases ih with
    | inl h => use 1, b; rw [h, one_mul, mul_one]
    | inr h =>
      rcases h with ⟨front, last, hfl⟩
      rw [hfl]
      use of b * front, last
      rw [mul_assoc]

theorem exists_last_elem_of_length_eq_succ (length : length b = Nat.succ n) :
    ∃ b_front b_last, b = b_front  *  .of b_last := by
  rcases eq_one_or_has_last_elem b
  · rename_i b_is_one
    rw [b_is_one, length_one] at length
    exact (Nat.succ_ne_zero n length.symm).elim
  assumption

theorem parts_eq (h : FreeMonoid.of a * b = FreeMonoid.of c * d) : a = c ∧ b = d := by
  apply List.append_inj at h
  simp only [toList_of, List.length_singleton, List.cons.injEq, and_true,
    EmbeddingLike.apply_eq_iff_eq, true_implies] at h
  exact h

theorem neq_one {c : FreeMonoid α} (h : c ≠ 1) : ∃ a b, c = FreeMonoid.of a * b := by
  induction c using FreeMonoid.inductionOn'
  · exact (h rfl).elim
  rename_i head tail _
  use head, tail

end FreeMonoid
