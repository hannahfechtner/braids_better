import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Maps
import Mathlib.Data.Fin.Basic
import BraidProject.BraidMonoid

--set_option autoImplicit false
namespace Braid

variable (M : α → α → ℕ)

def artin_tits (a b : α) (k : ℕ) :=
  match k with
  | 0 => 1
  | Nat.succ n => FreeGroup.of a * artin_tits b a n

def rel : α → α → FreeGroup (α) := fun i j => artin_tits i j (M i j) * (artin_tits j i (M i j))⁻¹

@[simp]
theorem artin_tits_one (a b : α) : artin_tits a b 1 = .of a := rfl

@[simp]
theorem artin_tits_two (a b : α) : artin_tits a b 2 = .of a * .of b := rfl

@[simp]
theorem artin_tits_three (a b : α) : artin_tits a b 3 = .of a * .of b * .of a := rfl

def M_braid (i j : ℕ) : ℕ :=
  match j-i with
  | 0 => 1
  | Nat.succ n =>
    match n with
    | 0 => 3
    | Nat.succ _ => 2

def M_braid_fin (i j : Fin n) : ℕ := if n = 0 ∨ n = 1 then 1 else M_braid i.val j.val

theorem succ_succ_of_ge_plus_two (h : i + 2 ≤ j) : ∃ n, j - i = Nat.succ (Nat.succ (n)) := by
  have H : i + 2 - i ≤ j - i := Nat.sub_le_sub_right h i
  simp only [add_tsub_cancel_left] at H
  rcases @Nat.exists_eq_succ_of_ne_zero (j - i - 1) (Nat.sub_ne_zero_iff_lt.mpr H) with ⟨w, hw⟩
  use w
  rw [← hw]
  exact (Nat.sub_add_cancel (Nat.one_le_of_lt H)).symm

theorem M_braid_apart {i j : ℕ} (h : i + 2 ≤ j) : M_braid i j = 2 := by
  unfold M_braid
  rcases succ_succ_of_ge_plus_two h with ⟨w, hw⟩
  rw [hw]

theorem M_braid_fin_apart (i j : Fin n) (h : i ≤ j) :
    M_braid_fin i.castSucc.castSucc j.succ.succ = 2 := by
  induction n
  · exact (Nat.not_succ_le_zero (↑i) i.2).elim
  unfold M_braid_fin
  exact M_braid_apart <| Nat.add_le_of_le_sub (tsub_add_cancel_iff_le.mp rfl) h

theorem M_braid_close {i : ℕ} : M_braid i (i + 1) = 3 := by
  unfold M_braid
  simp only [add_tsub_cancel_left]

theorem M_braid_fin_close (i : Fin n) : M_braid_fin i.castSucc i.succ = 3 := by
  induction n
  · exact (Nat.not_succ_le_zero (↑i) i.2).elim
  unfold M_braid_fin
  simp only [add_eq_zero, one_ne_zero, and_false, and_self, add_left_eq_self, or_self, ↓reduceIte,
    Fin.coe_castSucc, Fin.val_succ]
  exact M_braid_close

theorem foo (a b : Fin n) (h : a + b < n) : (a+b).val = a.val + b.val := by
  rw [Fin.val_add_eq_ite]
  simp only [ite_eq_right_iff, isEmpty_Prop, not_le, h, IsEmpty.forall_iff]

def braid_rels_coexeter : Set (FreeGroup ℕ) := Set.range (Function.uncurry (rel M_braid))

def braid_rels_fin_coexeter (n : ℕ): Set (FreeGroup (Fin n)) := Set.range (Function.uncurry (rel M_braid_fin))
/-
The predecessor in the next definition is annoying, but hopefully not too bad.
Most of the time we will write `braid_group (n + 1)`, which corresponds to `B_{n + 1}`.
-/

def braid_group (n : ℕ) := PresentedGroup (braid_rels_fin_coexeter n.pred)

def braid_group_inf := PresentedGroup braid_rels_coexeter

instance (n : ℕ) : Group (braid_group n) := by
  unfold braid_group; infer_instance

instance : Group braid_group_inf := by
  unfold braid_group_inf; infer_instance

def braid_group.rel := PresentedGroup braid_rels_coexeter

def σ {n : ℕ} (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k

def σi (k : ℕ) : braid_group_inf := PresentedGroup.of k


/-
This version makes n explicit. Note that `σ' n k` is an element of
`braid group (n + 1).`
-/
abbrev σ' (n : ℕ) (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k

  -- symm; rw [←mul_inv_eq_one]
  -- apply QuotientGroup.eq.mpr
  -- apply Subgroup.subset_normalClosure
  -- simp only [Nat.succ_eq_add_one, Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.coe_castSucc,
  --   mul_inv_rev, inv_inv, mul_one]
  -- left; use i
  -- simp [braid_rels, braid_rel, mul_assoc]
  -- sorry

theorem braid_group.braid (i : Fin n) :
    σ i.castSucc * σ i.succ * σ i.castSucc = σ i.succ * σ i.castSucc * σ i.succ := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i.castSucc, i.succ)
  rw [Function.uncurry_apply_pair, Braid.rel, M_braid_fin_close i]
  simp only [Nat.pred_succ, artin_tits_three, mul_inv_rev, Nat.succ_eq_add_one, inv_inv, mul_one]

theorem braid_group_inf.braid (i : ℕ) :
    σi i * σi i.succ * σi i = σi i.succ * σi i * σi i.succ := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, i + 1)
  simp only [Function.uncurry_apply_pair, rel, M_braid_close, artin_tits_three, mul_inv_rev,
    Nat.succ_eq_add_one, inv_inv, mul_one]

theorem braid_group.comm {i j : Fin n} (h : i ≤ j) :
    σ i.castSucc.castSucc * σ j.succ.succ = σ j.succ.succ * σ i.castSucc.castSucc := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i.castSucc.castSucc, j.succ.succ)
  rw [Function.uncurry_apply_pair, Braid.rel, M_braid_fin_apart i j h]
  simp only [artin_tits_two, mul_inv_rev, inv_inv, mul_one]

theorem separated (h :e + 2 ≤ g) : FreeGroup.of e * .of g * (.of e)⁻¹ * (.of g)⁻¹ ∈ braid_rels_coexeter := by
  unfold braid_rels_coexeter
  refine Set.mem_range.mpr ?_
  use (e, g)
  simp
  rw [rel, M_braid_apart h]
  simp
  rfl


theorem braid_group_inf.comm {i j : ℕ} (h : i + 2 ≤ j) :
    σi i * σi j = σi j * σi i := by
  symm
  rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  apply Set.mem_range.mpr
  use (i, j)
  simp only [Function.uncurry_apply_pair, rel, M_braid_apart h, artin_tits_two, mul_inv_rev,
    inv_inv, mul_one]

theorem generated_by (H : Subgroup braid_group_inf) (h : ∀ i : ℕ, σi i ∈ H) :
    ∀ x : braid_group_inf, x ∈ H := by
  intro x
  apply QuotientGroup.induction_on
  intro z
  change ⟦z⟧ ∈ H
  apply FreeGroup.induction_on (C := fun z => ⟦z⟧ ∈ H) _ (one_mem H)
  . exact fun i => h i
  . intro i h
    apply (Subgroup.inv_mem_iff H).mp
    exact h
  intro i j h1 h2
  change QuotientGroup.mk _ ∈ H.carrier
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ h1 h2

  theorem generated_by_fin (H : Subgroup (braid_group (n + 1))) (h : ∀ i : Fin n, σ i ∈ H) :
    ∀ x : braid_group (n + 1), x ∈ H := by
  intro x
  apply QuotientGroup.induction_on
  intro z
  change ⟦z⟧ ∈ H
  apply FreeGroup.induction_on (C := fun z => ⟦z⟧ ∈ H) _ (one_mem H)
  . exact fun i => h i
  . intro i h
    apply (Subgroup.inv_mem_iff H).mp
    exact h
  intro i j h1 h2
  change QuotientGroup.mk _ ∈ H.carrier
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ h1 h2


-- theorem generated_by (n : ℕ) (H : Subgroup (braid_group n)) (h : ∀ i : Fin n, σ' n i ∈ H) :
--     ∀ x : braid_group (n + 1), x ∈ H := by
--   intro x
--   apply QuotientGroup.induction_on
--   intro z
--   change ⟦z⟧ ∈ H
--   apply FreeGroup.induction_on (C := fun z => ⟦z⟧ ∈ H) _ (one_mem H)
--   . intro i
--     specialize h i
--   . intro i j h1 h2
--     change QuotientGroup.mk _ ∈ H.carrier
--     rw [QuotientGroup.mk_mul]
--     exact Subgroup.mul_mem _ h1 h2

-- theorem braid_group_2.is_cyclic : ∃ g : (braid_group 2), ∀ x, x ∈ Subgroup.zpowers g := by
--   use (σ 0)
--   intro x
--   apply generated_by
--   intro i
--   rw [Subgroup.mem_zpowers_iff]
--   have h : i=0 := by
--     apply Fin.eq_of_val_eq
--     simp
--   use 1
--   rw [h]
--   rfl

-- theorem embed_helper (n : ℕ) : ∀ (a b : FreeMonoid' (Fin (n.pred))),
--     (braid_rels_m (n.pred)) a b → ((FreeMonoid'.lift fun a => σ a) a : braid_group n)=
--     (FreeMonoid'.lift fun a => σ a) b := by
--   repeat
--     rcases n
--     · intro _ _ h
--       exfalso
--       apply h
--     rename_i n
--   intro a b h
--   rcases h
--   · rename_i j
--     simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
--     sorry --apply braid_group.braid
--   simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
--   apply braid_group.comm
--   next ih => exact ih

-- def embed {n : ℕ} : (BraidMonoid n) →* (braid_group (n)) :=
--   PresentedMonoid.toMonoid (fun a => @σ (n.pred) a) (embed_helper n)

theorem embed_inf_helper : ∀ (a b : FreeMonoid' ℕ),
    (braid_rels_m_inf a b → ((FreeMonoid'.lift fun a => σi a) a : braid_group_inf)=
    (FreeMonoid'.lift fun a => σi a) b) := by
  intro a b h
  rcases h
  · rename_i j
    simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
    apply braid_group_inf.braid
  simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
  apply braid_group_inf.comm
  next ih => exact ih

def embed_inf : BraidMonoidInf →* braid_group_inf :=
  PresentedMonoid.toMonoid (fun a => σi a) embed_inf_helper

/-
We need a theorem that says that we can define a function from the braid group by giving any
function on the generators that satisfies the relations.

This should just be a nicer repackaging of `PresentedGroup.toGroup`.
-/
