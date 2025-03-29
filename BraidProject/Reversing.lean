import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.FreeMonoid.Basic
--import BraidProject.BraidGroup
import BraidProject.Cancellability
import BraidProject.BraidGroup
import BraidProject.TrueFalse
import BraidProject.SemiThue

def in_order' (a : List (α × Bool)) := ∀ (i : Fin (a.length -1)),
  (List.get a ⟨i.val, Nat.lt_of_lt_pred i.2⟩).2 = true ∨
  (List.get a ⟨i.val + 1, Nat.add_lt_of_lt_sub i.2⟩).2 = false

def part_split (a : FreeMonoid (α × Bool)) : FreeMonoid (α × Bool) × (Option ((α × Bool) × (α × Bool))) × FreeMonoid (α × Bool) :=
  match a with
  | [] => (1, none, 1)
  | (b, true) :: c => (FreeMonoid.of (b, true) * (part_split c).1, (part_split c).2.1, (part_split c).2.2)
  | (b, false) :: c =>
    match c with
    | [] => (FreeMonoid.of (b, false), none, 1)
    | (d, true) :: e => (1, some ((b, false), (d, true)), e)
    | (_, false) :: _ => (FreeMonoid.of (b, false) * (part_split c).1, (part_split c).2.1, (part_split c).2.2)

#eval part_split ([(3, false), (2, false), (2, false), (4, true),(5, true)] : List (ℕ × Bool))
#eval part_split [(3, false), (2, false), (1, true)]
#eval part_split [(2, true), (4, true), (5, false)]

inductive reversing_rels : List (α × Bool) → List (α × Bool) → Prop
  | inverse (a : ℕ) : reversing_rels [(a, false), (a, true)] []
  | adjacent (i j : ℕ) (h : i.dist j = 1) : reversing_rels [(i, false), (j, true)]
      [(j, true), (i, true), (j, false), (i, false)]
  | separated (i j : ℕ) (h : i.dist j >= 2): reversing_rels [(i, false), (j, true)]
      [(j, true), (i, false)]

-- def reverse : List (α × Bool) → List (α × Bool) :=
--   fun a => match (part_split a) with
--   | (first, none, last) => first * last
--   | (first, some (c, d), last) => reverse (first * last)

inductive reversing_rels' : FreeMonoid (α × Bool) → FreeMonoid (α × Bool) → Prop
  | inverse (a : ℕ) : reversing_rels' (FreeMonoid.of (a, false) * FreeMonoid.of (a, true)) 1
  | adjacent (i j : ℕ) (h : i.dist j = 1) : reversing_rels' [(i, false), (j, true)]
      [(j, true), (i, true), (j, false), (i, false)]
  | separated (i j : ℕ) (h : i.dist j >= 2): reversing_rels' [(i, false), (j, true)]
      [(j, true), (i, false)]

inductive first_rw_closure (rels : List (α × Bool) → List (α × Bool) → Prop) :
    List (α × Bool) → List (α × Bool) → Prop
  | refl (a : List (α × Bool)) : in_order a → first_rw_closure rels a a
  | reg (a : List (α × Bool)) : rels b c → in_order a →
      first_rw_closure rels (a ++ b ++ d) (a ++ c ++ d)
  | trans : first_rw_closure rels a b → first_rw_closure rels b c → first_rw_closure rels a c

inductive second_rw_closure (rels : FreeMonoid (α × Bool) → FreeMonoid (α × Bool) → Prop) :
    FreeMonoid (α × Bool) → FreeMonoid (α × Bool) → Prop
  | refl (a : FreeMonoid (α × Bool)) : second_rw_closure rels a a
  | reg : rels b c → second_rw_closure rels b c
  | left : second_rw_closure rels a b → second_rw_closure rels (c * a) (c * b)
  | right : second_rw_closure rels a b → second_rw_closure rels (a * d) (b * d)
  | trans : second_rw_closure rels a b → second_rw_closure rels b c → second_rw_closure rels a c


-- theorem uniqueness (a : List (α × Bool)) (h1 : first_rw_closure reversing_rels a b)
--     (h2 : first_rw_closure reversing_rels a c) (hc : in_order c) (hb : in_order b) : b = c := by
--   induction h1 with
--   | refl c hc =>
--     induction h2 with
--     | refl d hd => rfl
--     | reg a _ _ => sorry
--     | trans _ _ _ _ => sorry
--   | reg a _ _ => sorry
--   | trans _ _ _ _ => sorry
--open Braid
-- need some kind of PresentedGroup.mk
-- theorem braid_rel_holds (h1 : first_rw_closure reversing_rels a b) :
--     (QuotientGroup.mk (FreeGroup.mk a) : PresentedGroup braid_rels_coexeter) =
--     QuotientGroup.mk (FreeGroup.mk b) := by
--   induction h1 with
--   | refl a _ => rfl
--   | reg a h1 h2 =>
--     rcases h1
--     · rename_i e
--       rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
--       rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
--       rw [mul_left_inj, mul_right_inj]
--       apply QuotientGroup.eq'.mpr
--       have H1 : (FreeGroup.mk [(e, false), (e, true)])⁻¹ * FreeGroup.mk [] = 1 := by
--         show ((FreeGroup.of e)⁻¹ * FreeGroup.of e)⁻¹ * _ = _
--         group; rfl
--       rw [H1]
--       exact Subgroup.one_mem _
--     · rename_i c d j
--       rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
--         QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
--         mul_left_inj, mul_right_inj]
--       apply QuotientGroup.eq'.mpr
--       apply Subgroup.conjugatesOfSet_subset_normalClosure ; apply Group.mem_conjugatesOfSet_iff.mpr
--       use (FreeGroup.of c) * (FreeGroup.of d) * (FreeGroup.of c) * (FreeGroup.of d)⁻¹ *
--         (FreeGroup.of c)⁻¹ * (FreeGroup.of d)⁻¹
--       constructor
--       · sorry
--       symm
--       apply isConj_iff.mpr
--       use FreeGroup.of d
--       show FreeGroup.of d * ((FreeGroup.of d)⁻¹ * FreeGroup.of c * FreeGroup.of d * FreeGroup.of c *
--         (FreeGroup.of d)⁻¹ * (FreeGroup.of c)⁻¹) * _ = _
--       group
--     rename_i e g j
--     rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
--       QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
--       mul_left_inj, mul_right_inj]
--     rcases or_dist_iff.mp j
--     · apply QuotientGroup.eq'.mpr
--       show ((FreeGroup.of g)⁻¹ * FreeGroup.of e) * (FreeGroup.of g * (FreeGroup.of e)⁻¹) ∈ _
--       apply Subgroup.conjugatesOfSet_subset_normalClosure ; apply Group.mem_conjugatesOfSet_iff.mpr
--       use FreeGroup.of e * FreeGroup.of g * (FreeGroup.of e)⁻¹ * (FreeGroup.of g)⁻¹
--       constructor
--       · apply separated
--         assumption
--       apply isConj_iff.mpr; use (FreeGroup.of g)⁻¹; group
--     symm
--     apply QuotientGroup.eq'.mpr
--     apply Subgroup.conjugatesOfSet_subset_normalClosure ; apply Group.mem_conjugatesOfSet_iff.mpr
--     use FreeGroup.of g * FreeGroup.of e * (FreeGroup.of g)⁻¹ * (FreeGroup.of e)⁻¹
--     constructor
--     · apply separated
--       assumption
--     apply isConj_iff.mpr; use (FreeGroup.of g)⁻¹; group
--     rfl
--   | trans _ _ h1 h2 => exact h1.trans h2

theorem grid_to_rev' (h : grid a b c d) : second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid.reverse c)) := by
  induction h with
  | empty => exact second_rw_closure.refl _
  | top_bottom i => exact second_rw_closure.refl _
  | sides i => exact second_rw_closure.refl _
  | top_left i => exact second_rw_closure.reg (reversing_rels'.inverse _)
  | adjacent i k h => exact second_rw_closure.reg (reversing_rels'.adjacent _ _ h)
  | separated i j h =>
    exact second_rw_closure.reg (reversing_rels'.separated i j h)
  | vertical h1 h2 h1_ih h2_ih =>
    rw [FreeMonoid.reverse_mul, FreeMonoid.reverse_mul, map_mul, map_mul, mul_assoc]
    apply (second_rw_closure.left h1_ih).trans
    rw [← mul_assoc, ← mul_assoc]
    exact second_rw_closure.right h2_ih
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [map_mul, map_mul, ← mul_assoc,]
    apply (second_rw_closure.right h1_ih).trans
    rw [mul_assoc, mul_assoc]
    exact second_rw_closure.left h2_ih



theorem rev'_to_grid {a b c d : List ℕ} (h : SemiThue reversing_rels'
    (to_up a ++ to_over b) (to_over d ++ to_up c)) : grid a b c d := by sorry

theorem uniqueness {u v u₁ v₁ : FreeMonoid ℕ} {a b: FreeMonoid ℕ}
    (h1 : SemiThue reversing_rels' (to_up a ++ to_over b) (to_over v ++ to_up u))
    (h2 : SemiThue reversing_rels' (to_up a ++ to_over b) (to_over v₁ ++ to_up u₁))
    : u = u₁ ∧ v = v₁ :=
  (unicity (rev'_to_grid h2) _ _ (rev'_to_grid h1))
