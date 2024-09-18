import Mathlib.Data.Nat.Dist
import BraidProject.FreeMonoid_mine
import BraidProject.BraidGroup
import BraidProject.Cancellability
import BraidProject.ListBoolFacts

def in_order (a : List (α × Bool)) := ∀ (i : Fin (a.length -1)),
  (List.get a ⟨i.val, Nat.lt_of_lt_pred i.prop⟩).2 = true ∨
  (List.get a ⟨i.val + 1, Nat.add_lt_of_lt_sub i.prop⟩).2 = false

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
open Braid
-- need some kind of PresentedGroup.mk
theorem braid_rel_holds (h1 : first_rw_closure reversing_rels a b) :
    (QuotientGroup.mk (FreeGroup.mk a) : PresentedGroup braid_rels_inf) =
    QuotientGroup.mk (FreeGroup.mk b) := by
  induction h1 with
  | refl a _ => rfl
  | reg a h1 h2 =>
    rcases h1
    · rename_i e
      rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      rw [mul_left_inj, mul_right_inj]
      apply QuotientGroup.eq'.mpr
      have H1 : (FreeGroup.mk [(e, false), (e, true)])⁻¹ * FreeGroup.mk [] = 1 := by
        show ((FreeGroup.of e)⁻¹ * FreeGroup.of e)⁻¹ * _ = _
        group; rfl
      rw [H1]
      exact Subgroup.one_mem _
    · rename_i c d j
      rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        mul_left_inj, mul_right_inj]
      apply QuotientGroup.eq'.mpr
      apply Subgroup.conjugatesOfSet_subset_normalClosure ; apply Group.mem_conjugatesOfSet_iff.mpr
      use (FreeGroup.of c) * (FreeGroup.of d) * (FreeGroup.of c) * (FreeGroup.of d)⁻¹ *
        (FreeGroup.of c)⁻¹ * (FreeGroup.of d)⁻¹
      constructor
      · sorry
      symm
      apply isConj_iff.mpr
      use FreeGroup.of d
      show FreeGroup.of d * ((FreeGroup.of d)⁻¹ * FreeGroup.of c * FreeGroup.of d * FreeGroup.of c *
        (FreeGroup.of d)⁻¹ * (FreeGroup.of c)⁻¹) * _ = _
      group
    rename_i e g j
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      mul_left_inj, mul_right_inj]
    apply QuotientGroup.eq'.mpr
    show ((FreeGroup.of g)⁻¹ * FreeGroup.of e) * (FreeGroup.of g * (FreeGroup.of e)⁻¹) ∈ _
    apply Subgroup.conjugatesOfSet_subset_normalClosure ; apply Group.mem_conjugatesOfSet_iff.mpr
    use FreeGroup.of e * FreeGroup.of g * (FreeGroup.of e)⁻¹ * (FreeGroup.of g)⁻¹
    constructor
    · sorry
    apply isConj_iff.mpr; use (FreeGroup.of g)⁻¹; group
  | trans _ _ h1 h2 => exact h1.trans h2

theorem grid_to_rev' (h : grid a b c d) : second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c)) := by
  induction h with
  | empty => exact second_rw_closure.refl _
  | top_bottom i => exact second_rw_closure.refl _
  | sides i => exact second_rw_closure.refl _
  | top_left i => exact second_rw_closure.reg (reversing_rels'.inverse _)
  | adjacent i k h => exact second_rw_closure.reg (reversing_rels'.adjacent _ _ h)
  | separated i j h =>
    exact second_rw_closure.reg (reversing_rels'.separated i j (or_dist_iff.mpr h))
  | vertical h1 h2 h1_ih h2_ih =>
    rw [FreeMonoid'.reverse_mul, FreeMonoid'.reverse_mul, map_mul, map_mul, mul_assoc]
    apply (second_rw_closure.left h1_ih).trans
    rw [← mul_assoc, ← mul_assoc]
    exact second_rw_closure.right h2_ih
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [map_mul, map_mul, ← mul_assoc,]
    apply (second_rw_closure.right h1_ih).trans
    rw [mul_assoc, mul_assoc]
    exact second_rw_closure.left h2_ih

theorem rev'_to_grid' {a b c d : FreeMonoid' ℕ} (h : second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c))) : grid a b c d := by
  rcases (existence a b) with ⟨c₁, d₁, hc₁d₁⟩
  have H2 := braid_eq_of_grid hc₁d₁
  sorry

theorem rev'_to_grid {a b c d : FreeMonoid' ℕ} (h : second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c))) : grid a b c d := by
  have H : ∀ e f, second_rw_closure reversing_rels' e f → ∀ a b c d, e = (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
      FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b) → f = (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
      FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c)) → grid a b c d := by
    intro e f hef
    induction hef with
    | refl g =>
      intro a b c d a1 a2
      have H := a1.symm.trans a2
      have H1 : a = 1 ∧ c = 1 ∧ b = d ∨ b = 1 ∧ d = 1 ∧ a = c := by sorry
      rcases H1 with one | two
      · rw [one.1, one.2.1, one.2.2]
        exact grid_top_bottom_word d
      rw [two.1, two.2.1, two.2.2]
      exact grid_sides_word c
    | reg h =>
      rename_i g i
      intro a b c d g_is i_is
      cases h with
      | inverse s =>
        have H : d = 1 ∧ c = 1 ∧ a = b := by
          constructor
          · have H := (FreeMonoid.prod_eq_one i_is.symm).1
            exact FreeMonoid.lift_bool_one H
          constructor
          · have H := (FreeMonoid.prod_eq_one i_is.symm).2
            have H2 : c.reverse = 1 := FreeMonoid.lift_bool_one H
            have H3 := congr_arg FreeMonoid'.reverse H2
            simp only [FreeMonoid'.reverse_reverse, FreeMonoid'.length_one,
              FreeMonoid'.reverse_length, FreeMonoid'.eq_one_of_length_eq_zero] at H3
            exact H3
          sorry
        rw [H.1, H.2.1, H.2.2]
        exact grid_top_left_word b
      | adjacent i j h =>
        have H : a = FreeMonoid.of i ∧ b = FreeMonoid.of j ∧ d = [j, i] ∧ c = [i, j] := by sorry
        rw [H.1, H.2.1, H.2.2.1, H.2.2.2]
        exact grid.adjacent _ _ h
      | separated i j h =>
        have H : a = FreeMonoid.of i ∧ b = FreeMonoid.of j ∧ d = FreeMonoid.of j ∧ c = FreeMonoid.of i := by sorry
        rw [H.1, H.2.1, H.2.2.1, H.2.2.2]
        apply grid.separated
        exact or_dist_iff.mp h
    | left g h =>
      rename_i i j k
      induction k using FreeMonoid'.inductionOn'
      · intro a b c d h1 h2
        rw [one_mul] at h1
        rw [one_mul] at h2
        exact h _ _ _ _ h1 h2
      rename_i kh kt ihk
      intro a1 b1 c1 d1 h1 h2
      rcases a1
      · rcases b1
        · sorry
        sorry
      sorry
    | right _ _ => sorry
    | trans h1 h2 h1_ih h2_ih =>
      rename_i i j k
      intro a1 b1 c1 d1
      intro i_is k_is
      sorry
  exact H _ _ h _ _ _ _ rfl rfl

theorem uniqueness {u v u₁ v₁ : FreeMonoid' ℕ} {a b: FreeMonoid' ℕ}
    (h1 : second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) u *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse v)))
    (h2 : second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) u₁ *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) v₁.reverse)) : u = u₁ ∧ v = v₁ :=
  (unicity (rev'_to_grid h2) _ _ (rev'_to_grid h1)).symm
