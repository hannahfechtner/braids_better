import Mathlib.Algebra.PresentedMonoid.Basic
import BraidProject.Additions.FreeMonoid
import Mathlib.GroupTheory.Congruence.Basic
import BraidProject.Additions.Congruence

namespace PresentedMonoid

section Basic

variable (rels : FreeMonoid α → FreeMonoid α → Prop)

open Set Submonoid

@[to_additive (attr := simp)]
theorem mk_mul (a b : FreeMonoid α) : mk rels (a * b) = mk rels a * (mk rels b) := rfl

@[to_additive (attr := simp)]
theorem one_def : mk rels 1 = (1 : PresentedMonoid rels) := rfl

instance : MonoidHom (FreeMonoid α) (PresentedMonoid rels) where
  toFun := mk rels
  map_mul' := fun _ _ => rfl
  map_one' := rfl

end Basic

section inductionOn

variable {α : Type*}

def rel (rels : FreeMonoid α → FreeMonoid α → Prop) := ConGen.Rel rels

variable {rels : FreeMonoid α → FreeMonoid α → Prop}

theorem mkfreeMonoid_lift_presentedMonoid_of : (FreeMonoid.lift (PresentedMonoid.of rels)) a =
    PresentedMonoid.mk rels a := by
  induction a using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of b a ih =>
    simp [ih]
    rfl

theorem freeMonoid_lift_eq_of_rel {G₁ : Type} [Group G₁] (f : α → G₁)
    (h : ∀ r₁ r₂, rels r₁ r₂ → (FreeMonoid.lift f r₁ = FreeMonoid.lift f r₂))
    (a b : FreeMonoid α) (hr : PresentedMonoid.rel rels a b) :
    (FreeMonoid.lift f) a = (FreeMonoid.lift f) b :=
  ConGen.Rel.rec (fun x y rxy ↦ h x y rxy) (fun _ ↦ rfl) (fun _ ryx ↦ ryx.symm)
  (fun _ _ rab rbc ↦ rab.trans rbc) (fun  _ _ ih1 ih2 ↦ by rw [map_mul, map_mul, ih1, ih2]) hr

theorem freeMonoid_lift_of_eq_mk_of_mulHom {β : Type} [Monoid β] (r : FreeMonoid α)
    (f : PresentedMonoid rels →* β) :
    (FreeMonoid.lift fun x => f (PresentedMonoid.of rels x)) r =
    (f (PresentedMonoid.mk rels r)) := by
  induction r using FreeMonoid.inductionOn' with
  | one => exact f.map_one.symm
  | mul_of b a ih =>
    rw [map_mul, ih, FreeMonoid.lift_eval_of, mk_mul, map_mul]
    rfl

theorem refl : PresentedMonoid.rel rels a a := ConGen.Rel.refl _
theorem one_step_reduction : ∀ c d, rels a b → PresentedMonoid.rel rels (c * a * d) (c * b * d) :=
  fun _ _ h => ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _) (ConGen.Rel.of _ _ h))
        (ConGen.Rel.refl _)
theorem one_step_reduction_symm : ∀ c d, rels a b →
    PresentedMonoid.rel rels (c * b * d) (c * a * d) :=
  fun _ _ h => ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _)
        (ConGen.Rel.symm (ConGen.Rel.of _ _ h))) (ConGen.Rel.refl _)
theorem trans : PresentedMonoid.rel rels a b → PresentedMonoid.rel rels b c →
  PresentedMonoid.rel rels a c := fun h1 h2 => h1.trans h2
theorem mul : PresentedMonoid.rel rels a b → PresentedMonoid.rel rels c d →
  PresentedMonoid.rel rels (a * c) (b * d) := fun h1 h2 => ConGen.Rel.mul h1 h2
theorem mul_rels_left : rels a b → PresentedMonoid.rel rels c d →
  PresentedMonoid.rel rels (a * c) (b * d) := fun h1 h2 => ConGen.Rel.mul (ConGen.Rel.of _ _ h1) h2
theorem mul_rels_right : PresentedMonoid.rel rels a b → rels c d →
  PresentedMonoid.rel rels (a * c) (b * d) := fun h1 h2 => ConGen.Rel.mul h1 (ConGen.Rel.of _ _ h2)
theorem append_left : PresentedMonoid.rel rels c d →
  PresentedMonoid.rel rels (a * c) (a * d) := fun h => ConGen.Rel.mul refl h
theorem append_right : PresentedMonoid.rel rels a b →
  PresentedMonoid.rel rels (a * c) (b * c) := fun h => ConGen.Rel.mul h refl
theorem rels_left : rels c d → PresentedMonoid.rel rels (a * c) (a * d) :=
  fun h => ConGen.Rel.mul refl (ConGen.Rel.of _ _ h)
theorem rels_right : rels a b → PresentedMonoid.rel rels (a * c) (b * c) :=
  fun h => ConGen.Rel.mul (ConGen.Rel.of _ _ h) refl
theorem rels_alone : rels a b → PresentedMonoid.rel rels a b :=
  fun h => ConGen.Rel.of _ _ h
theorem symm_alone : rels a b → PresentedMonoid.rel rels b a :=
  fun h => ConGen.Rel.symm (ConGen.Rel.of _ _ h)
theorem symm : PresentedMonoid.rel rels a b → PresentedMonoid.rel rels b a :=
  fun h => ConGen.Rel.symm h

private inductive rw_system (rels : FreeMonoid α → FreeMonoid α → Prop) : FreeMonoid α → FreeMonoid α → Prop
  | refl : rw_system rels a a
  | reg : ∀ c d, rels a b → rw_system rels (c * a * d) (c * b * d)
  | symm : ∀ c d, rels a b → rw_system rels (c * b * d) (c * a * d)
  | trans : rw_system rels a b → rw_system rels b c → rw_system rels a c

private theorem rw_system_symm : rw_system rels a b → rw_system rels b a := by
  intro h
  induction h with
  | refl => exact rw_system.refl
  | reg c d h => exact rw_system.symm _ _ h
  | symm c d h => exact rw_system.reg _ _ h
  | trans _ _ h3 h4 => exact h4.trans h3

private theorem mul_front : rw_system rels a b → rw_system rels (a * c) (b * c) := by
  intro h
  induction h with
  | refl => exact PresentedMonoid.rw_system.refl
  | reg c d h =>
    rename_i e f g
    rw [mul_assoc _ d e, mul_assoc _ d e]
    exact PresentedMonoid.rw_system.reg _ _ h
  | symm c d h =>
    rename_i e f g
    rw [mul_assoc _ d e, mul_assoc _ d e]
    exact PresentedMonoid.rw_system.symm _ _ h
  | trans _ _ ha hb => exact ha.trans hb

private theorem mul_back : rw_system rels a b → rw_system rels (c * a) (c * b) := by
  intro h
  induction h with
  | refl => exact PresentedMonoid.rw_system.refl
  | reg c d h =>
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    exact rw_system.reg _ _ h
  | symm c d h =>
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    exact rw_system.symm _ _ h
  | trans _ _ ha hb => exact ha.trans hb

private theorem rw_system_mul : rw_system rels a b → rw_system rels c d → rw_system rels (a * c) (b * d) := by
  intro h1 h2
  induction h1 with
  | refl => exact mul_back h2
  | reg c d h =>
    induction h2 with
    | refl => exact mul_front <| rw_system.reg _ _ h
    | reg c d h1 =>
      exact (mul_front (rw_system.reg _ _ h)).trans (mul_back (rw_system.reg _ _ h1))
    | symm c d h1 =>
      exact (mul_front (rw_system.reg _ _ h)).trans (mul_back (rw_system.symm _ _ h1))
    | trans _ _ h3 h4 =>
      rename_i g i k l m _ _
      apply h3.trans
      have step : rw_system rels (c * i * d * l) (c * g * d * l) := by
        rw [mul_assoc _ d, mul_assoc _ d]
        exact rw_system.symm _ _ h
      apply step.trans h4
  | symm c d h =>
    rename_i g i
    induction h2 with
    | refl =>
      apply mul_front
      apply rw_system.symm _ _ h
    | reg c d h1 =>
      exact (mul_front (rw_system.symm _ _ h)).trans (mul_back (rw_system.reg _ _ h1))
    | symm c d h1 =>
      exact (mul_front (rw_system.symm _ _ h)).trans (mul_back (rw_system.symm _ _ h1))
    | trans _ _ hc hd =>
      rename_i j k l m _ _
      apply hc.trans
      have step : PresentedMonoid.rw_system rels (c * g * d * l) (c * i * d * l) := by
        rw [mul_assoc _ d, mul_assoc _ d]
        exact rw_system.reg _ _ h
      exact step.trans hd
  | trans _ hb hc _ => exact hc.trans (mul_front hb)

private theorem rw_system_rel_iff (rels : FreeMonoid α → FreeMonoid α → Prop) :
    rw_system rels a b ↔ rel rels a b := by
  constructor
  · intro h
    induction h with
    | refl => exact refl
    | reg c d h => exact one_step_reduction _ _ h
    | symm c d h => exact one_step_reduction_symm _ _ h
    | trans _ _ h1 h2 => exact h1.trans h2
  intro h
  induction h with
  | of x y h =>
    rw [← mul_one x, ← mul_one y, ← one_mul x, ← one_mul y]
    exact rw_system.reg _ _ h
  | refl _ => exact rw_system.refl
  | symm _ h => exact rw_system_symm h
  | trans _ _ h1 h2 => exact h1.trans h2
  | mul _ _ h1 h2 => exact rw_system_mul h1 h2

theorem rel_induction_rw {P : FreeMonoid α → FreeMonoid α → Prop} {a b : FreeMonoid α}
    (h : rel rels a b)
    (h1 : ∀ (a : FreeMonoid α), P a a)
    (h2 : ∀ a b {c d}, rels a b → P (c * a * d) (c * b * d))
    (h3 : ∀ a b {c d}, rels b a → P (c * a * d) (c * b * d))
    (h4 : ∀ a b c, P a b ∧ P b c → P a c)
  : P a b := by
  induction ((rw_system_rel_iff _).mpr h) with
  | refl => exact h1 _
  | reg _ _ ih => exact h2 _ _ ih
  | symm _ _ ih => exact h3 _ _ ih
  | trans ha hb h1 h2 =>
    exact h4 _ _ _ ⟨h1 ((rw_system_rel_iff _).mp ha), h2 ((rw_system_rel_iff _).mp hb)⟩

protected theorem sound (h : rel rels a b) : mk rels a = mk rels b :=
  Quotient.sound h

theorem exact {rels : FreeMonoid α → FreeMonoid α → Prop}
    (h : PresentedMonoid.mk rels a = PresentedMonoid.mk rels b) : PresentedMonoid.rel rels a b :=
  Quotient.exact h

def lift_of_mul {β : Type} (f : FreeMonoid α → β) (hm : ∀ {a b c d}, f a = f c →
    f b = f d → f (a * b) = f (c * d))
    (h : ∀ (a b : FreeMonoid α), rels a b → f a = f b) : PresentedMonoid rels → β :=
  fun c => Con.liftOn c f (fun _ _ cg => by
    induction cg with
    | of x y ih => exact h _ _ ih
    | refl x => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
    | mul _ _ ih1 ih2 => exact hm ih1 ih2 )

@[simp]
theorem lift_of_mul_mk {β : Type} (x : FreeMonoid α) (f : FreeMonoid α → β)
    (hm : ∀ {a b c d}, f a = f c → f b = f d → f (a * b) = f (c * d))
    (h : ∀ (a b : FreeMonoid α), rels a b → f a = f b) :
    lift_of_mul f hm h (PresentedMonoid.mk rels x) = f x := rfl

section Isomorphism
variable {β : Type*} (e : α ≃ β) (rels : FreeMonoid α → FreeMonoid α → Prop)

/-- presented monoids over isomorphic types (with the relations converted appropriately)
are isomorpic -/
@[to_additive /-- presented additive monoids over isomorphic types (with the relations converted
appropriately) are isomorpic -/]
noncomputable def equivPresentedMonoid (rel : FreeMonoid β → FreeMonoid β → Prop) :
    PresentedMonoid rel ≃* PresentedMonoid (FreeMonoid.comap_rel e rel) :=
  (Con.comapQuotientEquivOfSurj _ _ (FreeMonoid.congr_iso e).surjective).symm.trans <|
  Con.congr (Con.comap_conGen_of_Bijective (FreeMonoid.congr_iso e) (MulEquiv.bijective _) _ rel)

theorem equivPresentedMonoid_apply_of (rel : FreeMonoid β → FreeMonoid β → Prop) (x : α) :
    equivPresentedMonoid e rel (of rel $ e x) = of (FreeMonoid.comap_rel e rel) x := by
  unfold equivPresentedMonoid PresentedMonoid.of
  simp only [Equiv.toFun_as_coe]
  erw [MulEquiv.trans_apply]
  have helper := Con.comapQuotientEquivOfSurj_symm_mk' (conGen rel) (FreeMonoid.congr_iso e)
    (FreeMonoid.of x)
  rw [← Con.comap_conGen_of_Bijective _ ⟨fun a b => by simp, fun a => by simp⟩ (by aesop)] at helper
  have : Con.comap (fun x => x) (fun x y => rfl) (conGen rel)= conGen rel :=
    Con.ext fun x y ↦ Con.comap_rel fun x y ↦ rfl
  rw [this] at helper
  erw [helper]
  rfl

theorem equivPresentedMonoid_symm_apply_of (rel : FreeMonoid β → FreeMonoid β → Prop) (x : α) :
    (equivPresentedMonoid e rel).symm (PresentedMonoid.of (FreeMonoid.comap_rel e rel) x) =
    PresentedMonoid.of rel (e x) := rfl

end Isomorphism
