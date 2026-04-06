/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/

--import BraidProject.FreeMonoid_mine
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence.Basic
import BraidProject.Additions.Congruence
import BraidProject.Additions.FreeMonoid

/-!
# Defining a monoid given by generators and relations

Given a subset `rels` of relations of the free monoid on a type `α`, this file constructs the monoid
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `PresentedMonoid rels`: the quot group of the free group on a type `α` by the steps-to closure
  of a subset `rels` of relations of the free monoid on `α`.
* `of`: The canonical map from `α` to a presented monoid with generators `α`.
* `toMonoid f`: the canonical monoid homomorphism `PresentedMonoid rels → M`, given a function
  `f : α → G` from a type `α` to a monoid `M` which satisfies the relations `rels`.

## Tags

generators, relations, monoid presentations
-/

variable {α : Type*}

/-- Given a set of relations, `rels`, over a type `α`, `PresentedMonoid` constructs the monoid with
generators `x : α` and relations `rels` as a quotient of a congruence structure over rels. -/
@[to_additive /--Given a set of relations, `rels`, over a type `α`, `PresentedAddMonoid` constructs
the monoid with generators `x : α` and relations `rels` as a quotient of an Addcon structure over
rels-/]
def PresentedMonoid (rels : FreeMonoid α → FreeMonoid α → Prop):= (conGen rels).Quotient

namespace PresentedMonoid

section Basic

variable (rels : FreeMonoid α → FreeMonoid α → Prop)

open Set Submonoid

@[to_additive]
instance : Monoid (PresentedMonoid rels) := Con.monoid (conGen rels)

/-- The quotient map from the free monoid on `α` to the presented monoid with the same generators
and the given relations `rels`. -/
@[to_additive /--The quotient map from the free additive monoid on `α` to the presented additive
monoid with the same generators and the given relations `rels`-/]
def mk : FreeMonoid α →ₙ* PresentedMonoid rels := ⟨Quotient.mk (conGen rels).toSetoid, fun _ _ => rfl⟩

@[to_additive (attr := simp)]
theorem mk_mul (a b : FreeMonoid α) : mk rels (a * b) = mk rels a * (mk rels b) := rfl

@[to_additive (attr := simp)]
theorem one_def : mk rels 1 = (1 : PresentedMonoid rels) := rfl

instance : MonoidHom (FreeMonoid α) (PresentedMonoid rels) where
  toFun := mk rels
  map_mul' := fun _ _ => rfl
  map_one' := rfl

/-- `of` is the canonical map from `α` to a presented monoid with generators `x : α`. The term `x`
is mapped to the equivalence class of the image of `x` in `FreeMonoid α`. -/
@[to_additive /--`of` is the canonical map from `α` to a presented additive monoid with generators
`x : α`. The term `x` is mapped to the equivalence class of the image of `x` in `FreeAddMonoid α` -/]
def of (x : α) : PresentedMonoid rels := Quotient.mk (conGen rels).toSetoid (FreeMonoid.of x)

end Basic

section inductionOn

variable {α₁ α₂ α₃ : Type* } {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop}
  {rels₂ : FreeMonoid α₂ → FreeMonoid α₂ → Prop} {rels₃ : FreeMonoid α₃ → FreeMonoid α₃ → Prop}

local notation "P₁" => PresentedMonoid rels₁
local notation "P₂" => PresentedMonoid rels₂
local notation "P₃" => PresentedMonoid rels₃

@[to_additive (attr := elab_as_elim), induction_eliminator]
protected theorem inductionOn {δ : P₁ → Prop} (q : P₁) (h : ∀ a, δ (mk rels₁ a)) : δ q :=
  Quotient.ind h q

@[to_additive (attr := elab_as_elim)]
protected theorem inductionOn₂ {δ : P₁ → P₂ → Prop} (q₁ : P₁) (q₂ : P₂)
    (h : ∀ a b, δ (mk rels₁ a) (mk rels₂ b)) : δ q₁ q₂ :=
  Quotient.inductionOn₂ q₁ q₂ h

@[to_additive (attr := elab_as_elim)]
protected theorem inductionOn₃ {δ : P₁ → P₂ → P₃ → Prop} (q₁ : P₁)
    (q₂ : P₂) (q₃ : P₃) (h : ∀ a b c, δ (mk rels₁ a) (mk rels₂ b) (mk rels₃ c)) :
    δ q₁ q₂ q₃ :=
  Quotient.inductionOn₃ q₁ q₂ q₃ h

end inductionOn

variable {α : Type*}

def rel (rels : FreeMonoid α → FreeMonoid α → Prop) := ConGen.Rel rels

variable {rels : FreeMonoid α → FreeMonoid α → Prop}

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

def lift {β : Type} [Monoid β] (f :  α → β) (h : ∀ (a b : FreeMonoid α),
    (conGen rels) a b → (FreeMonoid.lift f) a = (FreeMonoid.lift f) b ) :
    (conGen rels).Quotient →* β := Con.lift (conGen rels) (FreeMonoid.lift f) h

theorem lift_mk {β : Type} [Monoid β] (x : α) (f : α → β)
    (h : ∀ (a b : FreeMonoid α),
    (conGen rels) a b → (FreeMonoid.lift f) a = (FreeMonoid.lift f) b ) :
    PresentedMonoid.lift f h (PresentedMonoid.of rels x) = f x :=
    Con.lift_mk' h (FreeMonoid.of x)

/-- The generators of a presented monoid generate the presented monoid. That is, the submonoid
closure of the set of generators equals `⊤`. -/
@[to_additive (attr := simp) /--The generators of a presented additive monoid generate the
presented additive monoid. That is, the submonoid closure of the set of generators equals `⊤`-/]
theorem closure_range_of (rels : FreeMonoid α → FreeMonoid α → Prop) :
    Submonoid.closure (Set.range (PresentedMonoid.of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction x with
  | h a =>
  induction a with
  | one => exact Submonoid.one_mem _
  | of x => exact Submonoid.mem_closure_of_mem (Exists.intro x rfl)
  | mul x y hx hy => exact Submonoid.mul_mem _ hx hy

section ToMonoid
variable {α M : Type*} [Monoid M] (f : α → M)
variable {rels : FreeMonoid α → FreeMonoid α → Prop}
variable (h : ∀ a b : FreeMonoid α, rels a b → FreeMonoid.lift f a = FreeMonoid.lift f b)

/-- The extension of a map `f : α → M` that satisfies the given relations to a monoid homomorphism
from `PresentedMonoid rels → M`. -/
@[to_additive /--The extension of a map `f : α → M` that satisfies the given relations to an
additive-monoid homomorphism from `PresentedAddMonoid rels → M`-/]
def toMonoid : MonoidHom (PresentedMonoid rels) M :=
  Con.lift _ (FreeMonoid.lift f) (Con.conGen_le h)

@[to_additive]
theorem toMonoid.unique (g : MonoidHom (conGen rels).Quotient M)
    (hg : ∀ a : α, g (of rels a) = f a) : g = toMonoid f h :=
  Con.lift_unique (Con.conGen_le h) g (FreeMonoid.hom_eq fun x ↦ hg x)

@[to_additive (attr := simp)]
theorem toMonoid.of {x : α} : (PresentedMonoid.toMonoid f h) (PresentedMonoid.of rels x) =
    f x := rfl

end ToMonoid

@[to_additive (attr := ext)]
theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid α → FreeMonoid α → Prop)
    {φ ψ : PresentedMonoid rels →* M} (hx : ∀ (x : α), φ (.of rels x) = ψ (.of rels x)) :
    φ = ψ := by
  ext a
  induction a with
  | h b =>
  induction b with
  | one => rw [one_def, map_one, map_one]
  | of x => exact hx x
  | mul x y hx hy => rw [mk_mul, map_mul, map_mul, hx, hy]

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
