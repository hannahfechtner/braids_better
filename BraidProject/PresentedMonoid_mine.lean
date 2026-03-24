/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/

--import BraidProject.FreeMonoid_mine
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence.Basic


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
def PresentedMonoid (rel : FreeMonoid α → FreeMonoid α → Prop) := (conGen rel).Quotient

namespace PresentedMonoid

open Set Submonoid

@[to_additive]
instance (rels : FreeMonoid α → FreeMonoid α → Prop) : Monoid (PresentedMonoid rels) :=
  Con.monoid (conGen rels)

/-- The quotient map from the free monoid on `α` to the presented monoid with the same generators
and the given relations `rels`. -/
@[to_additive /--The quotient map from the free additive monoid on `α` to the presented additive
monoid with the same generators and the given relations `rels`-/]
def mk (rels : FreeMonoid α → FreeMonoid α → Prop) (a : FreeMonoid α) : PresentedMonoid rels :=
  Quotient.mk (conGen rels).toSetoid a

@[to_additive (attr := simp)]
theorem mul_mk (rels : FreeMonoid α → FreeMonoid α → Prop) (a b : FreeMonoid α) : mk rels (a*b) =
  mk rels a * (mk rels b) := rfl

@[to_additive (attr := simp)]
theorem one_def (rels : FreeMonoid α → FreeMonoid α → Prop) : mk rels 1 =
  (1 : PresentedMonoid rels) := rfl

instance (rels : FreeMonoid α → FreeMonoid α → Prop) : MonoidHom (FreeMonoid α)
    (PresentedMonoid rels) where
  toFun := mk rels
  map_mul' := mul_mk rels
  map_one' := one_def rels

/-- `of` is the canonical map from `α` to a presented monoid with generators `x : α`. The term `x`
is mapped to the equivalence class of the image of `x` in `FreeMonoid α`. -/
@[to_additive /--`of` is the canonical map from `α` to a presented additive monoid with generators
`x : α`. The term `x` is mapped to the equivalence class of the image of `x` in `FreeAddMonoid α` -/]
def of (rels : FreeMonoid α → FreeMonoid α → Prop) (x : α) : PresentedMonoid rels :=
  Quotient.mk (conGen rels).toSetoid (FreeMonoid.of x)

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


variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop}

def rel (rels : FreeMonoid α → FreeMonoid α → Prop) := ConGen.Rel rels

private inductive rw_system (rels : FreeMonoid α → FreeMonoid α → Prop) : FreeMonoid α → FreeMonoid α → Prop
  | refl : rw_system rels a a
  | reg : ∀ c d, rels a b → rw_system rels (c * a * d) (c * b * d)
  | symm : ∀ c d, rels a b → rw_system rels (c * b * d) (c * a * d)
  | trans : rw_system rels a b → rw_system rels b c → rw_system rels a c

theorem refl : PresentedMonoid.rel rels a a := ConGen.Rel.refl _
theorem reg : ∀ c d, rels a b → PresentedMonoid.rel rels (c * a * d) (c * b * d) :=
  fun _ _ h => ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _) (ConGen.Rel.of _ _ h))
        (ConGen.Rel.refl _)
theorem symm : ∀ c d, rels a b → PresentedMonoid.rel rels (c * b * d) (c * a * d) :=
  fun _ _ h => ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl _)
        (ConGen.Rel.symm (ConGen.Rel.of _ _ h))) (ConGen.Rel.refl _)
theorem trans : PresentedMonoid.rel rels a b → PresentedMonoid.rel rels b c →
  PresentedMonoid.rel rels a c := fun h1 h2 => h1.trans h2
theorem mul : PresentedMonoid.rel rels a b → PresentedMonoid.rel rels c d →
  PresentedMonoid.rel rels (a * c) (b * d) := fun h1 h2 => ConGen.Rel.mul h1 h2
theorem mul_left : rels a b → PresentedMonoid.rel rels c d →
  PresentedMonoid.rel rels (a * c) (b * d) := fun h1 h2 => ConGen.Rel.mul (ConGen.Rel.of _ _ h1) h2
theorem mul_right : PresentedMonoid.rel rels a b → rels c d →
  PresentedMonoid.rel rels (a * c) (b * d) := fun h1 h2 => ConGen.Rel.mul h1 (ConGen.Rel.of _ _ h2)
theorem append_left : PresentedMonoid.rel rels c d →
  PresentedMonoid.rel rels (a * c) (a * d) := fun h => ConGen.Rel.mul refl h
theorem append_right : PresentedMonoid.rel rels a b →
  PresentedMonoid.rel rels (a * c) (b * c) := fun h => ConGen.Rel.mul h refl
theorem rel_left : rels c d → PresentedMonoid.rel rels (a * c) (a * d) :=
  fun h => ConGen.Rel.mul refl (ConGen.Rel.of _ _ h)
theorem rel_right : rels a b → PresentedMonoid.rel rels (a * c) (b * c) :=
  fun h => ConGen.Rel.mul (ConGen.Rel.of _ _ h) refl
theorem rel_alone : rels a b → PresentedMonoid.rel rels a b :=
  fun h => ConGen.Rel.of _ _ h
theorem symm_alone : rels a b → PresentedMonoid.rel rels b a :=
  fun h => ConGen.Rel.symm (ConGen.Rel.of _ _ h)
theorem swap : PresentedMonoid.rel rels a b → PresentedMonoid.rel rels b a :=
  fun h => ConGen.Rel.symm h

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

private theorem rw_system_cg (rels : FreeMonoid α → FreeMonoid α → Prop) : rw_system rels a b ↔ rel rels a b := by
  constructor
  · intro h
    induction h with
    | refl => exact refl
    | reg c d h => exact reg _ _ h
    | symm c d h => exact symm _ _ h
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

-- @[induction_eliminator]
-- theorem rel_induction {P : FreeMonoid α → FreeMonoid α → Prop} (h : rel rels a b)
--     (h1 : ∀ a, P a a) (h2 : ∀ a b, rels a b → P a b) (h3 : ∀ a b, P b a → P a b)
--     (h4 : ∀ a b c, P a b ∧ P b c → P a c) (h5 : ∀ a b c d, P a b → P c d → P (a * c) (b * d))
--   : P a b := by
--   induction h with
--   | of _ _ ih =>
--     exact h2 _ _ ih
--   | symm _ ih =>
--     exact h3 _ _ ih
--   | refl => exact h1 _
--   | trans _ _ h1 h2 => exact h4 _ _ _ ⟨h1, h2⟩
--   | mul _ _ h1 h2 => exact h5 _ _ _ _ h1 h2

theorem rel_induction_rw {P : FreeMonoid α → FreeMonoid α → Prop} {a b : FreeMonoid α}
    (h : rel rels a b)
    (h1 : ∀ (a : FreeMonoid α), P a a)
    (h2 : ∀ a b {c d}, rels a b → P (c * a * d) (c * b * d))
    (h3 : ∀ a b {c d}, rels b a → P (c * a * d) (c * b * d))
    (h4 : ∀ a b c, P a b ∧ P b c → P a c)
  : P a b := by
  induction ((rw_system_cg _).mpr h) with
  | refl =>
    exact h1 _
  | reg _ _ ih =>
    exact h2 _ _ ih
  | symm _ _ ih =>
    exact h3 _ _ ih
  | trans ha hb h1 h2 => exact h4 _ _ _ ⟨h1 ((rw_system_cg _).mp ha), h2 ((rw_system_cg _).mp hb)⟩

-- def rel_induction_rw_C {P : FreeMonoid α → FreeMonoid α → Type} {a b : FreeMonoid α}
--     (h : rel rels a b)
--     (h1 : ∀ (a : FreeMonoid α), P a a)
--     (h2 : ∀ a b {c d}, rels a b → P (c * a * d) (c * b * d))
--     (h3 : ∀ a b {c d}, rels b a → P (c * a * d) (c * b * d))
--     (h4 : ∀ a b c, P a b × P b c → P a c) : P a b := by
--   sorry
  -- have H := (rw_system_cg _).mpr h


  --sorry
  --apply @rel_induction_rw α _ P a b h h1 h2 h3 h4


  -- | refl =>
  --   exact h1 _
  -- | reg _ _ ih =>
  --   exact h2 _ _ ih
  -- | symm _ _ ih =>
  --   exact h3 _ _ ih
  -- | trans ha hb h1 h2 => exact h4 _ _ _ ⟨h1 ((rw_system_cg _).mp ha), h2 ((rw_system_cg _).mp hb)⟩
-- -- @[induction_eliminator]
-- theorem rel_induction {P : FreeMonoid α → FreeMonoid α → Prop} (h : rel rels a b)
--     (h1 : ∀ a, P a a) (h2 : ∀ a b, rels a b → P a b) (h3 : ∀ a b, rels b a → P a b)
--     (h4 : ∀ a b c, P a b ∧ P b c → P a c) (h5 : ∀ a b c d, P a b → P c d → P (a * c) (b * d))
--   : P a b := by
--   induction (rw_system_cg rels).mpr h with
--   | refl =>
--     exact h1 _
--   | symm _ _ ih => exact h3 _ _ (PresentedMonoid.symm _ _ ih)
--   | reg => exact h1 _
--   | trans _ _ h1 h2 =>
--     rename_i g1 g2
--     exact h4 _ _ _ ⟨h1 <| (mine_cg rels).mp g1, h2 <| (mine_cg rels).mp g2⟩

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

theorem lift_of_eq_mk_of_mulHom {β : Type} [Monoid β] (r : FreeMonoid α)
    (f : PresentedMonoid rels →* β) :
    (FreeMonoid.lift fun x => f (PresentedMonoid.of rels x)) r =
    (f (PresentedMonoid.mk rels r)) := by
  induction r using FreeMonoid.inductionOn' with
  | one => exact f.map_one.symm
  | mul_of b a ih =>
    rw [map_mul, ih, FreeMonoid.lift_eval_of, PresentedMonoid.mul_mk, map_mul]
    rfl

def lift_hom {β : Type} [Monoid β] (f :  α → β) (h : ∀ (a b : FreeMonoid α),
    (conGen rels) a b → (FreeMonoid.lift f) a = (FreeMonoid.lift f) b ) :
    (conGen rels).Quotient →* β := Con.lift (conGen rels) (FreeMonoid.lift f) h

theorem lift_hom_mk {β : Type} [Monoid β] (x : α) (f : α → β)
    (h : ∀ (a b : FreeMonoid α),
    (conGen rels) a b → (FreeMonoid.lift f) a = (FreeMonoid.lift f) b ) :
    PresentedMonoid.lift_hom f h (PresentedMonoid.of rels x) = f x :=
    Con.lift_mk' h (FreeMonoid.of x)

/-- The generators of a presented monoid generate the presented monoid. That is, the submonoid
closure of the set of generators equals `⊤`. -/
@[to_additive (attr := simp) /--The generators of a presented additive monoid generate the presented
additive monoid. That is, the submonoid closure of the set of generators equals `⊤`-/]
theorem closure_range_of (rels : FreeMonoid α → FreeMonoid α → Prop) :
    Submonoid.closure (Set.range (PresentedMonoid.of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction x with
  | h a =>
  induction a with
  | one => exact Submonoid.one_mem _
  | of x => exact subset_closure (Exists.intro x rfl)
  | mul x y hx hy => exact Submonoid.mul_mem _ hx hy

section ToMonoid
variable {α M : Type*} [Monoid M] (f : α → M)
variable {rels : FreeMonoid α → FreeMonoid α → Prop}
variable (h : ∀ a b : FreeMonoid α, rels a b →  FreeMonoid.lift f a = FreeMonoid.lift f b)

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
  | mul x y hx hy => rw [mul_mk, map_mul, map_mul, hx, hy]

section FreeMonoid
namespace FreeMonoid
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


end FreeMonoid

section Con
namespace Con

@[to_additive]
theorem comap_conGen_of_Bijective {M N : Type*} [Mul M] [Mul N] (f : M → N)
    (hf : Function.Bijective f) (H : ∀ (x y : M), f (x * y) = f x * f y) (rel : N → N → Prop) :
    Con.comap f H (conGen rel) = conGen (fun x y ↦ rel (f x) (f y)) := by
  ext a b
  constructor
  · intro h
    simp only [Con.comap_rel] at h
    have H : ∀ n1 n2, (conGen rel) n1 n2 → ∀ a b, f a = n1 → f b = n2 →
        (conGen fun x y ↦ rel (f x) (f y)) a b := by
      intro n1 n2 h
      induction h with
      | of x y h =>
        intro _ _ fa fb
        apply ConGen.Rel.of
        rw [fa, fb]
        exact h
      | refl x =>
        intro _ _ fc fd
        rw [hf.1 (fc.trans fd.symm)]
        exact ConGen.Rel.refl _
      | symm _ h => exact fun a b fs fb ↦ ConGen.Rel.symm (h b a fb fs)
      | trans _ _ ih ih1 =>
        exact fun a b fa fb ↦ Exists.casesOn (hf.right _) fun c' hc' ↦
        ConGen.Rel.trans (ih a c' fa hc') (ih1 c' b hc' fb)
      | mul _ _ ih ih1 =>
        rename_i w x y z _ _
        intro a b fa fb
        rcases Function.bijective_iff_has_inverse.mp hf with ⟨f', is_inv⟩
        have Ha : a = f' w * f' y := by
          rw [← is_inv.1 a, fa]
          have H : f (f' (w * y)) = f (f' w * f' y) := by
            rw [is_inv.2 (w * y), H, is_inv.2 w, is_inv.2 y]
          exact hf.1 H
        have Hb : b = f' x * f' z := by
          rw [← is_inv.1 b, fb]
          have H : f (f' (x * z)) = f (f' x * f' z) := by
            rw [is_inv.2 (x * z), H, is_inv.2 x, is_inv.2 z]
          exact hf.1 H
        rw [Ha, Hb]
        exact ConGen.Rel.mul (ih (f' w) (f' x) (is_inv.right w) (is_inv.right x))
          (ih1 (f' y) (f' z) (is_inv.right y) (is_inv.right z))
    exact H (f a) (f b) h a b rfl rfl
  intro h
  simp only [Con.comap_rel]
  exact ConGen.Rel.rec (fun x y h ↦ ConGen.Rel.of (f x) (f y) h) (fun x ↦ ConGen.Rel.refl (f x))
    (fun _ h ↦ ConGen.Rel.symm h) (fun _ _ h1 h2 ↦ h1.trans h2) (fun {w x y z} _ _ h1 h2 ↦
    (congrArg (fun a ↦ (conGen rel) a (f (x * z))) (H w y)).mpr
    (((congrArg (fun a ↦ (conGen rel) (f w * f y) a) (H x z))).mpr
    (ConGen.Rel.mul h1 h2))) h

end Con

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
