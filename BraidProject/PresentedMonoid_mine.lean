/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/

import BraidProject.FreeMonoid_mine
import Mathlib.Algebra.Group.Submonoid.Operations
import BraidProject.Congruence_mine

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
@[to_additive "Given a set of relations, `rels`, over a type `α`, `PresentedAddMonoid` constructs
the monoid with generators `x : α` and relations `rels` as a quotient of an AddCon' structure over
rels"]
def PresentedMonoid (rel : FreeMonoid' α → FreeMonoid' α → Prop) := (con'Gen rel).Quotient

namespace PresentedMonoid

open Set Submonoid

@[to_additive]
instance (rels : FreeMonoid' α → FreeMonoid' α → Prop) : Monoid (PresentedMonoid rels) :=
  Con'.monoid (con'Gen rels)

/-- The quotient map from the free monoid on `α` to the presented monoid with the same generators
and the given relations `rels`. -/
@[to_additive "The quotient map from the free additive monoid on `α` to the presented additive
monoid with the same generators and the given relations `rels`"]
def mk (rels : FreeMonoid' α → FreeMonoid' α → Prop) (a : FreeMonoid' α) : PresentedMonoid rels :=
  Quotient.mk (con'Gen rels).toSetoid a

@[to_additive (attr := simp)]
theorem mul_mk (rels : FreeMonoid' α → FreeMonoid' α → Prop) (a b : FreeMonoid' α) : mk rels (a*b) =
  mk rels a * (mk rels b) := rfl

@[to_additive (attr := simp)]
theorem one_def (rels : FreeMonoid' α → FreeMonoid' α → Prop) : mk rels 1 =
  (1 : PresentedMonoid rels) := rfl

instance (rels : FreeMonoid' α → FreeMonoid' α → Prop) : MonoidHom (FreeMonoid' α)
    (PresentedMonoid rels) where
  toFun := mk rels
  map_mul' := mul_mk rels
  map_one' := one_def rels

/-- `of` is the canonical map from `α` to a presented monoid with generators `x : α`. The term `x`
is mapped to the equivalence class of the image of `x` in `FreeMonoid' α`. -/
@[to_additive "`of` is the canonical map from `α` to a presented additive monoid with generators
`x : α`. The term `x` is mapped to the equivalence class of the image of `x` in `FreeAddMonoid α`"]
def of (rels : FreeMonoid' α → FreeMonoid' α → Prop) (x : α) : PresentedMonoid rels :=
  Quotient.mk (con'Gen rels).toSetoid (FreeMonoid'.of x)

section inductionOn

variable {α₁ α₂ α₃ : Type* } {rels₁ : FreeMonoid' α₁ → FreeMonoid' α₁ → Prop}
  {rels₂ : FreeMonoid' α₂ → FreeMonoid' α₂ → Prop} {rels₃ : FreeMonoid' α₃ → FreeMonoid' α₃ → Prop}

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


variable {α : Type*} {rels : FreeMonoid' α → FreeMonoid' α → Prop}

def rel (rels : FreeMonoid' α → FreeMonoid' α → Prop) := Con'Gen.Rel rels

inductive mine4 (rels : FreeMonoid' α → FreeMonoid' α → Prop) : FreeMonoid' α → FreeMonoid' α → Prop
  | refl : mine4 rels a a
  | reg : ∀ c d, rels a b → mine4 rels (c * a * d) (c * b * d)
  | symm : ∀ c d, rels a b → mine4 rels (c * b * d) (c * a * d)
  | trans : mine4 rels a b → mine4 rels b c → mine4 rels a c

private theorem mine4_symm : mine4 rels a b → mine4 rels b a := by
  intro h
  induction h with
  | refl => exact mine4.refl
  | reg c d h => exact mine4.symm _ _ h
  | symm c d h => exact mine4.reg _ _ h
  | trans _ _ h3 h4 => exact h4.trans h3

private theorem mul_front : mine4 rels a b → mine4 rels (a * c) (b * c) := by
  intro h
  induction h with
  | refl => exact PresentedMonoid.mine4.refl
  | reg c d h =>
    rename_i e f g
    rw [mul_assoc _ d e, mul_assoc _ d e]
    exact PresentedMonoid.mine4.reg _ _ h
  | symm c d h =>
    rename_i e f g
    rw [mul_assoc _ d e, mul_assoc _ d e]
    exact PresentedMonoid.mine4.symm _ _ h
  | trans _ _ ha hb => exact ha.trans hb

private theorem mul_back : mine4 rels a b → mine4 rels (c * a) (c * b) := by
  intro h
  induction h with
  | refl => exact PresentedMonoid.mine4.refl
  | reg c d h =>
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    exact mine4.reg _ _ h
  | symm c d h =>
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    apply mine4.symm _ _ h
  | trans _ _ ha hb => exact ha.trans hb

private theorem mine4_mul : mine4 rels a b → mine4 rels c d → mine4 rels (a * c) (b * d) := by
  intro h1 h2
  induction h1 with
  | refl => exact mul_back h2
  | reg c d h =>
    induction h2 with
    | refl => exact mul_front <| mine4.reg _ _ h
    | reg c d h1 =>
      exact (mul_front (mine4.reg _ _ h)).trans (mul_back (mine4.reg _ _ h1))
    | symm c d h1 =>
      exact (mul_front (mine4.reg _ _ h)).trans (mul_back (mine4.symm _ _ h1))
    | trans _ _ h3 h4 =>
      rename_i g i k l m _ _
      apply h3.trans
      have step : mine4 rels (c * i * d * l) (c * g * d * l) := by
        rw [mul_assoc _ d, mul_assoc _ d]
        exact mine4.symm _ _ h
      apply step.trans h4
  | symm c d h =>
    rename_i g i
    induction h2 with
    | refl =>
      apply mul_front
      apply mine4.symm _ _ h
    | reg c d h1 =>
      exact (mul_front (mine4.symm _ _ h)).trans (mul_back (mine4.reg _ _ h1))
    | symm c d h1 =>
      exact (mul_front (mine4.symm _ _ h)).trans (mul_back (mine4.symm _ _ h1))
    | trans _ _ hc hd =>
      rename_i j k l m _ _
      apply hc.trans
      have step : PresentedMonoid.mine4 rels (c * g * d * l) (c * i * d * l) := by
        rw [mul_assoc _ d, mul_assoc _ d]
        exact mine4.reg _ _ h
      exact step.trans hd
  | trans _ hb hc _ => exact hc.trans (mul_front hb)

theorem mine4_cg (rels : FreeMonoid' α → FreeMonoid' α → Prop) : mine4 rels a b ↔ Con'Gen.Rel rels a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Con'Gen.Rel.refl _
    | reg c d h =>
      exact Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl _) (Con'Gen.Rel.of _ _ h))
        (Con'Gen.Rel.refl _)
    | symm c d h =>
      exact Con'Gen.Rel.mul (Con'Gen.Rel.mul (Con'Gen.Rel.refl _)
        (Con'Gen.Rel.symm (Con'Gen.Rel.of _ _ h))) (Con'Gen.Rel.refl _)
    | trans _ _ h1 h2 => exact h1.trans h2
  intro h
  induction h with
  | of x y h =>
    rw [← mul_one x, ← mul_one y, ← one_mul x, ← one_mul y]
    exact mine4.reg _ _ h
  | refl _ => exact mine4.refl
  | symm _ h => exact mine4_symm h
  | trans _ _ h1 h2 => exact h1.trans h2
  | mul _ _ h1 h2 => exact mine4_mul h1 h2

-- @[induction_eliminator]
-- theorem rel_induction {P : FreeMonoid' α → FreeMonoid' α → Prop} (h : rel rels a b)
--     (h1 : ∀ a, P a a) (h2 : ∀ a b, rels a b → P a b) (h3 : ∀ a b, rels b a → P a b)
--     (h4 : ∀ a b c, P a b ∧ P b c → P a c) (h5 : ∀ a b c d, P a b → P c d → P (a * c) (b * d))
--   : P a b := by
--   induction (mine4_cg rels).mpr h with
--   | of _ =>
--     rename_i _ ih
--     exact h2 _ _ ih
--   | symm ih => exact h3 _ _ ih
--   | refl => exact h1 _
--   | trans _ _ h1 h2 =>
--     rename_i g1 g2
--     exact h4 _ _ _ ⟨h1 <| (mine_cg rels).mp g1, h2 <| (mine_cg rels).mp g2⟩
--   | steps first second h1 h2 =>
--     exact h5 _ _ _ _ (h1 ((mine_cg rels).mp first)) (h2 ((mine_cg rels).mp second))

theorem sound (h : rel rels a b) : mk rels a = mk rels b :=
  Quotient.sound h

theorem exact {rels : FreeMonoid' α → FreeMonoid' α → Prop}
    (h : PresentedMonoid.mk rels a = PresentedMonoid.mk rels b) : PresentedMonoid.rel rels a b := by
  apply Quot.exact at h
  unfold rel
  induction h
  · rename_i ih
    change PresentedMonoid.rel _ _ _ at ih
    induction ih
    · rename_i a b h
      exact Con'Gen.Rel.of a b h
    · exact Con'Gen.Rel.refl _
    · rename_i a
      exact Con'Gen.Rel.symm a
    · rename_i a b
      exact Con'Gen.Rel.trans a b
    rename_i a b
    exact Con'Gen.Rel.mul a b
  · exact Con'Gen.Rel.refl _
  · rename_i a
    exact Con'Gen.Rel.symm a
  rename_i a b
  exact Con'Gen.Rel.trans a b

def lift_of_mul {β : Type} (f : FreeMonoid' α → β) (hm : ∀ {a b c d}, f a = f c →
    f b = f d → f (a * b) = f (c * d))
    (h : ∀ (a b : FreeMonoid' α), rels a b → f a = f b) : PresentedMonoid rels → β :=
  fun c => Con'.liftOn c f (fun _ _ cg => by
    induction cg with
    | of x y ih => exact h _ _ ih
    | refl x => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
    | mul _ _ ih1 ih2 => exact hm ih1 ih2 )

@[simp]
theorem lift_of_mul_mk {β : Type} (x : FreeMonoid' α) (f : FreeMonoid' α → β)
    (hm : ∀ {a b c d}, f a = f c → f b = f d → f (a * b) = f (c * d))
    (h : ∀ (a b : FreeMonoid' α), rels a b → f a = f b) :
    lift_of_mul f hm h (PresentedMonoid.mk rels x) = f x := rfl

def lift_hom {β : Type} [Monoid β] (f :  α → β) (h : ∀ (a b : FreeMonoid' α),
    (con'Gen rels) a b → (FreeMonoid'.lift f) a = (FreeMonoid'.lift f) b ) :
    (con'Gen rels).Quotient →* β := Con'.lift (con'Gen rels) (FreeMonoid'.lift f) h

theorem lift_hom_mk {β : Type} [Monoid β] (x : α) (f : α → β)
    (h : ∀ (a b : FreeMonoid' α),
    (con'Gen rels) a b → (FreeMonoid'.lift f) a = (FreeMonoid'.lift f) b ) :
    PresentedMonoid.lift_hom f h (PresentedMonoid.of rels x) = f x :=
    Con'.lift_mk' h (FreeMonoid'.of x)



/-- The generators of a presented monoid generate the presented monoid. That is, the submonoid
closure of the set of generators equals `⊤`. -/
@[to_additive (attr := simp) "The generators of a presented additive monoid generate the presented
additive monoid. That is, the submonoid closure of the set of generators equals `⊤`"]
theorem closure_range_of (rels : FreeMonoid' α → FreeMonoid' α → Prop) :
    Submonoid.closure (Set.range (PresentedMonoid.of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction' x with a
  induction a
  · exact Submonoid.one_mem _
  · rename_i x
    exact subset_closure (Exists.intro x rfl)
  rename_i x y hx hy
  exact Submonoid.mul_mem _ hx hy

section ToMonoid
variable {α M : Type*} [Monoid M] (f : α → M)
variable {rels : FreeMonoid' α → FreeMonoid' α → Prop}
variable (h : ∀ a b : FreeMonoid' α, rels a b →  FreeMonoid'.lift f a = FreeMonoid'.lift f b)

/-- The extension of a map `f : α → M` that satisfies the given relations to a monoid homomorphism
from `PresentedMonoid rels → M`. -/
@[to_additive "The extension of a map `f : α → M` that satisfies the given relations to an
additive-monoid homomorphism from `PresentedAddMonoid rels → M`"]
def toMonoid : MonoidHom (PresentedMonoid rels) M :=
  Con'.lift _ (FreeMonoid'.lift f) (Con'.con'Gen_le h)

@[to_additive]
theorem toMonoid.unique (g : MonoidHom (con'Gen rels).Quotient M)
    (hg : ∀ a : α, g (of rels a) = f a) : g = toMonoid f h :=
  Con'.lift_unique (proof_1 f h) g (FreeMonoid'.hom_eq fun x ↦ let_fun this := hg x; this)

@[to_additive (attr := simp)]
theorem toMonoid.of {x : α} : (PresentedMonoid.toMonoid f h) (PresentedMonoid.of rels x) =
    f x := rfl

end ToMonoid

@[to_additive (attr := ext)]
theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid' α → FreeMonoid' α → Prop)
    {φ ψ : PresentedMonoid rels →* M} (hx : ∀ (x : α), φ (.of rels x) = ψ (.of rels x)) :
    φ = ψ := by
  ext a
  induction' a with b
  induction b
  · rw [one_def, map_one, map_one]
  · rename_i x
    exact hx x
  rename_i x y hx hy
  rw [mul_mk, map_mul, map_mul, hx, hy]

section Isomorphism
variable {β : Type*} (e : α ≃ β) (rels : FreeMonoid' α → FreeMonoid' α → Prop)

/-- presented monoids over isomorphic types (with the relations converted appropriately)
are isomorpic -/
@[to_additive "presented additive monoids over isomorphic types (with the relations converted
appropriately) are isomorpic"]
noncomputable def equivPresentedMonoid (rel : FreeMonoid' β → FreeMonoid' β → Prop) :
    PresentedMonoid rel ≃* PresentedMonoid (FreeMonoid'.comap_rel e rel) :=
  (Con'.comapQuotientEquivOfSurj _ _ (FreeMonoid'.congr_iso e).surjective).symm.trans <|
  Con'.congr (Con'.comap_con'Gen_of_Bijective (FreeMonoid'.congr_iso e) (MulEquiv.bijective _) _ rel)

theorem equivPresentedMonoid_apply_of (rel : FreeMonoid' β → FreeMonoid' β → Prop) (x : α) :
    equivPresentedMonoid e rel (of rel $ e x) = of (FreeMonoid'.comap_rel e rel) x := by
  unfold equivPresentedMonoid PresentedMonoid.of
  simp only [Equiv.toFun_as_coe, MulEquiv.trans_apply]
  have helper := Con'.comapQuotientEquivOfSurj_symm_mk' (con'Gen rel) (FreeMonoid'.congr_iso e)
    (FreeMonoid'.of x)
  rw [← Con'.comap_con'Gen_of_Bijective _ ⟨fun a b => by simp, fun a => by simp⟩] at helper
  have : Con'.comap (fun x => x) (fun x y => rfl) (con'Gen rel)= con'Gen rel :=
    Con'.ext fun x y ↦ Con'.comap_rel fun x y ↦ rfl
  rw [this] at helper
  erw [helper, Con'.congr_mk (equivPresentedMonoid.proof_3 e rel) (FreeMonoid'.of x)]
  rfl

theorem equivPresentedMonoid_symm_apply_of (rel : FreeMonoid' β → FreeMonoid' β → Prop) (x : α) :
    (equivPresentedMonoid e rel).symm (PresentedMonoid.of (FreeMonoid'.comap_rel e rel) x) =
    PresentedMonoid.of rel (e x) := rfl

end Isomorphism
