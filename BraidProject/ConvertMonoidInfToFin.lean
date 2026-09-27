import BraidProject.BraidMonoidFin
import Mathlib.Data.Fin.Basic
import BraidProject.BraidMonoidInf
import BraidProject.Additions.Nat

open Braid

theorem braid_monoid_rels_fin_of_inf (n: ℕ) (a b: FreeMonoid ℕ) (holds_in_inf : braid_monoid_rels_inf a b)
    (bounded_a: ∀ (x : ℕ), x ∈ a → x < n.pred) (bounded_b: ∀ (x : ℕ), x ∈ b → x < n.pred) :
    braid_monoid_rels_fin n (FreeMonoid.mapNatToFin n.pred a bounded_a) (FreeMonoid.mapNatToFin n.pred b bounded_b) := by
  cases holds_in_inf with
  | adjacent i =>
    exact braid_monoid_rels_fin.adjacent ⟨i, _⟩ _ rfl
  | separated i j h =>
    apply braid_monoid_rels_fin.separated
    linarith

theorem BraidMonoidFin.eq_of_BraidMonoidInf_eq (n : ℕ) (a b : FreeMonoid ℕ) (bounded_a: ∀ x, x ∈ a → x < n.pred)
    (bounded_b: ∀ x, x ∈ b→ x < n.pred) (h : BraidMonoidInf.mk a = BraidMonoidInf.mk b) :
    BraidMonoidFin.mk _ (FreeMonoid.mapNatToFin n.pred a bounded_a) = BraidMonoidFin.mk _ (FreeMonoid.mapNatToFin n.pred b bounded_b) := by
  apply PresentedMonoid.exact at h
  induction h with
  | of x y old =>
    apply BraidMonoidFin.sound
    apply PresentedMonoid.rels_alone
    exact braid_monoid_rels_fin_of_inf n _ _ old bounded_a bounded_b
  | refl x => rfl
  | symm _ ih => exact (ih bounded_b bounded_a).symm
  | trans _ _ ih1 ih2 =>
    specialize ih1 bounded_a
    rename_i a b c ab _
    have bounded_d : ∀ x, x ∈ b → x < n.pred := by
      intro x hb
      apply bounded_a x
      apply FreeMonoid.mem_symbols.mp
      have : a.symbols = b.symbols :=
          congrArg BraidMonoidInf.generators (BraidMonoidInf.sound ab)
      rw [this]
      exact FreeMonoid.mem_symbols.mpr hb
    exact (ih1 bounded_d).trans (ih2 bounded_d bounded_b)
  | mul _ _ ih1 ih2 =>
    specialize ih1 (by aesop) (by aesop)
    specialize ih2 (by aesop) (by aesop)
    rw [FreeMonoid.mapNatToFin_mul, FreeMonoid.mapNatToFin_mul]
    · exact BraidMonoidFin.concat_mk ih1 ih2
    all_goals aesop
