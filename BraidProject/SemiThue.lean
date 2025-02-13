import Mathlib.Data.Nat.Dist
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lex
import BraidProject.Cancellability

inductive SemiThue (rels : List α → List α → Prop) : List α → List α → Prop
| refl (a : List α) : SemiThue rels a a
| reduction {a b c d : List α} (h : rels a b) : SemiThue rels (c++a++d) (c++b++d)
| trans (a b c : List α) : SemiThue rels a b → SemiThue rels b c → SemiThue rels a c

inductive SemiThue_one_step (rels : List α → List α → Prop) : List α → List α → Prop
| refl (a : List α) : SemiThue_one_step rels a a
| one_step {a b c d e : List α} (h1 : SemiThue_one_step rels e (c++a++d)) (h2 : rels a b) :
    SemiThue_one_step rels e (c++b++d)

private theorem one_step_in_front {a b c d e : List α} (h1 : SemiThue_one_step rels (c++a++d) e)
    (h2 : rels b a) : SemiThue_one_step rels (c++b++d) e := by
  have H : ∀ f, SemiThue_one_step rels f e → f = c ++ a ++ d →
      SemiThue_one_step rels (c ++ b ++ d) e := by
    intro f hf
    induction hf
    · intro f_is
      rw [f_is]
      rw [f_is] at h1
      exact SemiThue_one_step.one_step (SemiThue_one_step.refl _) h2
    rename_i l m n
    intro k_is
    rw [k_is] at l
    exact SemiThue_one_step.one_step (n l k_is) m
  exact H _ h1 rfl

private theorem one_step_trans (h1 : SemiThue_one_step rels a b) (h2 : SemiThue_one_step rels b c) :
    SemiThue_one_step rels a c := by
  induction h1
  · assumption
  rename_i d e f g h i j k
  have H : ∀ l, SemiThue_one_step rels l c → l = (f ++ e ++ g) → SemiThue_one_step rels h c := by
    intro l
    intro hl
    induction hl
    · intro l_is
      rw [l_is]
      exact SemiThue_one_step.one_step i j
    intro l_is
    rename_i m n o p q r s t
    rw [l_is] at r t
    apply k
    exact one_step_in_front h2 j
  exact H _ h2 rfl

theorem one_step_equiv_reg {a b : List α} : SemiThue rels a b ↔ SemiThue_one_step rels a b := by
  constructor
  · intro h
    induction h
    · exact SemiThue_one_step.refl _
    · rename_i c d _ _ h
      exact SemiThue_one_step.one_step (SemiThue_one_step.refl _) h
    rename_i ih1 ih2
    exact one_step_trans ih1 ih2
  intro h
  induction h
  · exact SemiThue.refl _
  rename_i h1 h2
  apply h2.trans
  exact SemiThue.reduction h1
