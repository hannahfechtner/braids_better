import Mathlib.Data.Nat.Dist
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Induction
import BraidProject.Additions.FreeMonoid

inductive SemiThue {α : Type} (rels : List α → List α → Prop) : List α → List α → Prop
| refl {a : List α} : SemiThue rels a a
| step {a b : List α} (c d : List α) (h : rels a b) : SemiThue rels (c ++ a ++ d) (c ++ b ++ d)
| trans {a b c : List α} : SemiThue rels a b → SemiThue rels b c → SemiThue rels a c

inductive SemiThueDerivation (rels : List α → List α → Prop) : List α → List α → Prop
| refl {a : List α} : SemiThueDerivation rels a a
| step {a b c d e : List α} (h1 : SemiThueDerivation rels e (c ++ a ++ d)) (h2 : rels a b) :
    SemiThueDerivation rels e (c ++ b ++ d)

private noncomputable def SemiThueDerivation.trans (h1 : SemiThueDerivation rels a b) (h2 : SemiThueDerivation rels b c) :
    SemiThueDerivation rels a c := by
  induction h2 with
  | refl => exact h1
  | step h1 h2 ih => exact SemiThueDerivation.step (ih h1) h2

noncomputable def SemiThueDerivation.toSemiThue {a b : List α} (h : SemiThueDerivation rels a b) :
    SemiThue rels a b := by
  induction h with
  | refl =>  exact SemiThue.refl
  | step h1 h2 ih => exact ih.trans (SemiThue.step _ _ h2)

noncomputable def SemiThue.toSemiThueDerivation {a b : List α} (h : SemiThue rels a b) :
    SemiThueDerivation rels a b := by
  induction h with
  | refl => exact SemiThueDerivation.refl
  | step _ _ h => exact SemiThueDerivation.step SemiThueDerivation.refl h
  | trans _ _ ih1 ih2 => exact SemiThueDerivation.trans ih1 ih2

def SemiThue.cons (h : SemiThue rels a b) : SemiThue rels (c :: a) (c :: b) := by
  match h with
  | SemiThue.refl => exact SemiThue.refl
  | SemiThue.step _ _ h =>
    rw [← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append]
    exact SemiThue.step _ _ h
  | SemiThue.trans f g =>
    apply (SemiThue.cons f).trans (SemiThue.cons g)


def SemiThue.append_left (h : SemiThue rels a b) : SemiThue rels (c ++ a) (c ++ b) := by
  match h with
  | SemiThue.refl => exact SemiThue.refl
  | SemiThue.step _ _ h =>
    rename_i e f g i j
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    apply SemiThue.step _ _ h
  | SemiThue.trans f g =>
    apply (SemiThue.append_left f).trans (SemiThue.append_left g)

def SemiThue.append_right (h : SemiThue rels a b) : SemiThue rels (a ++ c) (b ++ c) := by
  match h with
  | SemiThue.refl => exact SemiThue.refl
  | SemiThue.step _ _ h =>
    rename_i e f g i j
    rw [List.append_assoc _ j c, List.append_assoc _ j c]
    apply SemiThue.step _ _ h
  | SemiThue.trans f g =>
    apply (SemiThue.append_right f).trans (SemiThue.append_right g)

def SemiThue.append_left_right (h : SemiThue rels a b) : SemiThue rels (c ++ a ++ d) (c ++ b ++ d) :=
  SemiThue.append_right (SemiThue.append_left h)

def SemiThue.of_rel (h : rels a b) : SemiThue rels a b := by
  rw [← List.nil_append a, ← List.nil_append b, ← List.append_nil ([] ++ a), ← List.append_nil ([] ++ b)]
  exact SemiThue.step _ _ h

def SemiThue.append (hab : SemiThue rels a b) (hcd : SemiThue rels c d) :
  SemiThue rels (a ++ c) (b ++ d) := (SemiThue.append_right hab).trans (SemiThue.append_left hcd)
