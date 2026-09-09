import Mathlib.Data.Nat.Dist
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Induction
import BraidProject.Additions.FreeMonoid

inductive SemiThueData {α : Type} (rels : List α → List α → Type) : List α → List α → Type
| refl {a : List α} : SemiThueData rels a a
| step {a b : List α} (c d : List α) (h : rels a b) : SemiThueData rels (c ++ a ++ d) (c ++ b ++ d)
| trans {a b c : List α} : SemiThueData rels a b → SemiThueData rels b c → SemiThueData rels a c

inductive SemiThueDataDerivation (rels : List α → List α → Type) : List α → List α → Type
| refl {a : List α} : SemiThueDataDerivation rels a a
| step {a b c d e : List α} (h1 : SemiThueDataDerivation rels e (c ++ a ++ d)) (h2 : rels a b) :
    SemiThueDataDerivation rels e (c ++ b ++ d)

private noncomputable def SemiThueDataDerivation.trans (h1 : SemiThueDataDerivation rels a b) (h2 : SemiThueDataDerivation rels b c) :
    SemiThueDataDerivation rels a c := by
  induction h2 with
  | refl => exact h1
  | step h1 h2 ih => exact SemiThueDataDerivation.step (ih h1) h2

noncomputable def SemiThueDataDerivation.toSemiThueData {a b : List α} (h : SemiThueDataDerivation rels a b) :
    SemiThueData rels a b := by
  induction h with
  | refl =>  exact SemiThueData.refl
  | step h1 h2 ih => exact ih.trans (SemiThueData.step _ _ h2)

noncomputable def SemiThueData.toSemiThueDataDerivation {a b : List α} (h : SemiThueData rels a b) :
    SemiThueDataDerivation rels a b := by
  induction h with
  | refl => exact SemiThueDataDerivation.refl
  | step _ _ h => exact SemiThueDataDerivation.step SemiThueDataDerivation.refl h
  | trans _ _ ih1 ih2 => exact SemiThueDataDerivation.trans ih1 ih2

def SemiThueData.cons (h : SemiThueData rels a b) : SemiThueData rels (c :: a) (c :: b) := by
  match h with
  | SemiThueData.refl => exact SemiThueData.refl
  | SemiThueData.step _ _ h =>
    rw [← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append]
    exact SemiThueData.step _ _ h
  | SemiThueData.trans f g =>
    apply (SemiThueData.cons f).trans (SemiThueData.cons g)


def SemiThueData.append_left (h : SemiThueData rels a b) : SemiThueData rels (c ++ a) (c ++ b) := by
  match h with
  | SemiThueData.refl => exact SemiThueData.refl
  | SemiThueData.step _ _ h =>
    rename_i e f g i j
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    apply SemiThueData.step _ _ h
  | SemiThueData.trans f g =>
    apply (SemiThueData.append_left f).trans (SemiThueData.append_left g)

def SemiThueData.append_right (h : SemiThueData rels a b) : SemiThueData rels (a ++ c) (b ++ c) := by
  match h with
  | SemiThueData.refl => exact SemiThueData.refl
  | SemiThueData.step _ _ h =>
    rename_i e f g i j
    rw [List.append_assoc _ j c, List.append_assoc _ j c]
    apply SemiThueData.step _ _ h
  | SemiThueData.trans f g =>
    apply (SemiThueData.append_right f).trans (SemiThueData.append_right g)

def SemiThueData.append_left_right (h : SemiThueData rels a b) : SemiThueData rels (c ++ a ++ d) (c ++ b ++ d) :=
  SemiThueData.append_right (SemiThueData.append_left h)

def SemiThueData.of_rel (h : rels a b) : SemiThueData rels a b := by
  rw [← List.nil_append a, ← List.nil_append b, ← List.append_nil ([] ++ a), ← List.append_nil ([] ++ b)]
  exact SemiThueData.step _ _ h

def SemiThueData.append (hab : SemiThueData rels a b) (hcd : SemiThueData rels c d) :
  SemiThueData rels (a ++ c) (b ++ d) := (SemiThueData.append_right hab).trans (SemiThueData.append_left hcd)
