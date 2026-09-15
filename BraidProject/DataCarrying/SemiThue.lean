import Mathlib.Data.Nat.Dist
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Induction
import BraidProject.Additions.FreeMonoid
import BraidProject.SemiThue

inductive SemiThueData {α : Type} (rels : List α → List α → Type) : List α → List α → Type
| refl {a : List α} : SemiThueData rels a a
| step {a b : List α} (c d : List α) (h : rels a b) : SemiThueData rels (c ++ a ++ d) (c ++ b ++ d)
| trans {a b c : List α} : SemiThueData rels a b → SemiThueData rels b c → SemiThueData rels a c

theorem SemiThueData.to_SemiThue {rels : List α → List α → Type} {rels' : List α → List α → Prop}
    (h : SemiThueData rels a b) (hr : ∀ a b, rels a b → rels' a b) : SemiThue rels' a b :=
  match h with
  | .refl => SemiThue.refl
  | .step c d h => SemiThue.step c d (hr _ _ h)
  | .trans f g => (f.to_SemiThue hr).trans (g.to_SemiThue hr)

inductive SemiThueDataDerivation (rels : List α → List α → Type) : List α → List α → Type
| refl {a : List α} : SemiThueDataDerivation rels a a
| step {a b c d e : List α} (h1 : SemiThueDataDerivation rels e (c ++ a ++ d)) (h2 : rels a b) :
    SemiThueDataDerivation rels e (c ++ b ++ d)

theorem SemiThueDataDerivation.to_SemiThueDerivation
    {rels : List α → List α → Type} {rels' : List α → List α → Prop}
    (h : SemiThueDataDerivation rels a b) (hr : ∀ a b, rels a b → rels' a b) :
    SemiThueDerivation rels' a b :=
  match h with
  | .refl => SemiThueDerivation.refl
  | .step h1 h2 => SemiThueDerivation.step (h1.to_SemiThueDerivation hr) (hr _ _ h2)

def SemiThueDataDerivation.trans
    (h1 : SemiThueDataDerivation rels a b) (h2 : SemiThueDataDerivation rels b c) :
    SemiThueDataDerivation rels a c  := by
  match h2 with
  | SemiThueDataDerivation.refl => use h1
  | SemiThueDataDerivation.step h1 h2 =>
    rename_i e f g h i j k
    use SemiThueDataDerivation.step (SemiThueDataDerivation.trans f h1) h2

namespace SemiThueData

def toSemiThueDataDerivation {a b : List α} (h : SemiThueData rels a b) :
    SemiThueDataDerivation rels a b := by
  match h with
  | SemiThueData.refl => exact SemiThueDataDerivation.refl
  | SemiThueData.step _ _ h => exact SemiThueDataDerivation.step SemiThueDataDerivation.refl h
  | SemiThueData.trans h1 h2 => exact SemiThueDataDerivation.trans (toSemiThueDataDerivation h1) (toSemiThueDataDerivation h2)

def cons (h : SemiThueData rels a b) : SemiThueData rels (c :: a) (c :: b) := by
  match h with
  | SemiThueData.refl => exact SemiThueData.refl
  | SemiThueData.step _ _ h =>
    rw [← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append]
    exact SemiThueData.step _ _ h
  | SemiThueData.trans f g =>
    apply (SemiThueData.cons f).trans (SemiThueData.cons g)

def append_left : {c : List α} → SemiThueData rels a b → SemiThueData rels (c ++ a) (c ++ b)
  | [], h => h
  | _ :: _, h => SemiThueData.cons (append_left h)

def append_right (h : SemiThueData rels a b) : SemiThueData rels (a ++ c) (b ++ c) := by
  match h with
  | SemiThueData.refl => exact SemiThueData.refl
  | @SemiThueData.step _ _ x y c₁ d₁ h =>
    have eq1 : c₁ ++ x ++ (d₁ ++ c) = c₁ ++ x ++ d₁ ++ c := (List.append_assoc _ _ _).symm
    have eq2 : c₁ ++ y ++ (d₁ ++ c) = c₁ ++ y ++ d₁ ++ c := (List.append_assoc _ _ _).symm
    exact eq1 ▸ eq2 ▸ (SemiThueData.step c₁ (d₁ ++ c) h)
  | SemiThueData.trans f g =>
    apply (SemiThueData.append_right f).trans (SemiThueData.append_right g)

def append_left_right (h : SemiThueData rels a b) : SemiThueData rels (c ++ a ++ d) (c ++ b ++ d) :=
  SemiThueData.append_right (SemiThueData.append_left h)

def of_rel (h : rels a b) : SemiThueData rels a b :=
  have eq1 : a ++ [] = a := List.append_nil _
  have eq2 : b ++ [] = b := List.append_nil _
  eq1 ▸ eq2 ▸ (SemiThueData.step [] [] h)

def append (hab : SemiThueData rels a b) (hcd : SemiThueData rels c d) :
  SemiThueData rels (a ++ c) (b ++ d) := (SemiThueData.append_right hab).trans (SemiThueData.append_left hcd)

def rel_subset (h : SemiThueData rel₁ a b) (hr : ∀ a b, rel₁ a b → rel₂ a b) :
    SemiThueData rel₂ a b :=
  match h with
  | .refl => .refl
  | .step c d h => .step c d (hr _ _ h)
  | .trans f g => .trans (rel_subset f hr) (rel_subset g hr)

@[simp]
theorem rel_subset_refl {rel₁ rel₂ : List α → List α → Type}  (hr : ∀ a b, rel₁ a b → rel₂ a b) :
    rel_subset (@SemiThueData.refl _ rel₁ a) hr = SemiThueData.refl := rfl
@[simp]
theorem rel_subset_step {rel₁ rel₂ : List α → List α → Type} (c d : List α) (h : rel₁ a b)
    (hr : ∀ a b, rel₁ a b → rel₂ a b) :
    rel_subset (SemiThueData.step c d h) hr = SemiThueData.step c d (hr _ _ h) := rfl
@[simp]
theorem rel_subset_trans {rel₁ rel₂ : List α → List α → Type} (f : SemiThueData rel₁ a b) (g : SemiThueData rel₁ b c)
    (hr : ∀ a b, rel₁ a b → rel₂ a b) :
    rel_subset (f.trans g) hr = (rel_subset f hr).trans (rel_subset g hr) := rfl

def length {a b : List α} {rels : List α → List α → Type}
  (rels_length : {a b : List α} → rels a b → ℕ) (h : SemiThueData rels a b) : ℕ := match h with
| SemiThueData.refl => 0
| SemiThueData.step _ _ h1 => rels_length h1
| SemiThueData.trans h1 h2 => length rels_length h1 + length rels_length h2


@[simp]
theorem length_refl : length rels_length (@SemiThueData.refl _ _ a) = 0 := rfl

@[simp]
theorem length_trans : length rels_length (SemiThueData.trans h1 h2) =
    length rels_length h1 + length rels_length h2 := rfl

@[simp]
theorem length_step {c d : List α} :
  length rels_length (SemiThueData.step c d h) = rels_length h := rfl

theorem length_eq_zero (h : SemiThueData rels a b)
    (hz : ∀ {a b} (r : rels a b), rels_length r = 0) :
    length rels_length h = 0 := by
  induction h with
  | refl => rfl
  | step c d h => exact hz h
  | trans _ _ _ _ => simp_all

@[simp]
theorem length_cons (h : SemiThueData rels a b) :
    length rels_length (@SemiThueData.cons _ _ a b c h) = length rels_length h := by
  induction h with
  | refl => rfl
  | step _ _ h => rfl
  | trans f g hf hg =>
    unfold SemiThueData.cons
    rw [length_trans, length_trans, hf, hg]

theorem length_rel_subset {rel₁ rel₂ : List α → List α → Type}
    {rel₁_length : {a b : List α} → rel₁ a b → ℕ} {rel₂_length : {a b : List α} → rel₂ a b → ℕ}
    (h : SemiThueData rel₁ a b) (hr : ∀ a b, rel₁ a b → rel₂ a b)
    (hr' : ∀ a b, (h1 : rel₁ a b) → @rel₁_length a b h1 = @rel₂_length a b (hr a b h1)) :
    length rel₁_length h = length rel₂_length (rel_subset h hr) := by
  induction h with
  | refl => rfl
  | step c d h => simp [hr']
  | trans _ _ _ _ => simp_all

--Fording
@[simp]
private theorem ford_length_left
    {a a' b : List α} (h : SemiThueData rels a b) (eq : a = a') :
    length rels_length (eq ▸ h : SemiThueData rels a' b) = length rels_length h := by
  subst eq; rfl

@[simp]
private theorem ford_length_right {a b b' : List α} (h : SemiThueData rels a b) (eq : b = b') :
    length rels_length (eq ▸ h : SemiThueData rels a b') = length rels_length h := by
  subst eq; rfl

@[simp]
theorem length_append_left (h : SemiThueData rels a b) :
    length rels_length (@SemiThueData.append_left _ _ a b c h) = length rels_length h := by
  induction c with
  | nil => rfl
  | cons x xs ih =>
    show length rels_length (SemiThueData.cons (@SemiThueData.append_left _ _ _ _ xs h)) = _
    rw [length_cons]
    exact ih

@[simp]
theorem length_append_right (h : SemiThueData rels a b) :
    length rels_length (@SemiThueData.append_right _ _ a b c h) = length rels_length h := by
  induction h with
  | refl => rfl
  | step c d h =>
    unfold SemiThueData.append_right
    simp
  | trans f g hf hg =>
    unfold SemiThueData.append_right
    rw [length_trans, length_trans, hf, hg]

@[simp]
theorem length_append_left_right (h : SemiThueData rels a b) :
    length rels_length (@SemiThueData.append_left_right _ _ a b c d h) = length rels_length h := by
  simp [SemiThueData.append_left_right]

@[simp]
theorem length_append (hab : SemiThueData rels a b) (hcd : SemiThueData rels c d) :
  length rels_length (SemiThueData.append hab hcd) =
    length rels_length hab + length rels_length hcd := by
  unfold SemiThueData.append
  rw [length_trans, length_append_right, length_append_left]


@[simp]
theorem length_of_rel {a b : List α} {rels : List α → List α → Type}
    {rels_length : {a b : List α} → rels a b → ℕ} (h : rels a b) :
    length rels_length (@SemiThueData.of_rel _ rels _ _ h) = rels_length h := by
  simp only [of_rel, ford_length_left, ford_length_right]
  rfl

end SemiThueData

namespace SemiThueDataDerivation

def toSemiThueData {a b : List α} (h : SemiThueDataDerivation rels a b) :
    SemiThueData rels a b := by
  match h with
  | SemiThueDataDerivation.refl =>  exact SemiThueData.refl
  | SemiThueDataDerivation.step h1 h2 => exact (toSemiThueData h1).trans (SemiThueData.step _ _ h2)

def rel_subset (h : SemiThueDataDerivation rel₁ a b) (hr : ∀ a b, rel₁ a b → rel₂ a b) : SemiThueDataDerivation rel₂ a b := by
  match h with
  | SemiThueDataDerivation.refl => exact SemiThueDataDerivation.refl
  | SemiThueDataDerivation.step h1 h => exact SemiThueDataDerivation.step (rel_subset h1 hr) (hr _ _ h)

section Length
def length {rels : List α → List α → Type} (rels_length : {a b : List α} → rels a b → ℕ) (h : SemiThueDataDerivation rels a b) : ℕ := match h with
| SemiThueDataDerivation.refl => 0
| SemiThueDataDerivation.step h1 h2 => SemiThueDataDerivation.length rels_length h1 + rels_length h2

variable {rels : List α → List α → Type} {rels_length : {a b : List α} → rels a b → ℕ}
@[simp]
def length_refl: length rels_length (@SemiThueDataDerivation.refl _ rels a)= 0 := rfl

@[simp]
theorem length_step
  (h1 : SemiThueDataDerivation rels a (c ++ b ++ d)) (h2 : rels b e) :
  length rels_length (SemiThueDataDerivation.step h1 h2) =
  length rels_length h1 + rels_length h2 := rfl

@[simp]
theorem length_trans (h1 : SemiThueDataDerivation rels a b) (h2 : SemiThueDataDerivation rels b c) :
  length rels_length (h1.trans h2) = length rels_length h1 + length rels_length h2 := by
  induction h2 with
  | refl => rfl
  | step h1 h2 ih =>
    rw [length_step, ← Nat.add_assoc]
    unfold trans
    rw [length_step, Nat.add_right_cancel_iff]
    apply ih

theorem toSemiThueData_length {a b : List α} (h : SemiThueDataDerivation rels a b) :
    SemiThueData.length rels_length (toSemiThueData h) = length rels_length h := by
  induction h with
  | refl => rfl
  | step h1 h2 ih =>
    rw [length_step, ← ih]
    rfl

end Length

end SemiThueDataDerivation

theorem SemiThueData.toSemiThueDataDerivation_length {h : SemiThueData rels a b} :
  SemiThueDataDerivation.length rels_length (SemiThueData.toSemiThueDataDerivation h) = SemiThueData.length rels_length h := by
  induction h with
  | refl => rfl
  | step c d h =>
    rw [length_step]
    unfold toSemiThueDataDerivation
    simp only [SemiThueDataDerivation.length_step, SemiThueDataDerivation.length_refl, zero_add]
  | trans f g hf hg =>
    rw [length_trans, ← hf, ← hg]
    exact SemiThueDataDerivation.length_trans _ _
