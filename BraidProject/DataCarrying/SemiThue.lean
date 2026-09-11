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

def SemiThueDataDerivation.trans
    (h1 : SemiThueDataDerivation rels a b) (h2 : SemiThueDataDerivation rels b c) :
    SemiThueDataDerivation rels a c  := by
  match h2 with
  | SemiThueDataDerivation.refl => use h1
  | SemiThueDataDerivation.step h1 h2 =>
    rename_i e f g h i j k
    use SemiThueDataDerivation.step (SemiThueDataDerivation.trans f h1) h2


namespace SemiThueData

noncomputable def toSemiThueDataDerivation {a b : List α} (h : SemiThueData rels a b) :
    SemiThueDataDerivation rels a b := by
  induction h with
  | refl => exact SemiThueDataDerivation.refl
  | step _ _ h => exact SemiThueDataDerivation.step SemiThueDataDerivation.refl h
  | trans _ _ ih1 ih2 => exact SemiThueDataDerivation.trans ih1 ih2

def cons (h : SemiThueData rels a b) : SemiThueData rels (c :: a) (c :: b) := by
  match h with
  | SemiThueData.refl => exact SemiThueData.refl
  | SemiThueData.step _ _ h =>
    rw [← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append]
    exact SemiThueData.step _ _ h
  | SemiThueData.trans f g =>
    apply (SemiThueData.cons f).trans (SemiThueData.cons g)

-- def append_left (h : SemiThueData rels a b) : SemiThueData rels (c ++ a) (c ++ b) := by
--   match h with
--   | SemiThueData.refl => exact SemiThueData.refl
--   | SemiThueData.step _ _ h =>
--     rename_i e f g i j
--     rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
--     apply SemiThueData.step _ _ h
--   | SemiThueData.trans f g =>
--     apply (SemiThueData.append_left f).trans (SemiThueData.append_left g)

-- def append_right (h : SemiThueData rels a b) : SemiThueData rels (a ++ c) (b ++ c) := by
--   match h with
--   | SemiThueData.refl => exact SemiThueData.refl
--   | SemiThueData.step _ _ h =>
--     rename_i e f g i j
--     rw [List.append_assoc _ j c, List.append_assoc _ j c]
--     apply SemiThueData.step _ _ h
--   | SemiThueData.trans f g =>
--     apply (SemiThueData.append_right f).trans (SemiThueData.append_right g)

def append_left : {c : List α} → SemiThueData rels a b → SemiThueData rels (c ++ a) (c ++ b)
  | [], h => h
  | _ :: _, h => SemiThueData.cons (append_left h)

def append_right (h : SemiThueData rels a b) : SemiThueData rels (a ++ c) (b ++ c) := by
  match h with
  | SemiThueData.refl => exact SemiThueData.refl
  | @SemiThueData.step _ _ x y c' d h =>
    have step := SemiThueData.step (rels := rels) c' (d ++ c) h
    have eq1 : c' ++ x ++ (d ++ c) = c' ++ x ++ d ++ c := (List.append_assoc _ _ _).symm
    have eq2 : c' ++ y ++ (d ++ c) = c' ++ y ++ d ++ c := (List.append_assoc _ _ _).symm
    exact eq1 ▸ eq2 ▸ step
  | SemiThueData.trans f g =>
    apply (SemiThueData.append_right f).trans (SemiThueData.append_right g)

def append_left_right (h : SemiThueData rels a b) : SemiThueData rels (c ++ a ++ d) (c ++ b ++ d) :=
  SemiThueData.append_right (SemiThueData.append_left h)

def of_rel' (h : rels a b) : SemiThueData rels a b := by
  rw [← List.nil_append a, ← List.nil_append b, ← List.append_nil ([] ++ a), ← List.append_nil ([] ++ b)]
  exact SemiThueData.step _ _ h

def of_rel (h : rels a b) : SemiThueData rels a b :=
  have step := SemiThueData.step (rels := rels) [] [] h
  have eq1 : a ++ [] = a := List.append_nil _
  have eq2 : b ++ [] = b := List.append_nil _
  eq1 ▸ eq2 ▸ step

def append (hab : SemiThueData rels a b) (hcd : SemiThueData rels c d) :
  SemiThueData rels (a ++ c) (b ++ d) := (SemiThueData.append_right hab).trans (SemiThueData.append_left hcd)

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

@[simp]
theorem length_cons (h : SemiThueData rels a b) :
    length rels_length (@SemiThueData.cons _ _ a b c h) = length rels_length h := by
  induction h with
  | refl => rfl
  | step _ _ h => rfl
  | trans f g hf hg =>
    unfold SemiThueData.cons
    rw [length_trans, length_trans, hf, hg]

-- @[simp]
-- theorem length_append_left (h : SemiThueData rels a b) :
--     length rels_length (@SemiThueData.append_left _ _ a b c h) = length rels_length h := by
--   induction h with
--   | refl => rfl
--   | step _ _ h =>
--     unfold SemiThueData.append_left
--     rfl
--   | trans f g hf hg =>
--     unfold SemiThueData.append_left
--     rw [length_trans, length_trans, hf, hg]

-- @[simp]
-- theorem length_append_right (h : SemiThueData rels a b) :
--   length rels_length (@SemiThueData.append_right _ _ a b c h) = length rels_length h := by
--   induction h with
--   | refl => rfl
--   | step c d h =>
--     rw [length_step]
--     unfold append_right
--     simp
--     rfl
--     unfold SemiThueData.append_right
--     rw [length_step]
--     sorry
--   | trans f g hf hg =>
--     unfold SemiThueData.append_right
--     rw [length_trans, length_trans, hf, hg]

private theorem length_eq_rec_left {a a' b : List α} (h : SemiThueData rels a b) (eq : a = a') :
    length rels_length (eq ▸ h : SemiThueData rels a' b) = length rels_length h := by
  subst eq; rfl

private theorem length_eq_rec_right {a b b' : List α} (h : SemiThueData rels a b) (eq : b = b') :
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
  | step c' d h =>
    unfold SemiThueData.append_right
    rw [length_eq_rec_left, length_eq_rec_right, length_step, length_step]
  | trans f g hf hg =>
    unfold SemiThueData.append_right
    rw [length_trans, length_trans, hf, hg]

@[simp]
theorem length_append_left_right (h : SemiThueData rels a b) :
    length rels_length (@SemiThueData.append_left_right _ _ a b c d h) = length rels_length h := by
  unfold SemiThueData.append_left_right
  simp

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
  unfold SemiThueData.of_rel
  rw [length_eq_rec_left, length_eq_rec_right]
  rfl

end SemiThueData


namespace SemiThueDataDerivation

noncomputable def toSemiThueData {a b : List α} (h : SemiThueDataDerivation rels a b) :
    SemiThueData rels a b := by
  induction h with
  | refl =>  exact SemiThueData.refl
  | step h1 h2 ih => exact ih.trans (SemiThueData.step _ _ h2)

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

-- noncomputable def trans_with_length
--     (h1 : SemiThueDataDerivation rels a b) (h2 : SemiThueDataDerivation rels b c) :
--     {h3 : SemiThueDataDerivation rels a c // length rels_length h3 = length rels_length h1 + length rels_length h2} := by
--   induction h2 with
--   | refl =>
--     use h1; simp
--   | step h1 h2 ih =>
--     have ⟨s1, ls1⟩ := ih h1
--     use SemiThueDataDerivation.step s1 h2
--     simp only [length, ls1, Nat.add_assoc]

-- @[simp]
-- def length_trans : length rels_length (@SemiThueDataDerivation.trans_with_length _ rels rels_length _ _ _ h1 h2).1 =
--     length rels_length h1 + length rels_length h2 :=
--   (@SemiThueDataDerivation.trans_with_length _ rels rels_length _ _ _ h1 h2).2


theorem toSemiThueData_length {a b : List α} (h : SemiThueDataDerivation rels a b) :
    SemiThueData.length rels_length (toSemiThueData h) = length rels_length h := by
  induction h with
  | refl => rfl
  | step h1 h2 ih =>
    rw [length_step, ← ih]
    unfold toSemiThueData
    rw [SemiThueData.length_trans, SemiThueData.length_step, Nat.add_left_cancel_iff]

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
    unfold toSemiThueDataDerivation
    simp only [SemiThueDataDerivation.length_trans]

-- noncomputable def SemiThueData.toSemiThueDataDerivation_with_length
--     {rels : List α → List α → Type} {rels_length : {a b : List α} → rels a b → ℕ} {a b : List α} (h : SemiThueData rels a b) :
--     {h1 : SemiThueDataDerivation rels a b //
--       SemiThueDataDerivation.length rels_length h1 = SemiThueData.length rels_length h}:= by
--   induction h with
--   | refl => use SemiThueDataDerivation.refl; rfl
--   | step _ _ h =>
--     use SemiThueDataDerivation.step SemiThueDataDerivation.refl h
--     simp
--   | trans _ _ ih1 ih2 =>
--     have ⟨s1, ls1⟩ := ih1
--     have ⟨s2, ls2⟩ := ih2
--     use (@SemiThueDataDerivation.trans_with_length _ rels rels_length _ _ _ s1 s2)
--     simp [ls1, ls2]
