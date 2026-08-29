import BraidProject.SemiThue_C
import BraidProject.Relations


namespace Braid

namespace SemiThueData

def length {a b : List α} {rels : List α → List α → Type}
  (rels_length : {a : List α} → {b : List α} → rels a b → ℕ) (h : SemiThueData rels a b) : ℕ := match h with
| SemiThueData.refl => 0
| SemiThueData.step _ _ h1 => rels_length h1
| SemiThueData.trans h1 h2 => length rels_length h1 + length rels_length h2

@[simp]
def length_refl : length rels_length (@SemiThueData.refl _ _ a) = 0 := by
  rfl

@[simp]
def length_trans : length rels_length (SemiThueData.trans h1 h2) = length rels_length h1 + length rels_length h2 := by
  rfl

@[simp]
def length_step {c d : List α}: length rels_length (SemiThueData.step c d h) = rels_length h := by
  rfl

def grid_style.length (h : SemiThueData grid_style a b) : ℕ :=
  SemiThueData.length Braid.grid_style.length h

@[simp]
theorem grid_style.length_refl : grid_style.length (@SemiThueData.refl _ _ a) = 0 := by
  rfl

@[simp]
theorem grid_style.length_trans (h1 : SemiThueData grid_style a b) (h2 : SemiThueData grid_style b c) :
  grid_style.length (SemiThueData.trans h1 h2) = grid_style.length h1 + grid_style.length h2 := by rfl

@[simp]
theorem grid_style.length_step (h : grid_style a b) {c d : List (Option ℕ × Bool)}: grid_style.length (SemiThueData.step c d h) = Braid.grid_style.length h := by
  rfl

end SemiThueData

namespace SemiThueDataDerivation

def length {rels : List α → List α → Type} (rels_length : {a : List α} → {b : List α} → rels a b → ℕ) (h : SemiThueDataDerivation rels a b) : ℕ := match h with
| SemiThueDataDerivation.refl => 0
| SemiThueDataDerivation.step h1 h2 => SemiThueDataDerivation.length rels_length h1 + rels_length h2


def grid_style.length (h : SemiThueDataDerivation grid_style a b) : ℕ :=
  SemiThueDataDerivation.length Braid.grid_style.length h

@[simp]
theorem grid_style.length_refl : grid_style.length (@SemiThueDataDerivation.refl _ _ a) = 0 := by
  rfl

@[simp]
theorem grid_style.length_step (h1 : SemiThueDataDerivation grid_style a (c ++ b ++ d)) (h2 : grid_style b e) :
  grid_style.length (SemiThueDataDerivation.step h1 h2) = grid_style.length h1 + Braid.grid_style.length h2 := by
  rfl

noncomputable def grid_style.length_trans
  (h1 : SemiThueDataDerivation grid_style a b) (h2 : SemiThueDataDerivation grid_style b c) :
    {h3 : SemiThueDataDerivation grid_style a c //
    SemiThueDataDerivation.grid_style.length h3 =
    SemiThueDataDerivation.grid_style.length h1 + SemiThueDataDerivation.grid_style.length h2} := by
  induction h2
  · use h1
    simp [SemiThueDataDerivation.length, SemiThueDataDerivation.grid_style.length]
  rename_i d e f g h i j k
  specialize k h1
  rcases k with ⟨h4, len4⟩
  cases j with
  | basic n =>
    use h4.step (grid_style.basic n)
    rw [SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.grid_style.length,
      SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.length,
      ← SemiThueDataDerivation.grid_style.length,
      len4, add_assoc]
    rfl
  | over n =>
    use h4.step (grid_style.over n)
    rw [SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.grid_style.length,
      SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.length,
      ← SemiThueDataDerivation.grid_style.length,
      len4, add_assoc]
    rfl
  | up n =>
    use h4.step (grid_style.up n)
    rw [SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.grid_style.length,
      SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.length,
      ← SemiThueDataDerivation.grid_style.length,
      len4, add_assoc]
    rfl
  | empty =>
    use h4.step (grid_style.empty)
    rw [SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.grid_style.length,
      SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.length,
      ← SemiThueDataDerivation.grid_style.length,
      len4, add_assoc]
    rfl
  | apart h =>
    use h4.step (grid_style.apart h)
    rw [SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.grid_style.length,
      SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.length,
      ← SemiThueDataDerivation.grid_style.length,
      len4, add_assoc]
    rfl
  | close h =>
    use h4.step (grid_style.close h)
    rw [SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.grid_style.length,
      SemiThueDataDerivation.grid_style.length, SemiThueDataDerivation.length,
      ← SemiThueDataDerivation.grid_style.length,
      len4, add_assoc]
    rfl

/-- A `@[simp]` version of `length_trans`'s `.2`, so `simp` rewrites the length of the result. -/
@[simp]
theorem grid_style.length_length_trans
  (h1 : SemiThueDataDerivation grid_style a b) (h2 : SemiThueDataDerivation grid_style b c) :
    SemiThueDataDerivation.grid_style.length (SemiThueDataDerivation.grid_style.length_trans h1 h2).1 =
      SemiThueDataDerivation.grid_style.length h1 + SemiThueDataDerivation.grid_style.length h2 :=
  (SemiThueDataDerivation.grid_style.length_trans h1 h2).2

end SemiThueDataDerivation

noncomputable def SemiThueData.grid_style.toSemiThueDataDerivation_with_length {a b}
    (h1 : SemiThueData grid_style a b ) :
    {h2 : SemiThueDataDerivation grid_style a b //
    SemiThueData.grid_style.length h1 = SemiThueDataDerivation.grid_style.length h2} := by
  induction h1
  · use SemiThueDataDerivation.refl
    simp [SemiThueData.grid_style.length, SemiThueDataDerivation.grid_style.length,
      SemiThueData.length, SemiThueDataDerivation.length]
  · rename_i c d e f h
    use SemiThueDataDerivation.step (SemiThueDataDerivation.refl) h
    cases h
    all_goals rw [SemiThueData.grid_style.length, SemiThueDataDerivation.grid_style.length]; rfl
  rename_i ih1 ih2
  use (SemiThueDataDerivation.grid_style.length_trans ih1.1 ih2.1).1
  rw [SemiThueData.grid_style.length, SemiThueData.length, ← SemiThueData.grid_style.length, (SemiThueDataDerivation.grid_style.length_trans ih1.1 ih2.1).2,
    ]
  aesop

noncomputable def SemiThueDataDerivation.grid_style.toSemiThueData_with_length :
    (h1 : SemiThueDataDerivation grid_style a b) → (Σ h2 : SemiThueData grid_style a b,
    PLift (SemiThueData.grid_style.length h2 = SemiThueDataDerivation.grid_style.length h1)) := by
  intro h1
  induction h1
  · use SemiThueData.refl
    constructor
    rfl
  rename_i h1 h2
  use h2.1.trans (SemiThueData.step _ _ h1)
  constructor
  simp [h2.2.1]

noncomputable def SemiThueData.grid_style.empty_w_length : {h : SemiThueData grid_style [(none, false), (none, true)] [(none, true), (none, false)] // SemiThueData.grid_style.length h = 0}:= by
  rw [← List.nil_append [(none, false), (none, true)], ← List.nil_append [(none, true), (none, false)],
    ← List.append_nil ([] ++ [(none, false), (none, true)]), ← List.append_nil ([] ++ [(none, true), (none, false)])]
  use SemiThueData.step _ _ (grid_style.empty)
  simp [SemiThueData.grid_style.length]; rfl

noncomputable def SemiThueData.grid_style.top_bottom_w_length (i : ℕ) :
  {h : SemiThueData grid_style [(none, false), (some i, true)] [(some i, true), (none, false)] // SemiThueData.grid_style.length h = 0} := by
  rw [← List.nil_append [(none, false), (some i, true)], ← List.nil_append [(some i, true), (none, false)],
    ← List.append_nil ([] ++ [(none, false), (some i, true)]), ← List.append_nil ([] ++ [(some i, true), (none, false)])]
  use SemiThueData.step _ _ (grid_style.up i)
  simp [SemiThueData.grid_style.length]; rfl

noncomputable def SemiThueData.grid_style.sides_w_length (i : ℕ) :
  {h : SemiThueData grid_style [(some i, false), (none, true)] [(none, true), (some i, false)] // SemiThueData.grid_style.length h = 0} := by
  rw [← List.nil_append [(some i, false), (none, true)], ← List.nil_append [(none, true), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (none, true)]), ← List.append_nil ([] ++ [(none, true), (some i, false)])]
  use SemiThueData.step _ _ (grid_style.over i)
  simp [SemiThueData.grid_style.length]; rfl

noncomputable def SemiThueData.grid_style.top_left_w_length (i : ℕ) :
  {h : SemiThueData grid_style [(some i, false), (some i, true)] [(none, true), (none, false)] // SemiThueData.grid_style.length h = 1} := by
  rw [← List.nil_append [(none, true), (none, false)], ← List.nil_append [(some i, false), (some i, true)],
    ← List.append_nil ([] ++ [(none, true), (none, false)]), ← List.append_nil ([] ++ [(some i, false), (some i, true)])]
  use SemiThueData.step _ _ (grid_style.basic i)
  simp [SemiThueData.grid_style.length]; rfl

noncomputable def SemiThueData.grid_style.adjacent_w_length (i j : ℕ) (hd : Nat.dist i j = 1) :
  {h : SemiThueData grid_style [(some i, false), (some j, true)] [(some j, true), (some i, true), (some j, false), (some i, false)] // SemiThueData.grid_style.length h = 1} := by
  rw [← List.nil_append [(some i, false), (some j, true)], ← List.nil_append [(some j, true), (some i, true), (some j, false), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (some j, true)]), ← List.append_nil ([] ++ [(some j, true), (some i, true), (some j, false), (some i, false)])]
  use SemiThueData.step _ _ (grid_style.close hd)
  simp [SemiThueData.grid_style.length]; rfl

noncomputable def SemiThueData.grid_style.separated_w_length (i j : ℕ) (hd : Nat.dist i j ≥ 2) :
  {h : SemiThueData grid_style [(some i, false), (some j, true)] [(some j, true), (some i, false)] // SemiThueData.grid_style.length h = 1} := by
  rw [← List.nil_append [(some i, false), (some j, true)], ← List.nil_append [(some j, true), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (some j, true)]), ← List.append_nil ([] ++ [(some j, true), (some i, false)])]
  use SemiThueData.step _ _ (grid_style.apart hd)
  simp [SemiThueData.grid_style.length]; rfl

noncomputable def SemiThueData.grid_style.cons_w_length (h : SemiThueData grid_style a b) :
    {h1 : SemiThueData grid_style (c :: a) (c :: b) // SemiThueData.grid_style.length h1 = SemiThueData.grid_style.length h} := by
  induction h with
  | refl =>
    use SemiThueData.refl
    rfl
  | step _ _ h =>
    rw [← List.cons_append, ← List.cons_append]
    use SemiThueData.step _ _ h
    rfl
  | trans h1 h2 ih1 ih2 =>
    use SemiThueData.trans ih1.1 ih2.1
    unfold SemiThueData.grid_style.length at ih1 ih2
    simp [SemiThueData.grid_style.length, SemiThueData.length, ih1.2, ih2.2]

@[simp] theorem SemiThueData.grid_style.length_cons_w_length (h : SemiThueData grid_style a b) :
    SemiThueData.grid_style.length (@SemiThueData.grid_style.cons_w_length _ _ c h).1 =
      SemiThueData.grid_style.length h :=
  (SemiThueData.grid_style.cons_w_length h).2

noncomputable def SemiThueData.grid_style.append_left_w_length (c) (h : SemiThueData grid_style a b) :
  {h1 : SemiThueData grid_style (c ++ a) (c ++ b) // SemiThueData.grid_style.length h1 = SemiThueData.grid_style.length h} := by
  induction c
  · use h
    simp
  rename_i head tail ih
  have H := @SemiThueData.grid_style.cons_w_length (tail ++ a) (tail ++ b) head ih.1
  use H.1
  erw [H.2, ih.2]

@[simp] theorem SemiThueData.grid_style.length_append_left_w_length (c) (h : SemiThueData grid_style a b) :
    SemiThueData.grid_style.length (SemiThueData.grid_style.append_left_w_length c h).1 =
      SemiThueData.grid_style.length h :=
  (SemiThueData.grid_style.append_left_w_length c h).2

noncomputable def SemiThueData.grid_style.concat_w_length (h : SemiThueData grid_style a b) :
    {h1 : SemiThueData grid_style (a ++ [c]) (b ++ [c]) //
    SemiThueData.grid_style.length h1 = SemiThueData.grid_style.length h} := by
  induction h with
  | refl =>
    use SemiThueData.refl
    rfl
  | step _ _ h =>
    rename_i i
    rw [List.append_assoc, List.append_assoc _ i]
    use SemiThueData.step _ _ h
    rfl
  | trans h1 h2 ih1 ih2 =>
    use SemiThueData.trans ih1.1 ih2.1
    unfold SemiThueData.grid_style.length at ih1 ih2
    simp [SemiThueData.grid_style.length, SemiThueData.length, ih1.2, ih2.2]

@[simp] theorem SemiThueData.grid_style.length_concat_w_length (h : SemiThueData grid_style a b) :
    SemiThueData.grid_style.length (@SemiThueData.grid_style.concat_w_length _ _ c h).1 =
      SemiThueData.grid_style.length h :=
  (SemiThueData.grid_style.concat_w_length h).2

noncomputable def SemiThueData.grid_style.append_right_w_length (c) (h : SemiThueData grid_style a b) :
  {h1 : SemiThueData grid_style (a ++ c) (b ++ c) // SemiThueData.grid_style.length h1 = SemiThueData.grid_style.length h} := by
  induction c using List.reverseRecOn
  · rw [List.append_nil, List.append_nil]
    use h
  rename_i front caboose ih
  rw [← List.append_assoc, ← List.append_assoc]
  have H := (@SemiThueData.grid_style.concat_w_length (a ++ front) (b ++ front) caboose ih.1)
  use H.1
  rw [H.2, ih.2]

@[simp] theorem SemiThueData.grid_style.length_append_right_w_length (c) (h : SemiThueData grid_style a b) :
    SemiThueData.grid_style.length (SemiThueData.grid_style.append_right_w_length c h).1 =
      SemiThueData.grid_style.length h :=
  (SemiThueData.grid_style.append_right_w_length c h).2


@[simp]
theorem SemiThueData.grid_style.cons : SemiThueData.grid_style.length (@SemiThueData.cons _ _ _ _ c h) = SemiThueData.grid_style.length h := by
  induction h with
  | refl => simp [SemiThueData.cons, SemiThueData.grid_style.length, SemiThueData.length]
  | step h => simp [SemiThueData.cons, SemiThueData.grid_style.length, SemiThueData.length]
  | trans ha hb ih1 ih2 =>
    unfold SemiThueData.grid_style.length at ih1 ih2
    simp [SemiThueData.grid_style.length, SemiThueData.length, SemiThueData.cons, ← ih1, ← ih2]

def SemiThueData.reversing.length (h : SemiThueData reversing a b) : ℕ :=
  match h with
  | SemiThueData.refl => 0
  | SemiThueData.step _ _ h => 1
  | SemiThueData.trans h1 h2 => SemiThueData.reversing.length h1 + SemiThueData.reversing.length h2

def SemiThueDataDerivation.reversing.length (h : SemiThueDataDerivation reversing a b) : ℕ :=
  match h with
  | SemiThueDataDerivation.refl => 0
  | SemiThueDataDerivation.step h1 h => SemiThueDataDerivation.reversing.length h1 + 1

noncomputable def SemiThueDataDerivation.reversing.length_trans
  (h1 : SemiThueDataDerivation reversing a b) (h2 : SemiThueDataDerivation reversing b c) :
    (h3 : SemiThueDataDerivation reversing a c) ×
    PLift (SemiThueDataDerivation.reversing.length h3 =
    SemiThueDataDerivation.reversing.length h1 + SemiThueDataDerivation.reversing.length h2) := by
  induction h2
  · use h1
    constructor
    simp [SemiThueDataDerivation.reversing.length]
  rename_i d e f g h i j k
  specialize k h1
  rcases k with ⟨h4, len4⟩
  cases j with
  | basic n =>
    use h4.step (reversing.basic n)
    constructor
    rw [SemiThueDataDerivation.reversing.length, SemiThueDataDerivation.reversing.length, len4.1, add_assoc]
  | apart h =>
    use h4.step (reversing.apart h)
    constructor
    rw [SemiThueDataDerivation.reversing.length, SemiThueDataDerivation.reversing.length, len4.1, add_assoc]
  | close h =>
    use h4.step (reversing.close h)
    constructor
    rw [SemiThueDataDerivation.reversing.length, SemiThueDataDerivation.reversing.length, len4.1, add_assoc]

noncomputable def  SemiThueData.reversing.toSemiThueDataDerivation_with_length {a b}
    (h1 : SemiThueData reversing a b ) : (Σ h2 : SemiThueDataDerivation reversing a b,
    PLift (SemiThueData.reversing.length h1 = SemiThueDataDerivation.reversing.length h2) ):= by
  induction h1
  · use SemiThueDataDerivation.refl
    constructor
    simp [SemiThueData.reversing.length, SemiThueDataDerivation.reversing.length]
  · rename_i h
    use SemiThueDataDerivation.step SemiThueDataDerivation.refl h
    constructor
    cases h
    all_goals rw [SemiThueData.reversing.length, SemiThueDataDerivation.reversing.length, SemiThueDataDerivation.reversing.length]
  rename_i ih1 ih2
  use (SemiThueDataDerivation.reversing.length_trans ih1.1 ih2.1).1
  constructor
  rw [SemiThueData.reversing.length, (SemiThueDataDerivation.reversing.length_trans ih1.1 ih2.1).2.1]
  exact Mathlib.Tactic.Ring.add_congr ih1.2.1 ih2.2.1 rfl

end Braid
