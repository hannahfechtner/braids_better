import BraidProject.SemiThue_C
import BraidProject.Relations

namespace Braid

def SemiThue.grid_style.length (h : SemiThue grid_style a b) : ℕ :=
  match h with
  | SemiThue.refl => 0
  | SemiThue.step _ _ h =>
    match h with
    | grid_style.basic n => 1
    | grid_style.over n => 0
    | grid_style.up n => 0
    | grid_style.empty => 0
    | grid_style.apart h => 1
    | grid_style.close h => 1
  | SemiThue.trans h1 h2 => SemiThue.grid_style.length h1 + SemiThue.grid_style.length h2

def SemiThueDerivation.grid_style.length (h : SemiThueDerivation grid_style a b) : ℕ :=
  match h with
  | SemiThueDerivation.refl => 0
  | SemiThueDerivation.step h1 h =>
    match h with
    | grid_style.basic n => SemiThueDerivation.grid_style.length h1 + 1
    | grid_style.over n => SemiThueDerivation.grid_style.length h1 + 0
    | grid_style.up n => SemiThueDerivation.grid_style.length h1 + 0
    | grid_style.empty => SemiThueDerivation.grid_style.length h1 + 0
    | grid_style.apart h => SemiThueDerivation.grid_style.length h1 + 1
    | grid_style.close h => SemiThueDerivation.grid_style.length h1 + 1

noncomputable def SemiThueDerivation.grid_style.length_trans
  (h1 : SemiThueDerivation grid_style a b) (h2 : SemiThueDerivation grid_style b c) :
    {h3 : SemiThueDerivation grid_style a c //
    SemiThueDerivation.grid_style.length h3 =
    SemiThueDerivation.grid_style.length h1 + SemiThueDerivation.grid_style.length h2} := by
  induction h2
  · use h1
    simp [SemiThueDerivation.grid_style.length]
  rename_i d e f g h i j k
  specialize k h1
  rcases k with ⟨h4, len4⟩
  cases j with
  | basic n =>
    use h4.step (grid_style.basic n)
    rw [SemiThueDerivation.grid_style.length, SemiThueDerivation.grid_style.length,
      len4, add_assoc]
  | over n =>
    use h4.step (grid_style.over n)
    rw [SemiThueDerivation.grid_style.length, SemiThueDerivation.grid_style.length,
      len4, add_assoc]
  | up n =>
    use h4.step (grid_style.up n)
    rw [SemiThueDerivation.grid_style.length, SemiThueDerivation.grid_style.length,
      len4, add_assoc]
  | empty =>
    use h4.step (grid_style.empty)
    rw [SemiThueDerivation.grid_style.length, SemiThueDerivation.grid_style.length,
      len4, add_assoc]
  | apart h =>
    use h4.step (grid_style.apart h)
    rw [SemiThueDerivation.grid_style.length, SemiThueDerivation.grid_style.length,
      len4, add_assoc]
  | close h =>
    use h4.step (grid_style.close h)
    rw [SemiThueDerivation.grid_style.length, SemiThueDerivation.grid_style.length,
      len4, add_assoc]

noncomputable def SemiThue.grid_style.toSemiThueDerivation_with_length {a b}
    (h1 : SemiThue grid_style a b ) :
    {h2 : SemiThueDerivation grid_style a b //
    SemiThue.grid_style.length h1 = SemiThueDerivation.grid_style.length h2} := by
  induction h1
  · use SemiThueDerivation.refl
    simp [SemiThue.grid_style.length, SemiThueDerivation.grid_style.length]
  · rename_i c d e f h
    use SemiThueDerivation.step (SemiThueDerivation.refl) h
    cases h
    all_goals rw [SemiThue.grid_style.length, SemiThueDerivation.grid_style.length, SemiThueDerivation.grid_style.length]
  rename_i ih1 ih2
  use (SemiThueDerivation.grid_style.length_trans ih1.1 ih2.1).1
  rw [SemiThue.grid_style.length, (SemiThueDerivation.grid_style.length_trans ih1.1 ih2.1).2]
  aesop

noncomputable def SemiThueDerivation.grid_style.toSemiThue_with_length :
    (h1 : SemiThueDerivation grid_style a b) → (Σ h2 : SemiThue grid_style a b,
    PLift (SemiThue.grid_style.length h2 = SemiThueDerivation.grid_style.length h1)) := by
  intro h1
  induction h1
  · use SemiThue.refl
    constructor
    simp [SemiThue.grid_style.length, SemiThueDerivation.grid_style.length]
  rename_i h1 h2
  use h2.1.trans (SemiThue.step _ _ h1)
  constructor
  rw [SemiThue.grid_style.length, h2.2.1]
  cases h1
  all_goals rw [SemiThueDerivation.grid_style.length, SemiThue.grid_style.length]


noncomputable def SemiThue.grid_style.empty_w_length : {h : SemiThue grid_style [(none, false), (none, true)] [(none, true), (none, false)] // SemiThue.grid_style.length h = 0}:= by
  rw [← List.nil_append [(none, false), (none, true)], ← List.nil_append [(none, true), (none, false)],
    ← List.append_nil ([] ++ [(none, false), (none, true)]), ← List.append_nil ([] ++ [(none, true), (none, false)])]
  use SemiThue.step _ _ (grid_style.empty)
  simp [SemiThue.grid_style.length]

noncomputable def SemiThue.grid_style.top_bottom_w_length (i : ℕ) :
  {h : SemiThue grid_style [(none, false), (some i, true)] [(some i, true), (none, false)] // SemiThue.grid_style.length h = 0} := by
  rw [← List.nil_append [(none, false), (some i, true)], ← List.nil_append [(some i, true), (none, false)],
    ← List.append_nil ([] ++ [(none, false), (some i, true)]), ← List.append_nil ([] ++ [(some i, true), (none, false)])]
  use SemiThue.step _ _ (grid_style.up i)
  simp [SemiThue.grid_style.length]

noncomputable def SemiThue.grid_style.sides_w_length (i : ℕ) :
  {h : SemiThue grid_style [(some i, false), (none, true)] [(none, true), (some i, false)] // SemiThue.grid_style.length h = 0} := by
  rw [← List.nil_append [(some i, false), (none, true)], ← List.nil_append [(none, true), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (none, true)]), ← List.append_nil ([] ++ [(none, true), (some i, false)])]
  use SemiThue.step _ _ (grid_style.over i)
  simp [SemiThue.grid_style.length]

noncomputable def SemiThue.grid_style.top_left_w_length (i : ℕ) :
  {h : SemiThue grid_style [(some i, false), (some i, true)] [(none, true), (none, false)] // SemiThue.grid_style.length h = 1} := by
  rw [← List.nil_append [(none, true), (none, false)], ← List.nil_append [(some i, false), (some i, true)],
    ← List.append_nil ([] ++ [(none, true), (none, false)]), ← List.append_nil ([] ++ [(some i, false), (some i, true)])]
  use SemiThue.step _ _ (grid_style.basic i)
  simp [SemiThue.grid_style.length]

noncomputable def SemiThue.grid_style.adjacent_w_length (i j : ℕ) (hd : Nat.dist i j = 1) :
  {h : SemiThue grid_style [(some i, false), (some j, true)] [(some j, true), (some i, true), (some j, false), (some i, false)] // SemiThue.grid_style.length h = 1} := by
  rw [← List.nil_append [(some i, false), (some j, true)], ← List.nil_append [(some j, true), (some i, true), (some j, false), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (some j, true)]), ← List.append_nil ([] ++ [(some j, true), (some i, true), (some j, false), (some i, false)])]
  use SemiThue.step _ _ (grid_style.close hd)
  simp [SemiThue.grid_style.length]

noncomputable def SemiThue.grid_style.separated_w_length (i j : ℕ) (hd : Nat.dist i j ≥ 2) :
  {h : SemiThue grid_style [(some i, false), (some j, true)] [(some j, true), (some i, false)] // SemiThue.grid_style.length h = 1} := by
  rw [← List.nil_append [(some i, false), (some j, true)], ← List.nil_append [(some j, true), (some i, false)],
    ← List.append_nil ([] ++ [(some i, false), (some j, true)]), ← List.append_nil ([] ++ [(some j, true), (some i, false)])]
  use SemiThue.step _ _ (grid_style.apart hd)
  simp [SemiThue.grid_style.length]

noncomputable def SemiThue.grid_style.cons_w_length (h : SemiThue grid_style a b) :
    {h1 : SemiThue grid_style (c :: a) (c :: b) // SemiThue.grid_style.length h1 = SemiThue.grid_style.length h} := by
  induction h with
  | refl =>
    use SemiThue.refl
    simp [SemiThue.grid_style.length]
  | step _ _ h =>
    rw [← List.cons_append, ← List.cons_append]
    use SemiThue.step _ _ h
    rfl
  | trans h1 h2 ih1 ih2 =>
    use SemiThue.trans ih1.1 ih2.1
    simp [SemiThue.grid_style.length, ih1.2, ih2.2]

noncomputable def SemiThue.grid_style.append_left_w_length (c) (h : SemiThue grid_style a b) :
  {h1 : SemiThue grid_style (c ++ a) (c ++ b) // SemiThue.grid_style.length h1 = SemiThue.grid_style.length h} := by
  induction c
  · use h
    simp
  rename_i head tail ih
  have H := @SemiThue.grid_style.cons_w_length (tail ++ a) (tail ++ b) head ih.1
  use H.1
  erw [H.2, ih.2]

noncomputable def SemiThue.grid_style.concat_w_length (h : SemiThue grid_style a b) :
    {h1 : SemiThue grid_style (a ++ [c]) (b ++ [c]) //
    SemiThue.grid_style.length h1 = SemiThue.grid_style.length h} := by
  induction h with
  | refl =>
    use SemiThue.refl
    simp [SemiThue.grid_style.length]
  | step _ _ h =>
    rename_i e f g i
    rw [List.append_assoc, List.append_assoc _ i]
    use SemiThue.step _ _ h
    rfl
  | trans h1 h2 ih1 ih2 =>
    use SemiThue.trans ih1.1 ih2.1
    simp [SemiThue.grid_style.length, ih1.2, ih2.2]

noncomputable def SemiThue.grid_style.append_right_w_length (c) (h : SemiThue grid_style a b) :
  {h1 : SemiThue grid_style (a ++ c) (b ++ c) // SemiThue.grid_style.length h1 = SemiThue.grid_style.length h} := by
  induction c using List.reverseRecOn
  · rw [List.append_nil, List.append_nil]
    use h
  rename_i front caboose ih
  rw [← List.append_assoc, ← List.append_assoc]
  have H := (@SemiThue.grid_style.concat_w_length (a ++ front) (b ++ front) caboose ih.1)
  use H.1
  rw [H.2, ih.2]


theorem SemiThue.grid_style.cons : SemiThue.grid_style.length (@SemiThue.cons _ _ _ _ c h) = SemiThue.grid_style.length h := by
  induction h with
  | refl => simp [SemiThue.cons, SemiThue.grid_style.length]
  | step h => simp [SemiThue.cons, SemiThue.grid_style.length]
  | trans ha hb ih1 ih2 =>
    simp [SemiThue.grid_style.length, SemiThue.cons, ← ih1, ← ih2]

def SemiThue.reversing.length (h : SemiThue reversing a b) : ℕ :=
  match h with
  | SemiThue.refl => 0
  | SemiThue.step _ _ h => 1
  | SemiThue.trans h1 h2 => SemiThue.reversing.length h1 + SemiThue.reversing.length h2

def SemiThueDerivation.reversing.length (h : SemiThueDerivation reversing a b) : ℕ :=
  match h with
  | SemiThueDerivation.refl => 0
  | SemiThueDerivation.step h1 h => SemiThueDerivation.reversing.length h1 + 1

noncomputable def SemiThueDerivation.reversing.length_trans
  (h1 : SemiThueDerivation reversing a b) (h2 : SemiThueDerivation reversing b c) :
    (h3 : SemiThueDerivation reversing a c) ×
    PLift (SemiThueDerivation.reversing.length h3 =
    SemiThueDerivation.reversing.length h1 + SemiThueDerivation.reversing.length h2) := by
  induction h2
  · use h1
    constructor
    simp [SemiThueDerivation.reversing.length]
  rename_i d e f g h i j k
  specialize k h1
  rcases k with ⟨h4, len4⟩
  cases j with
  | basic n =>
    use h4.step (reversing.basic n)
    constructor
    rw [SemiThueDerivation.reversing.length, SemiThueDerivation.reversing.length, len4.1, add_assoc]
  | apart h =>
    use h4.step (reversing.apart h)
    constructor
    rw [SemiThueDerivation.reversing.length, SemiThueDerivation.reversing.length, len4.1, add_assoc]
  | close h =>
    use h4.step (reversing.close h)
    constructor
    rw [SemiThueDerivation.reversing.length, SemiThueDerivation.reversing.length, len4.1, add_assoc]

noncomputable def  SemiThue.reversing.toSemiThueDerivation_with_length {a b}
    (h1 : SemiThue reversing a b ) : (Σ h2 : SemiThueDerivation reversing a b,
    PLift (SemiThue.reversing.length h1 = SemiThueDerivation.reversing.length h2) ):= by
  induction h1
  · use SemiThueDerivation.refl
    constructor
    simp [SemiThue.reversing.length, SemiThueDerivation.reversing.length]
  · rename_i h
    use SemiThueDerivation.step SemiThueDerivation.refl h
    constructor
    cases h
    all_goals rw [SemiThue.reversing.length, SemiThueDerivation.reversing.length, SemiThueDerivation.reversing.length]
  rename_i ih1 ih2
  use (SemiThueDerivation.reversing.length_trans ih1.1 ih2.1).1
  constructor
  rw [SemiThue.reversing.length, (SemiThueDerivation.reversing.length_trans ih1.1 ih2.1).2.1]
  exact Mathlib.Tactic.Ring.add_congr ih1.2.1 ih2.2.1 rfl
