import BraidProject.Grids_C
import BraidProject.SemiThue_C
import BraidProject.TrueFalse_C
import BraidProject.PartialGrid_bounded

inductive pgf : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → Type
  | skeleton (a b) (ha : a.length > 0) (ha1 : is_false a) (hb : b.length > 0) (hb : is_true b ):
      pgf a b (a ++ b)
  | empty (h : pgf a b c) (hc : c = c1 ++ [(none, false), (none, true)] ++ c2) :
      pgf a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | top_bottom (i : ℕ) (h : pgf a b c) (hc : c = c1 ++ [(none, false), (some i, true)] ++ c2) :
      pgf a b (c1 ++ [(some i, true), (none, false)] ++ c2)
  | sides (i : ℕ) (h : pgf a b c) (hc : c = (c1 ++ [(some i, false), (none, true)] ++ c2)) :
      pgf a b (c1 ++ [(none, true), (some i, false)] ++ c2)
  | top_left (i : ℕ) (h : pgf a b c) (hc : c = (c1 ++ [(some i, false), (some i, true)] ++ c2)) :
      pgf a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | adjacent (i j : ℕ) (hd : Nat.dist i j = 1) (h : pgf a b c)
      (hc : c = (c1 ++ [(some i, false), (some j, true)] ++ c2)) :
      pgf a b (c1 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c2)
  | separated (i k : ℕ) (hd : Nat.dist i k ≥ 2) (h : pgf a b c)
     (hc : c = c1 ++ [(some i, false), (some k, true)] ++ c2) :
      pgf a b (c1 ++ [(some k, true), (some i, false)] ++ c2)

def remove_label (L : List (Option ℕ × Bool)) := List.map (fun x => x.2) L

inductive pgf' :
  {h : (List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → Type) // True}
  | skeleton (a b) (ha : a.length > 0) (ha1 : is_false a) (hb : b.length > 0) (hb : is_true b ):
      pgf' a b (a ++ b)
  | empty (h : pgf' a b c) (hc : c = c1 ++ [(none, false), (none, true)] ++ c2) :
      pgf' a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | top_bottom (i : ℕ) (h : pgf' a b c) (hc : c = c1 ++ [(none, false), (some i, true)] ++ c2) :
      pgf' a b (c1 ++ [(some i, true), (none, false)] ++ c2)
  | sides (i : ℕ) (h : pgf' a b c) (hc : c = (c1 ++ [(some i, false), (none, true)] ++ c2)) :
      pgf' a b (c1 ++ [(none, true), (some i, false)] ++ c2)
  | top_left (i : ℕ) (h : pgf' a b c) (hc : c = (c1 ++ [(some i, false), (some i, true)] ++ c2)) :
      pgf' a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | adjacent (i j : ℕ) (hd : Nat.dist i j = 1) (h : pgf' a b c)
      (hc : c = (c1 ++ [(some i, false), (some j, true)] ++ c2)) :
      pgf' a b (c1 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c2)
  | separated (i k : ℕ) (hd : Nat.dist i k ≥ 2) (h : pgf' a b c)
     (hc : c = c1 ++ [(some i, false), (some k, true)] ++ c2) :
      pgf' a b (c1 ++ [(some k, true), (some i, false)] ++ c2)
theorem uniqueness {a b c : List (Option ℕ × Bool)} (h : pgf a b c) :
  ∀ (h : pgf a b c1), remove_label c = remove_label c1 → c = c1 := by
  induction h with
  | skeleton ha ha1 hb hb => sorry
  | empty h hc ih => sorry
  | top_bottom i h hc ih => sorry
  | sides i h hc ih => sorry
  | top_left i h hc ih => sorry
  | adjacent i j hd h hc ih => sorry
  | separated i k hd h hc ih => sorry
