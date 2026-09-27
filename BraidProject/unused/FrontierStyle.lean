import BraidProject.DataCarrying.SemiThue
import BraidProject.PartialGrid.Basic

namespace Braid

namespace PartialGrid
open SignedList
inductive FrontierStyle : List (Option ℕ × Bool) → List (Option ℕ × Bool) →
  List (Option ℕ × Bool) → Type
  | skeleton (a b) (ha : a.length > 0) (ha1 : is_false a) (hb : b.length > 0) (hb : is_true b ):
      FrontierStyle a b (a ++ b)
  | empty (h : FrontierStyle a b c) (hc : c = c1 ++ [(none, false), (none, true)] ++ c2) :
      FrontierStyle a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | top_bottom (i : ℕ) (h : FrontierStyle a b c) (hc : c = c1 ++ [(none, false), (some i, true)] ++ c2) :
      FrontierStyle a b (c1 ++ [(some i, true), (none, false)] ++ c2)
  | sides (i : ℕ) (h : FrontierStyle a b c) (hc : c = (c1 ++ [(some i, false), (none, true)] ++ c2)) :
      FrontierStyle a b (c1 ++ [(none, true), (some i, false)] ++ c2)
  | top_left (i : ℕ) (h : FrontierStyle a b c) (hc : c = (c1 ++ [(some i, false), (some i, true)] ++ c2)) :
      FrontierStyle a b (c1 ++ [(none, true), (none, false)] ++ c2)
  | adjacent (i j : ℕ) (hd : Nat.dist i j = 1) (h : FrontierStyle a b c)
      (hc : c = (c1 ++ [(some i, false), (some j, true)] ++ c2)) :
      FrontierStyle a b (c1 ++ [(some j, true), (some i, true), (some j, false), (some i, false)] ++ c2)
  | separated (i k : ℕ) (hd : Nat.dist i k ≥ 2) (h : FrontierStyle a b c)
     (hc : c = c1 ++ [(some i, false), (some k, true)] ++ c2) :
      FrontierStyle a b (c1 ++ [(some k, true), (some i, false)] ++ c2)

namespace FrontierStyle

def length (h : FrontierStyle a b c) : Nat :=
  match h with
  | FrontierStyle.skeleton _ _ _ _ _ _ => 0
  | FrontierStyle.empty h _ => FrontierStyle.length h
  | FrontierStyle.top_bottom i h _ => FrontierStyle.length h
  | FrontierStyle.sides _ h _ => FrontierStyle.length h
  | FrontierStyle.top_left _ h _ => FrontierStyle.length h + 1
  | FrontierStyle.adjacent _ _ _ h _ => FrontierStyle.length h + 1
  | FrontierStyle.separated _ _ _ h _ => FrontierStyle.length h + 1

noncomputable def is_false_left_side (h : FrontierStyle a b c) : is_false a := by
  induction h; all_goals assumption

noncomputable def is_true_top_side (h : FrontierStyle a b c) : is_true b := by
  induction h; all_goals assumption
