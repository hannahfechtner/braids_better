import BraidProject.PresentedMonoid_mine

/- this I have barely looked at, just a template -/

open FreeMonoid'

def Phi (n m i : ℕ) : FreeMonoid' ℕ := sorry

def Psi (n m i : ℕ) : FreeMonoid' ℕ := sorry

-- for the braid with infinitely many strands
inductive fused_rels_m_inf : FreeMonoid' ℕ → FreeMonoid' ℕ → Prop
  | adjacent (i : ℕ): fused_rels_m_inf (of i * of (i+1) * of i) (of (i+1) * of i * of (i+1))
  | separated (i j : ℕ) (h : i +2 ≤ j): fused_rels_m_inf (of i * of j) (of j * of i)
  | cross_far_h (i j n m : ℕ) (h : j + 2 ≤ i) : fused_rels_m_inf (of j * Phi n m i) (Phi n m i * of j)
  | cross_far_s (i j n m : ℕ) (h : j + 2 ≤ i) : fused_rels_m_inf (of j * Psi n m i) (Psi n m i * of j)
  | cross_close_h (i j n m : ℕ) (h : i + n ≤ j) : fused_rels_m_inf (of j * Phi n m i) (Phi n m i * of (j - n + m))
  | cross_close_s (i j n m : ℕ) (h : i + n ≤ j) : fused_rels_m_inf (of j * Psi n m i) (Psi n m i * of (j - n + m))
