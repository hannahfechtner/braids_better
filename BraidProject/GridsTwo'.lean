import BraidProject.Grids'
set_option maxRecDepth 10000
open FreeMonoid Braid

namespace Grid

namespace DeterminativeSpine

private theorem one_one_helper (h : grid a b c d) (ha : a = 1) (hb : b = 1) : c = 1 ∧ d = 1 := by
  induction h with
  | empty => exact ⟨rfl, rfl⟩
  | top_bottom i => exact ⟨hb, rfl⟩
  | sides i => exact ⟨rfl, ha⟩
  | top_left i => exact ⟨rfl, rfl⟩
  | adjacent i k h => simp only [of_ne_one] at ha
  | separated i j h => simp only [of_ne_one] at ha
  | vertical h1 h2 h1_ih h2_ih =>
    have H := FreeMonoid.prod_eq_one ha
    aesop
  | horizontal h1 h2 h1_ih h2_ih =>
    have H := FreeMonoid.prod_eq_one hb
    aesop

theorem one_one (h1 : grid 1 1 c d) : c = 1 ∧ d = 1 := one_one_helper h1 rfl rfl

theorem one_generator {i : ℕ} (h : grid 1 (of i) c d) : c = of i ∧ d = 1 := by
  generalize hb : of i = b at h
  generalize ha : (1 : FreeMonoid ℕ) = a at h
  induction h with
  | empty => exact (of_ne_one _ hb).elim
  | top_bottom i => exact ⟨rfl, rfl⟩
  | sides i => exact (of_ne_one _ ha.symm).elim
  | top_left i => exact (of_ne_one _ ha.symm).elim
  | adjacent i k h => exact (of_ne_one _ ha.symm).elim
  | separated i j h => exact (of_ne_one _ ha.symm).elim
  | vertical h1 h2 h1_ih h2_ih =>
    have h3 := (FreeMonoid.prod_eq_one ha.symm)
    specialize h1_ih hb h3.1.symm
    specialize h2_ih (hb.trans h1_ih.1.symm) h3.2.symm
    rw [h2_ih.1, h2_ih.2, h1_ih.1, h1_ih.2]
    exact ⟨rfl, rfl⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rcases FreeMonoid.prod_eq_of hb.symm with h3 | h4
    · rw [h3.1, ← ha] at h1
      have H := one_one h1
      specialize h2_ih h3.2.symm H.2.symm
      rw [← ha, h3.1, one_mul, H.1, one_mul, h2_ih.1]
      exact ⟨rfl, h2_ih.2.trans H.2⟩
    rename_i e f g j k l m
    rw [← ha, h4.1, h4.2, mul_one]
    specialize h1_ih h4.1.symm ha
    rw [h4.2, h1_ih.2.trans ha.symm] at h2
    have H := one_one h2
    rw [H.1, mul_one, h1_ih.1]
    exact ⟨h4.1, H.2⟩

theorem generator_one (h : grid (of i) 1 c d) : c = 1 ∧ d = of i := by
  apply Grid.swap at h
  apply one_generator at h
  aesop

private theorem generator_generator_same_helper (h : grid a b c d) :
  a = FreeMonoid.of i → b = FreeMonoid.of i → c = 1 ∧ d = 1 := by
  induction h with
  | empty => exact fun _ _ => ⟨rfl, rfl⟩
  | top_bottom i =>
    intro h1
    simp only [one_ne_of] at h1
  | sides i =>
    intro h1 h2
    simp only [one_ne_of] at h2
  | top_left i => exact fun _ _ => ⟨rfl, rfl⟩
  | adjacent i k h =>
    intro h1 h2
    rw [FreeMonoid.of_injective h1, FreeMonoid.of_injective h2] at h
    simp only [Nat.dist_self, zero_ne_one] at h
  | separated i j h =>
    intro h1 h2
    rw [FreeMonoid.of_injective h1, FreeMonoid.of_injective h2] at h
    simp only [Nat.dist_self, gt_iff_lt, not_lt_zero'] at h
  | vertical h1 h2 h1_ih h2_ih =>
    intro h3 h4
    rw [h4] at h1
    rcases FreeMonoid.prod_eq_of h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have ⟨hc, hd⟩ := one_generator h1
      specialize h2_ih rfl hc
      rw [h2_ih.1, h2_ih.2, hd]
      simp only [mul_one, and_self]
    specialize h1_ih rfl h4
    rw [h1_ih.1] at h2
    have ⟨hf, hg⟩ := one_one h2
    rw [hf, hg, h1_ih.2]
    simp only [mul_one, and_self]
  | horizontal h1 h2 h1_ih h2_ih =>
    intro h3 h4
    rw [h3] at h1
    rcases FreeMonoid.prod_eq_of h4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have ⟨hc, hd⟩ := generator_one h1
      specialize h2_ih hd rfl
      rw [h2_ih.1, h2_ih.2, hc]
      simp only [one_mul, and_self]
    specialize h1_ih h3 rfl
    rw [h1_ih.2] at h2
    have ⟨hf, hg⟩ := one_one h2
    rw [hf, hg, h1_ih.1]
    simp only [one_mul, and_self]

theorem generator_generator_same (h : grid (of i) (of i) c d) :
    c = 1 ∧ d = 1 := generator_generator_same_helper h rfl rfl

theorem one_word (h : grid 1 b c d) : c = b ∧ d = 1 := by
  induction b using FreeMonoid.inductionOn' generalizing c with
  | one => exact one_one h
  | mul_of head tail ih =>
    rcases Grid.splittable_vertically h (of head) tail rfl with ⟨u, c₁, c₂, g1, g2, c_is⟩
    have ⟨hc, hd⟩ := one_generator g1
    rw [hd] at g2
    specialize ih g2
    aesop

theorem word_one (h : grid a 1 c d) : c = 1 ∧ d = a := by
  apply Grid.swap at h
  apply one_word at h
  aesop

private theorem word_word_same_helper (h : grid a b c d) : a = b → c = 1 ∧ d = 1 := by
  induction a using FreeMonoid.inductionOn' generalizing b c d with
  | one =>
    intro hb
    rw [← hb] at h
    exact one_one h
  | mul_of head tail ih =>
    intro b_is
    rcases Grid.splittable_horizontally h (of head) tail rfl with ⟨u, d₁, d₂, g1, g2, d_is⟩
    rw [← b_is] at g1
    rcases Grid.splittable_vertically g1 _ _ rfl with ⟨u', c₁, c₂, g1', g1'', c_is⟩
    have ⟨hc₁, hu⟩ := generator_generator_same g1'
    rw [hc₁, one_mul] at c_is
    rw [hu] at g1''
    have ⟨hc₂, hd₁⟩ := one_word g1''
    rw [hc₂] at c_is
    rw [c_is] at g2
    specialize ih g2 rfl
    rw [d_is, hd₁, one_mul]
    exact ih

theorem word_word_same (h : grid a a c d) : c = 1 ∧ d = 1 := word_word_same_helper h rfl

private theorem generator_generator_close_helper (h : grid a b c d) (ha : a = of i) (hb : b = of j)
    (hij : i.dist j = 1) : c = of j * of i ∧ d = of i * of j := by
  induction h with
  | empty => simp only [one_ne_of] at ha
  | top_bottom i => simp only [one_ne_of] at ha
  | sides i => simp only [one_ne_of] at hb
  | top_left i =>
    rw [← FreeMonoid.of_injective ha, ← FreeMonoid.of_injective hb] at hij
    simp only [Nat.dist_self, zero_ne_one] at hij
  | adjacent i k h =>
    rw [FreeMonoid.of_injective ha, FreeMonoid.of_injective hb]
    simp only [and_self]
  | separated i j h =>
    rw [FreeMonoid.of_injective ha, FreeMonoid.of_injective hb] at h
    aesop
  | vertical h1 h2 h1_ih h2_ih =>
    rcases FreeMonoid.prod_eq_of ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hb] at h1
      have ⟨hc, hd⟩ := one_generator h1
      rw [hd, one_mul]
      exact h2_ih rfl hc
    have ⟨hf, hg⟩ := one_word h2
    rw [hf, hg, mul_one]
    exact h1_ih rfl hb
  | horizontal h1 h2 h1_ih h2_ih =>
    rcases FreeMonoid.prod_eq_of hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [ha] at h1
      have ⟨hc, hd⟩ := generator_one h1
      rw [hc, one_mul]
      exact h2_ih hd rfl
    have ⟨hf, hg⟩ := word_one h2
    rw [hf, hg, mul_one]
    exact h1_ih ha rfl

def generator_generator_close (h : grid (of i) (of j) c d) (dist : i.dist j = 1) :
  c = of j * of i ∧ d = of i * of j := generator_generator_close_helper h rfl rfl dist

private theorem generator_generator_apart_helper (h : grid a b c d) (ha : a = of i) (hb : b = of j)
    (hij : i.dist j > 1) : c = of j ∧ d = of i := by
  induction h with
  | empty => simp only [one_ne_of] at ha
  | top_bottom i => simp only [one_ne_of] at ha
  | sides i => simp only [one_ne_of] at hb
  | top_left i =>
    rw [← FreeMonoid.of_injective ha, ← FreeMonoid.of_injective hb] at hij
    simp only [Nat.dist_self, gt_iff_lt, not_lt_zero'] at hij
  | adjacent i k h =>
    rw [FreeMonoid.of_injective ha, FreeMonoid.of_injective hb] at h
    aesop
  | separated i j h =>
    rw [FreeMonoid.of_injective ha, FreeMonoid.of_injective hb] at h
    aesop
  | vertical h1 h2 h1_ih h2_ih =>
    rcases FreeMonoid.prod_eq_of ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hb] at h1
      have ⟨hc, hd⟩ := one_generator h1
      rw [hd, one_mul]
      exact h2_ih rfl hc
    have ⟨hf, hg⟩ := one_word h2
    rw [hf, hg, mul_one]
    exact h1_ih rfl hb
  | horizontal h1 h2 h1_ih h2_ih =>
    rcases FreeMonoid.prod_eq_of hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [ha] at h1
      have ⟨hc, hd⟩ := generator_one h1
      rw [hc, one_mul]
      exact h2_ih hd rfl
    have ⟨hf, hg⟩ := word_one h2
    rw [hf, hg, mul_one]
    exact h1_ih ha rfl

def generator_generator_apart (h : grid (of i) (of j) c d) (dist : i.dist j > 1) :
  c = of j ∧ d = of i := generator_generator_apart_helper h rfl rfl dist

end DeterminativeSpine
end Grid
