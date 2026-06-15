import BraidProject.SemiThue_C
import BraidProject.Cancellability_C
import BraidProject.GridsTwo_C

open Braid GridData

namespace Braid

noncomputable def ab_len (a b : List ℕ) : ℕ :=
  match GridData.existence a b with
  | ⟨_, _, h⟩ => GridData.length h

namespace GridData

namespace DeterminativeSpineLength

theorem one_word (h : GridData a b c d) (h2 : a = 1) : GridData.length h = 0 := by
  induction h with
  | empty => simp [GridData.length]
  | top_bottom i => simp [GridData.length]
  | sides i => simp [GridData.length]
  | top_left i => simp at h2
  | adjacent i k h => simp at h2
  | separated i j h => simp at h2
  | vertical h1 h2 h1_ih h2_ih =>
    apply FreeMonoid.prod_eq_one at h2
    simp [GridData.length, h1_ih h2.1, h2_ih h2.2]
  | horizontal h1 h2 h1_ih h2_ih =>
    simp [GridData.length, h1_ih h2, h2_ih (DeterminativeSpine.one_word h1 h2).2]

theorem word_one (h : GridData a b c d) (h2 : b = 1) : GridData.length h = 0 := by
  induction h with
  | empty => simp [GridData.length]
  | top_bottom i => simp [GridData.length]
  | sides i => simp [GridData.length]
  | top_left i => simp at h2
  | adjacent i k h => simp at h2
  | separated i j h => simp at h2
  | vertical h1 h2 h1_ih h2_ih =>
    simp [GridData.length, h1_ih h2, h2_ih (DeterminativeSpine.word_one h1 h2).1]
  | horizontal h1 h2 h1_ih h2_ih =>
    apply FreeMonoid.prod_eq_one at h2
    simp [GridData.length, h1_ih h2.1, h2_ih h2.2]

theorem generator_generator_same (h : GridData a b c d) (h1 : a = .of i) (h2 : b = .of i) : GridData.length h = 1 := by
  have H := DeterminativeSpine.generator_generator_same h h1 h2
  induction h with
  | empty => simp at h1
  | top_bottom i => simp at h1
  | sides i => simp at h2
  | top_left i => simp [GridData.length]
  | adjacent i k h =>
    rw [FreeMonoid.of_injective h1, FreeMonoid.of_injective h2] at h
    simp at h
  | separated i j h =>
    rw [FreeMonoid.of_injective h1, FreeMonoid.of_injective h2] at h
    simp at h
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g j k l m n o
    simp only [GridData.length]
    rcases FreeMonoid.prod_eq_of h1 with ⟨he, hk⟩ | ⟨he, hk⟩
    · have := DeterminativeSpineLength.one_word n he
      apply DeterminativeSpine.one_generator at n
      grind
    have := DeterminativeSpineLength.one_word o hk
    have := DeterminativeSpine.generator_generator_same n he
    grind
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g j k l m n o
    simp only [GridData.length]
    rcases FreeMonoid.prod_eq_of h2 with ⟨hf, hk⟩ | ⟨hf, hk⟩
    · have := DeterminativeSpineLength.word_one n
      apply DeterminativeSpine.generator_one at n
      grind
    have := DeterminativeSpineLength.one_word o
    have := DeterminativeSpine.generator_generator_same n h1
    grind

theorem generator_generator_close (h : GridData a b c d) (h1 : a = .of i) (h2 : b = .of j) (hd : i.dist j = 1): GridData.length h = 1 := by
  have H := DeterminativeSpine.generator_generator_close h h1 h2 hd
  induction h with
  | empty => simp at h1
  | top_bottom i => simp at h1
  | sides i => simp at h2
  | top_left i =>
    rw [← FreeMonoid.of_injective h2, FreeMonoid.of_injective h1] at hd
    simp at hd
  | adjacent i k h => simp [GridData.length]
  | separated i j h => simp [GridData.length]
  | vertical g1 g2 h1_ih h2_ih =>
    simp only [GridData.length]
    rcases FreeMonoid.prod_eq_of h1 with ⟨he, hl⟩ | ⟨he, hl⟩
    · have := DeterminativeSpineLength.one_word g1 he
      apply DeterminativeSpine.one_generator at g1
      grind
    apply DeterminativeSpine.generator_generator_close at g1
    have H := DeterminativeSpineLength.one_word g2
    grind
  | horizontal g1 g2 h1_ih h2_ih =>
    simp only [GridData.length]
    rcases FreeMonoid.prod_eq_of h2 with ⟨hf, hk⟩ | ⟨hf, hk⟩
    · have := DeterminativeSpineLength.word_one g1 hf
      apply DeterminativeSpine.generator_one at g1
      grind
    apply DeterminativeSpine.generator_generator_close at g1
    have H := DeterminativeSpineLength.word_one g2
    grind

theorem generator_generator_apart (h : GridData a b c d) (h1 : a = .of i) (h2 : b = .of k) (hd : i.dist k > 1) : GridData.length h = 1 := by
  induction h with
  | empty => simp at h1
  | top_bottom i => simp at h1
  | sides i => simp at h2
  | top_left i =>
    rw [← FreeMonoid.of_injective h2, FreeMonoid.of_injective h1] at hd
    simp at hd
  | adjacent i k h => simp [GridData.length]
  | separated i j h => simp [GridData.length]
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g j l m n o p
    simp only [GridData.length]
    rcases FreeMonoid.prod_eq_of h1 with ⟨he, hl⟩ | ⟨he, hl⟩
    · have := DeterminativeSpineLength.one_word o he
      apply DeterminativeSpine.one_generator at o
      grind
    have := DeterminativeSpineLength.one_word p hl
    have := DeterminativeSpine.generator_generator_apart p hd
    grind
  | horizontal g1 g2 h1_ih h2_ih =>
    rename_i e f g j l m n
    simp only [GridData.length]
    rcases FreeMonoid.prod_eq_of h2 with ⟨hf, hk⟩ | ⟨hf, hk⟩
    · have := DeterminativeSpineLength.word_one g1 hf
      apply DeterminativeSpine.generator_one at g1
      grind
    have := DeterminativeSpineLength.word_one g2 hk
    have := DeterminativeSpine.generator_generator_apart g2 hd
    grind

end DeterminativeSpineLength

-- section

-- variable {T : Nat → Nat → Type} (f : {a b : Nat} → T a b → Nat)
--   (h : ∀ a b, ∀ x y : T a b, f x = f y)

-- example (a b a' b' : Nat) (ha : a = a') (hb : b = b') (x : T a b) (y : T a' b') : f x = f y := by
--   subst ha
--   subst hb
--   apply h

-- end

def split_horizontally_n (h : GridData a b c d) := ∀ a₁ a₂, a = a₁ * a₂ →
  Σ u d₁ d₂, (h1 : GridData a₁ b u d₁) × (h2 : GridData a₂ u c d₂) × PLift (d = d₁ * d₂) ×
  PLift (GridData.length h = GridData.length h1 + GridData.length h2)

private def prod_eq_of_sum {α} (a b : FreeMonoid α) {i : α} (h : a * b = .of i) :
    PSum (PLift (a = 1 ∧ b = .of i)) (PLift (a = .of i ∧ b = 1)) := by
  cases a with
  | h0 => exact .inl ⟨rfl, by rwa [one_mul] at h⟩
  | ih x rest =>
    rw [mul_assoc] at h
    have h' : .of x * (rest * b) = .of i * 1 := by rw [mul_one]; exact h
    have hp := FreeMonoid.parts_eq h'
    have hrb := FreeMonoid.prod_eq_one hp.2
    exact .inr ⟨by rw [hp.1, hrb.1, mul_one], hrb.2⟩

private def prod_eq_prod_sum_list {α} : ∀ (a b c d : List α), a ++ b = c ++ d →
    PSum (Σ m : List α, PLift (c = a ++ m ∧ b = m ++ d))
         (Σ m : List α, PLift (a = c ++ m ∧ d = m ++ b))
  | [], b, c, d, h => .inl ⟨c, ⟨rfl, by simpa using h⟩⟩
  | x :: rest, b, [], d, h => .inr ⟨x :: rest, ⟨by simp, by simpa using h.symm⟩⟩
  | x :: rest, b, y :: rest', d, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hxy, heq⟩ := h
    have ih := prod_eq_prod_sum_list rest b rest' d heq
    match ih with
    | .inl ⟨m, hm⟩ =>
      exact .inl ⟨m, ⟨by rw [hxy, hm.down.1]; rfl, hm.down.2⟩⟩
    | .inr ⟨m, hm⟩ =>
      exact .inr ⟨m, ⟨by rw [hxy, hm.down.1]; rfl, hm.down.2⟩⟩

private def prod_eq_prod_sum {α} (a b c d : FreeMonoid α) (h : a * b = c * d) :
    PSum (Σ m, PLift (c = a * m ∧ b = m * d)) (Σ m, PLift (a = c * m ∧ d = m * b)) :=
  prod_eq_prod_sum_list a b c d h

noncomputable def splittable_horizontally {a b c d : FreeMonoid ℕ} (h : GridData a b c d) :
    split_horizontally_n h := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    exact ⟨1, 1, 1, .empty, .empty, ⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    exact ⟨.of i, 1, 1, .top_bottom _, .top_bottom _, ⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩
  | sides i =>
    intro a₁ a₂ b_is
    rcases prod_eq_of_sum a₁ a₂ b_is.symm with ⟨⟨ha1, ha2⟩⟩ | ⟨⟨hb1, hb2⟩⟩
    · rw [ha1, ha2]
      exact ⟨1, 1, .of i, .empty, .sides _, ⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩
    rw [hb1, hb2]
    exact ⟨1, .of i, 1, .sides _, .empty, ⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩
  | top_left i =>
    intro a₁ a₂ b_is
    rcases prod_eq_of_sum a₁ a₂ b_is.symm with ⟨⟨ha1, ha2⟩⟩ | ⟨⟨hb1, hb2⟩⟩
    · rw [ha1, ha2]
      exact ⟨.of i, 1, 1, .top_bottom _, .top_left _, ⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩
    rw [hb1, hb2]
    exact ⟨1, 1, 1, .top_left _, .empty, ⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩
  | adjacent i k dist =>
    intro a₁ a₂ b_is
    rcases prod_eq_of_sum a₁ a₂ b_is.symm with ⟨⟨ha1, ha2⟩⟩ | ⟨⟨hb1, hb2⟩⟩
    · rw [ha1, ha2]
      exact ⟨.of k, 1, .of i * .of k, .top_bottom _, .adjacent i k dist, ⟨by simp⟩,
        ⟨by simp [GridData.length]⟩⟩
    rw [hb1, hb2]
    exact ⟨.of k * .of i, .of i * .of k, 1, .adjacent i k dist,
      .horizontal (.top_bottom k) (.top_bottom i), ⟨by simp⟩, ⟨by simp [GridData.length]⟩⟩
  | separated i j dist =>
    intro a₁ a₂ b_is
    rcases prod_eq_of_sum a₁ a₂ b_is.symm with ⟨⟨ha1, ha2⟩⟩ | ⟨⟨hb1, hb2⟩⟩
    · rw [ha1, ha2]
      exact ⟨.of j, 1, .of i, .top_bottom _, .separated _ _ dist, ⟨by simp⟩,
        ⟨by simp [GridData.length]⟩⟩
    rw [hb1, hb2]
    exact ⟨.of j, .of i, 1, .separated _ _ dist, .top_bottom _, ⟨by simp⟩,
      ⟨by simp [GridData.length]⟩⟩
  | vertical h1 h2 ih1 ih2 =>
    rename_i a' b' c' d' e' f' g'
    intro fi₁ fi₂ fi_is
    rcases prod_eq_prod_sum a' e' fi₁ fi₂ fi_is with ⟨m, ⟨hm1, hm2⟩⟩ | ⟨m, ⟨hm1, hm2⟩⟩
    · rcases ih2 m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, ⟨hk⟩, ⟨len⟩⟩
      use u, d' * k₁, k₂
      rw [hm1]
      refine ⟨.vertical h1 g1, g2, ⟨?_⟩, ⟨?_⟩⟩
      · rw [hk, mul_assoc]
      simp [GridData.length, len, add_assoc]
    rcases ih1 fi₁ m hm1 with ⟨u, k₁, k₂, g1, g2, ⟨hk⟩, ⟨len⟩⟩
    use u, k₁, k₂ * g'
    rw [hm2]
    refine ⟨g1, .vertical g2 h2, ⟨?_⟩, ⟨?_⟩⟩
    · rw [hk, mul_assoc]
    simp [GridData.length, len, add_assoc]
  | horizontal h1 h2 ih1 ih2 =>
    intro f₁ f₂ f_is
    rcases ih1 f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, ⟨heq⟩, ⟨len1⟩⟩
    rcases ih2 m n heq with ⟨o, p, q, hg3, hg4, ⟨heq'⟩, ⟨len2⟩⟩
    use l * o, p, q
    refine ⟨.horizontal hg1 hg3, .horizontal hg2 hg4, ⟨heq'⟩, ⟨?_⟩⟩
    simp [GridData.length, len1, len2]
    omega

  -- match h with
  -- | .empty =>
  --   intro _ _ b_is
  --   rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
  --   use 1, 1, 1
  --   exact ⟨.empty, ⟨.empty, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩ ⟩
  -- | .top_bottom i =>
  --   intro _ _ b_is
  --   rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
  --   use .of i, 1, 1
  --   exact ⟨.top_bottom _, ⟨.top_bottom _, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  -- | .sides i =>
  --   intro _ _ b_is
  --   rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
  --   · rw [ha1, ha2]
  --     use 1, 1, .of i
  --     exact ⟨.empty, ⟨.sides _, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  --   rw [hb1, hb2]
  --   use 1, .of i, 1
  --   exact ⟨.sides _, ⟨.empty, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  -- | .top_left i =>
  --   intro _ _ b_is
  --   rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
  --   · rw [ha1, ha2]
  --     use .of i, 1, 1
  --     exact ⟨.top_bottom _, ⟨.top_left _, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  --   rw [hb1, hb2]
  --   use 1, 1, 1
  --   exact ⟨.top_left _, ⟨.empty, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  -- | .adjacent _ _ b_is=>
  --   intro i
  --   rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
  --   · rw [ha1, ha2]
  --     rename_i k dist _ _
  --     use .of k, 1, .of i * (.of k)
  --     exact ⟨.top_bottom _, ⟨.adjacent i k dist, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  --   rw [hb1, hb2]
  --   rename_i k dist _ _
  --   use .of k * .of i, .of i * .of k, 1
  --   exact ⟨.adjacent i k dist, ⟨GridData_top_bottom_word _, ⟨⟨rfl⟩,
  --     ⟨by simp [GridData.length]; exact GridData_length_top_bottom_word _ _ _ _ _ rfl⟩⟩⟩⟩
  -- | .separated i j h =>
  --   intro _ _ b_is
  --   rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
  --   · rw [ha1, ha2]
  --     use .of j, 1, .of i
  --     exact ⟨.top_bottom _, ⟨.separated _ _ h, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  --   rw [hb1, hb2]
  --   use .of j, .of i, 1
  --   exact ⟨.separated _ _ h, ⟨.top_bottom _, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  -- | .vertical h1 h2 =>
  --   rename_i e f g h i j k
  --   intro fi₁ fi₂ fi_is
  --   rcases FreeMonoid.prod_eq_prod' fi_is with ha | hb
  --   · rcases ha with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
  --     rcases splittable_horizontally_of_gridn h2 m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, ⟨hk⟩, ⟨len⟩⟩
  --     use u, g * k₁, k₂
  --     rw [hm1]
  --     exact ⟨.vertical h1 g1, ⟨g2, ⟨⟨by rw [mul_assoc, hk]⟩, ⟨by simp [GridData.length, len, add_assoc]⟩⟩⟩⟩
  --   rcases hb with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
  --   rcases splittable_horizontally_of_gridn h1 fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, ⟨hh⟩, ⟨len⟩⟩
  --   use u, h₁, (h₂ * j)
  --   rw [hm2]
  --   exact ⟨g1, ⟨.vertical g2 h2, ⟨⟨by rw [← mul_assoc, hh]⟩, ⟨by simp [GridData.length, len, add_assoc]⟩⟩⟩⟩
  -- | .horizontal h1 h2  =>
  --   intro f₁ f₂ f_is
  --   rcases splittable_horizontally_of_gridn h1 f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, ⟨heq⟩, ⟨len1⟩⟩
  --   rcases splittable_horizontally_of_gridn h2 m n heq with ⟨o, p, q, hg3, hg4, ⟨heq'⟩, ⟨len2⟩⟩
  --   use l * o, p, q
  --   exact ⟨.horizontal hg1 hg3, ⟨.horizontal hg2 hg4, ⟨⟨heq'⟩, ⟨by simp [GridData.length, len1, len2]; omega⟩⟩⟩⟩

-- so now there was kind of no point of doing the other noncomputable splits, right?
def split_vertically_n (h : GridData a b c d)  := ∀ b₁ b₂, b = b₁ * b₂ →
  Σ u c₁ c₂, (h1 : GridData a b₁ c₁ u) × (h2 : GridData u b₂ c₂ d) × PLift (c = c₁ * c₂) ×
  PLift (GridData.length h = GridData.length h1 + GridData.length h2)

noncomputable def splittable_vertically {a b c d : FreeMonoid ℕ} (h : GridData a b c d) :
    split_vertically_n h := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1
    exact ⟨GridData.empty, ⟨GridData.empty, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rcases prod_eq_of_sum _ _ b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · use 1, 1, (.of i)
      exact ⟨GridData.empty, ⟨GridData.top_bottom _, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
    use 1, (.of i), 1
    exact ⟨GridData.top_bottom _, ⟨GridData.empty, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  | sides i =>
    intro _ _ b_is
    use (.of i), 1, 1
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    exact ⟨GridData.sides _, ⟨GridData.sides _, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases (prod_eq_of_sum _ _ b_is.symm) with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · use (.of i), 1, 1
      exact ⟨GridData.sides _, ⟨GridData.top_left _, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
    · use 1, 1, 1
      exact ⟨GridData.top_left _, ⟨GridData.empty, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  | adjacent i =>
    intro _ _ b_is
    rcases (prod_eq_of_sum _ _ b_is.symm) with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · rename_i k l
      use .of i, 1, .of (k) * .of i
      exact ⟨GridData.sides i, ⟨GridData.adjacent i k l, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
    · rename_i k l
      use .of i * .of k, .of k * .of i, 1
      exact ⟨GridData.adjacent i k l, ⟨GridData.sides_word _, ⟨⟨rfl⟩,
        ⟨by simp only [length, Nat.left_eq_add]; rfl⟩⟩⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases (prod_eq_of_sum _ _ b_is.symm) with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · use .of i, 1, .of j
      exact ⟨GridData.sides _, ⟨GridData.separated _ _ h, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
    use .of i, .of j, 1
    exact ⟨GridData.separated _ _ h, ⟨GridData.sides _, ⟨⟨rfl⟩, ⟨by simp [GridData.length]⟩⟩⟩⟩
  | vertical _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, ⟨heq⟩, ⟨len1⟩⟩
    rcases h2_ih m n heq with ⟨o, p, q, hg3, hg4, ⟨heq'⟩, ⟨len2⟩⟩
    use l * o, p, q
    exact ⟨GridData.vertical hg1 hg3, ⟨GridData.vertical hg2 hg4, ⟨⟨heq'⟩,
      ⟨by simp [GridData.length, len1, len2]; omega⟩⟩⟩⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    rcases prod_eq_prod_sum _ _ _ _ fi_is with ⟨m, ⟨rfl, rfl⟩⟩ | ⟨m, ⟨rfl, rfl⟩⟩
    · rcases h2_ih m fi₂ rfl with ⟨u, k₁, k₂, hg1, hg2, ⟨heq⟩, ⟨len⟩⟩
      use u, g * k₁, k₂
      refine ⟨GridData.horizontal h1 hg1, hg2, ⟨by rw [heq, mul_assoc]⟩, ⟨?_⟩⟩
      simp [GridData.length, len]; omega
    rcases h1_ih fi₁ m rfl with ⟨u, h₁, h₂, g1, g2, ⟨hh⟩, ⟨len⟩⟩
    use u, h₁, (h₂ * j)
    refine ⟨g1, GridData.horizontal g2 h2, ⟨by rw [hh, mul_assoc]⟩, ⟨?_⟩⟩
    simp [GridData.length, len]; omega

open DeterminativeSpineLength

theorem same_type_same_length (g1 : GridData a b c d) (g2 : GridData e f g h) :
    a = e → b = f → GridData.length g1 = GridData.length g2 := by
  induction g1 generalizing e f g h with
  | empty =>
    intro ha hb
    simp [GridData.length]
    exact (word_one g2 hb.symm).symm
  | top_bottom i =>
    intro ha hb
    simp [GridData.length]
    exact (one_word g2 ha.symm).symm
  | sides i =>
    intro ha hb
    simp [GridData.length]
    exact (word_one g2 hb.symm).symm
  | top_left i =>
    intro ha hb
    simp [GridData.length]
    exact (generator_generator_same g2 ha.symm hb.symm).symm
  | adjacent i k h1 =>
    intro ha hb
    simp [GridData.length]
    exact (generator_generator_close g2 ha.symm hb.symm h1).symm
  | separated i j h1 =>
    intro ha hb
    simp [GridData.length]
    exact (generator_generator_apart g2 ha.symm hb.symm h1).symm
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i k l m n o p q
    intro ko l_is
    rcases splittable_horizontally g2 _ _ ko.symm with ⟨r, s, t, g21, g22, ⟨mid_is⟩, ⟨len⟩⟩
    rw [len, GridData.length]
    specialize h1_ih g21 rfl l_is
    specialize h2_ih g22 rfl (GridData.unicity h1 g21 rfl l_is).1.1.symm
    rw [h1_ih]
    refine Nat.add_left_cancel_iff.mpr ?_
    apply h2_ih
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i k l m n o p q
    intro ko l_is
    rcases splittable_vertically g2 _ _ l_is.symm with ⟨r, s, t, g21, g22, ⟨mid_is⟩, ⟨len⟩⟩
    rw [len, GridData.length]
    specialize h1_ih g21 ko rfl
    specialize h2_ih g22 (GridData.unicity h1 g21 ko rfl).2.1.symm rfl
    omega
