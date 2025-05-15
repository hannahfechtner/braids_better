import BraidProject.StepTwo_C
import BraidProject.SemiThue_C
import BraidProject.Cancellability_C
import BraidProject.GridsTwo_C

def gridt.length : gridt a b c d → ℕ := by
  intro h
  match h with
  | gridt.empty => exact 0
  | gridt.sides _ => exact  0
  | gridt.top_bottom _ => exact 0
  | gridt.top_left _ => exact 1
  | gridt.adjacent _ _ _ => exact 1
  | gridt.separated _ _ _ => exact 1
  | gridt.horizontal h1 h2 => exact gridt.length h1 + gridt.length h2
  | gridt.vertical h1 h2 => exact gridt.length h1 + gridt.length h2

noncomputable def ab_len (a b : List ℕ) : ℕ :=
  match existence_s a b with
  | ⟨_, _, h⟩ => gridt.length h

theorem gridt_length_all_ones (h : gridt a b c d) (h1 : a = 1) (h2 : b = 1) : h.length = 0 := by
  have H := all_ones_t h h1 h2
  induction h with
  | empty => simp [gridt.length]
  | top_bottom i => simp [gridt.length]
  | sides i => simp [gridt.length]
  | top_left i => simp at h1
  | adjacent i k h => simp at h1
  | separated i j h => simp at h1
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g j k l m n o
    apply FreeMonoid.prod_eq_one at h1
    have H4 := FreeMonoid.prod_eq_one H.1
    simp [gridt.length]
    constructor
    · exact h1_ih h1.1 h2 ⟨(FreeMonoid.prod_eq_one H.1).1, (all_ones_t n h1.1 h2).2⟩
    exact h2_ih h1.2 (all_ones_t n h1.1 h2).2 ⟨H4.2, H.2⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g j k l m n o
    apply FreeMonoid.prod_eq_one at h2
    have H4 := FreeMonoid.prod_eq_one H.2
    simp [gridt.length]
    constructor
    · exact h1_ih h1 h2.1 ⟨(all_ones_t n h1 h2.1).1, (FreeMonoid.prod_eq_one H.2).1⟩
    apply h2_ih (all_ones_t n h1 h2.1).1 h2.2 ⟨H.1, H4.2⟩

theorem gridt_length_top_bottom {a b c d i} (h : gridt a b c d) (h1 : a = 1) (h2 : b = .of i) : h.length = 0 := by
  have H := i_top_bottom_t h i h1 h2
  induction h with
  | empty => simp [gridt.length]
  | top_bottom i => simp [gridt.length]
  | sides i => simp [gridt.length]
  | top_left i => simp at h1
  | adjacent i k h => simp at h1
  | separated i j h => simp at h1
  | vertical h1 h2 h1_ih h2_ih =>
    simp [gridt.length]
    rename_i e f g j k l m n o
    apply FreeMonoid.prod_eq_one at h1
    have H3 := i_top_bottom_t n _ h1.1 h2
    constructor
    · exact h1_ih h1.1 h2 ⟨(FreeMonoid.prod_eq_one H.1).1, H3.2⟩
    exact h2_ih h1.right H3.right ⟨(FreeMonoid.prod_eq_one H.left).right, H.right⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    simp [gridt.length]
    rename_i e f g j k l m n o
    rcases FreeMonoid.prod_eq_of h2 with fk | fk
    · rcases FreeMonoid.prod_eq_of H.2 with jm | jm
      · simp [fk, jm, H.1, h1] at h2_ih
        have H4 := all_ones_t n h1 fk.1
        constructor
        · exact gridt_length_all_ones n h1 fk.1
        apply h2_ih H4.1
      exfalso
      have H : j = 1 := (all_ones_t n h1 fk.1).2
      have H2 := (i_top_bottom_t o i (all_ones_t n h1 fk.1).1 fk.2).2
      rw [jm.2] at H2
      simp at H2
    rcases FreeMonoid.prod_eq_of H.2 with jm | jm
    · exfalso
      have H := (i_top_bottom_t n _ h1 fk.1)
      have H2 := all_ones_t o H.1 fk.2
      rw [H2.2] at jm
      simp at jm
    have H3 := i_top_bottom_t n _ h1 fk.1
    constructor
    · exact h1_ih h1 fk.1 H3
    exact gridt_length_all_ones o H3.1 fk.2

theorem gridt_length_top_bottom_word (a b c d) (h : gridt a b c d) (h2 : a = 1) : h.length = 0 := by
  induction h with
  | empty => simp [gridt.length]
  | top_bottom i => simp [gridt.length]
  | sides i => simp [gridt.length]
  | top_left i => simp at h2
  | adjacent i k h => simp at h2
  | separated i j h => simp at h2
  | vertical h1 h2 h1_ih h2_ih =>
    apply FreeMonoid.prod_eq_one at h2
    simp [gridt.length, h1_ih h2.1, h2_ih h2.2]
  | horizontal h1 h2 h1_ih h2_ih =>
    simp [gridt.length, h1_ih h2, h2_ih (word_side_side_t _ _ _ h1 h2).1]

theorem gridt_length_side_side {a b c d i} (h : gridt a b c d) (h1 : a = .of i) (h2 : b = 1) : h.length = 0 := by
  have H := i_side_side_t h i h1 h2
  induction h with
  | empty => simp [gridt.length]
  | top_bottom i => simp [gridt.length]
  | sides i => simp [gridt.length]
  | top_left i => simp at h2
  | adjacent i k h => simp at h2
  | separated i j h => simp at h2
  | vertical h1 h2 h1_ih h2_ih =>
    simp [gridt.length]
    rename_i e f g j k l m n o
    rcases FreeMonoid.prod_eq_of h1 with ek | ek
    · rcases FreeMonoid.prod_eq_of H.1 with gl | gl
      · simp only [ek, gl, true_and, forall_const] at h2_ih
        exact ⟨gridt_length_all_ones n ek.left h2, h2_ih (all_ones_t n ek.left h2).right H.right⟩
      rw [(i_side_side_t o i ek.2 (all_ones_t n ek.1 h2).2).1] at gl
      simp at gl
    rcases FreeMonoid.prod_eq_of H.1 with gl | gl
    · rw [(all_ones_t o ek.2 (i_side_side_t n _ ek.1 h2).2).1] at gl
      simp at gl
    exact ⟨h1_ih ek.left h2 ⟨gl.left, (i_side_side_t n i ek.left h2).right⟩,
      gridt_length_all_ones o ek.right (i_side_side_t n i ek.left h2).right⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g j k l m n o
    apply FreeMonoid.prod_eq_one at h2
    have H3 := i_side_side_t n _ h1 h2.1
    rw [gridt.length, Nat.add_eq_zero]
    constructor
    · apply h1_ih h1 h2.1 H3
    apply h2_ih H3.1 h2.2
    constructor
    · exact H.1
    rw [H3.2, one_mul] at H
    exact H.2

theorem gridt_length_side_side_word (a b c d) (h : gridt a b c d) (h2 : b = 1) : h.length = 0 := by
  induction h with
  | empty => simp [gridt.length]
  | top_bottom i => simp [gridt.length]
  | sides i => simp [gridt.length]
  | top_left i => simp at h2
  | adjacent i k h => simp at h2
  | separated i j h => simp at h2
  | vertical h1 h2 h1_ih h2_ih =>
    simp [gridt.length, h1_ih h2, h2_ih (word_top_bottom_t _ _ _ h1 h2).2]
  | horizontal h1 h2 h1_ih h2_ih =>
    apply FreeMonoid.prod_eq_one at h2
    simp [gridt.length, h1_ih h2.1, h2_ih h2.2]

theorem gridt_length_top_left (h : gridt a b c d) (h1 : a = .of i) (h2 : b = .of i) : h.length = 1 := by
  have H := i_top_left_t h i h1 h2
  induction h with
  | empty => simp at h1
  | top_bottom i => simp at h1
  | sides i => simp at h2
  | top_left i => simp [gridt.length]
  | adjacent i k h =>
    rw [FreeMonoid.of_injective h1, FreeMonoid.of_injective h2] at h
    simp at h
  | separated i j h =>
    rw [FreeMonoid.of_injective h1, FreeMonoid.of_injective h2] at h
    simp at h
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g j k l m n o
    simp [gridt.length]
    simp [h2] at h2_ih
    cases FreeMonoid.prod_eq_of h1
    · rename_i ek
      specialize h2_ih ek.2
      simp [FreeMonoid.prod_eq_one] at H
      simp [H] at h2_ih
      have H2 := i_top_bottom_t n i ek.1 h2
      specialize h2_ih H2.2
      rw [h2_ih]
      simp
      exact gridt_length_top_bottom n ek.1 h2
    rename_i ek
    rw [h1_ih ek.1 h2 ⟨(FreeMonoid.prod_eq_one H.1).1, (i_top_left_t n i ek.1 h2).2⟩]
    simp
    exact gridt_length_all_ones o ek.2 (i_top_left_t n i ek.1 h2).2
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g j k l m n o
    cases FreeMonoid.prod_eq_of h2
    · rename_i fk
      have H3 := i_side_side_t n _ h1 fk.1
      specialize h2_ih H3.1 fk.2 ⟨H.1, (FreeMonoid.prod_eq_one H.2).2⟩
      simp [gridt.length, gridt_length_side_side n h1 fk.1, h2_ih]
    rename_i fk
    have H3 := i_top_left_t n _ h1 fk.1
    specialize h1_ih h1 fk.1 H3
    simp [gridt.length, h1_ih]
    apply gridt_length_all_ones o H3.1 fk.2

theorem gridt_length_adjacent (h : gridt a b c d) (h1 : a = .of i) (h2 : b = .of j) (hd : i.dist j = 1): h.length = 1 := by
  have H := i_adjacent_t h i j h1 h2 hd
  induction h with
  | empty => simp at h1
  | top_bottom i => simp at h1
  | sides i => simp at h2
  | top_left i =>
    rw [← FreeMonoid.of_injective h2, FreeMonoid.of_injective h1] at hd
    simp at hd
  | adjacent i k h => simp [gridt.length]
  | separated i j h => simp [gridt.length]
  | vertical g1 g2 h1_ih h2_ih =>
    rename_i e f g k l m n
    simp [h2] at h1_ih
    simp [H.2] at h2_ih
    simp [gridt.length]
    cases FreeMonoid.prod_eq_of h1
    · rename_i el
      simp [el.2] at h2_ih
      have h := i_top_bottom_t g1 j el.1 h2
      specialize h2_ih h.2
      have h3 := i_adjacent_t g2 i j el.2 h.2 hd
      specialize h2_ih h3.1
      simp [h2_ih, gridt_length_top_bottom g1 el.1 h2]
    rename_i el
    have h := i_adjacent_t g1 i j el.1 h2 hd
    specialize h1_ih el.1 h.1 h.2
    simp [h1_ih]
    have h5 := word_side_side_t _ _ _ g2 el.2
    exact gridt_length_top_bottom_word _ _ _ _ _ el.2
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g k l m n o p
    specialize h1_ih h1
    simp [H.1] at h2_ih
    simp only [gridt.length]
    rcases FreeMonoid.prod_eq_of h2 with fk | fk
    · simp only [fk.2, forall_const] at h2_ih
      have gk := i_side_side_t o _ h1 fk.1
      rw [gk.2, one_mul] at H
      simp [gridt_length_side_side o h1 fk.1, h2_ih gk.1 H.2]
    simp only [fk.1, forall_const] at h1_ih
    simp [gridt.length, gridt_length_side_side_word _ _ _ _ p fk.2]
    exact h1_ih (i_adjacent_t o _ _ h1 fk.1 hd)

theorem gridt_length_separated (h : gridt a b c d) (h1 : a = .of i) (h2 : b = .of k) (hd : i.dist k > 1) : h.length = 1 := by
  induction h with
  | empty => simp at h1
  | top_bottom i => simp at h1
  | sides i => simp at h2
  | top_left i =>
    rw [← FreeMonoid.of_injective h2, FreeMonoid.of_injective h1] at hd
    simp at hd
  | adjacent i k h => simp [gridt.length]
  | separated i j h => simp [gridt.length]
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g j l m n o p
    rcases FreeMonoid.prod_eq_of h1 with el | el
    · specialize h2_ih el.2
      have gj := i_top_bottom_t o _ el.1 h2
      simp only [gridt.length, h2_ih gj.2, Nat.add_eq_right]
      exact gridt_length_top_bottom o el.1 h2
    simp [gridt.length, h1_ih el.1 h2]
    exact gridt_length_top_bottom_word _ _ _ _ p el.2
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g j l m n o p
    rcases FreeMonoid.prod_eq_of h2 with fl | fl
    · have gj := i_side_side_t o _ h1 fl.1
      simp [gridt.length, h2_ih gj.1 fl.2]
      exact gridt_length_side_side o h1 fl.1
    simp [gridt.length, h1_ih h1 fl.1]
    exact gridt_length_side_side_word _ _ _ _ p fl.2

section

variable {T : Nat → Nat → Type} (f : {a b : Nat} → T a b → Nat)
  (h : ∀ a b, ∀ x y : T a b, f x = f y)

example (a b a' b' : Nat) (ha : a = a') (hb : b = b') (x : T a b) (y : T a' b') : f x = f y := by
  subst ha
  subst hb
  apply h

end

def split_horizontally_n (h : gridt a b c d) := ∀ a₁ a₂, a = a₁ * a₂ →
  Σ u c₁ c₂, (h1 : gridt a₁ b c₁ u) × (h2 : gridt a₂ u c₂ d) × PLift (c = c₁ * c₂) ×
  PLift (h.length = h1.length + h2.length)

noncomputable def splittable_horizontally_of_gridn {a b c d : FreeMonoid ℕ} (h : gridt a b c d) :
    split_horizontally_n h := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1
    exact ⟨.empty, ⟨.empty, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩ ⟩
  | top_bottom i =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use .of i, 1, 1
    exact ⟨.top_bottom _, ⟨.top_bottom _, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
  | sides i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
    · rw [ha1, ha2]
      use 1, 1, .of i
      exact ⟨.empty, ⟨.sides _, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
    rw [hb1, hb2]
    use 1, .of i, 1
    exact ⟨.sides _, ⟨.empty, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
    · rw [ha1, ha2]
      use .of i, 1, 1
      exact ⟨.top_bottom _, ⟨.top_left _, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
    rw [hb1, hb2]
    use 1, 1, 1
    exact ⟨.top_left _, ⟨.empty, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
  | adjacent i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
    · rw [ha1, ha2]
      rename_i k dist _ _
      use .of k, 1, .of i * (.of k)
      exact ⟨.top_bottom _, ⟨.adjacent i k dist, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
    rw [hb1, hb2]
    rename_i k dist _ _
    use .of k * .of i, .of i * .of k, 1
    exact ⟨.adjacent i k dist, ⟨gridt_top_bottom_word _, ⟨⟨rfl⟩,
      ⟨by simp [gridt.length]; exact gridt_length_top_bottom_word _ _ _ _ _ rfl⟩⟩⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨hb1⟩, ⟨hb2⟩⟩
    · rw [ha1, ha2]
      use .of j, 1, .of i
      exact ⟨.top_bottom _, ⟨.separated _ _ h, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
    rw [hb1, hb2]
    use .of j, .of i, 1
    exact ⟨.separated _ _ h, ⟨.top_bottom _, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    rcases FreeMonoid.prod_eq_prod' fi_is with ha | hb
    · rcases ha with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
      rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1, g2, ⟨hk⟩, ⟨len⟩⟩
      use u, g * k₁, k₂
      rw [hm1]
      exact ⟨.vertical h1 g1, ⟨g2, ⟨⟨by rw [mul_assoc, hk]⟩, ⟨by simp [gridt.length, len, add_assoc]⟩⟩⟩⟩
    rcases hb with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, ⟨hh⟩, ⟨len⟩⟩
    use u, h₁, (h₂ * j)
    rw [hm2]
    exact ⟨g1, ⟨.vertical g2 h2, ⟨⟨by rw [← mul_assoc, hh]⟩, ⟨by simp [gridt.length, len, add_assoc]⟩⟩⟩⟩
  | horizontal _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, ⟨heq⟩, ⟨len1⟩⟩
    rcases h2_ih m n heq with ⟨o, p, q, hg3, hg4, ⟨heq'⟩, ⟨len2⟩⟩
    use l * o, p, q
    exact ⟨.horizontal hg1 hg3, ⟨.horizontal hg2 hg4, ⟨⟨heq'⟩, ⟨by simp [gridt.length, len1, len2]; omega⟩⟩⟩⟩


def split_vertically_n (h : gridt a b c d)  := ∀ b₁ b₂, b = b₁ * b₂ →
  Σ u d₁ d₂, (h1 : gridt a b₁ u d₁) × (h2 : gridt u b₂ c d₂) × PLift (d = d₁ * d₂) ×
  PLift (h.length = h1.length + h2.length)

noncomputable def splittable_vertically_of_gridn {a b c d : FreeMonoid ℕ} (h : gridt a b c d) :
    split_vertically_n h := by
  induction h with
  | empty =>
    intro _ _ b_is
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    use 1, 1, 1
    exact ⟨gridt.empty, ⟨gridt.empty, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
  | top_bottom i =>
    intro _ _ b_is
    rcases FreeMonoid.prod_eq_of' b_is.symm with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · rw [ha1, ha2]
      use 1, 1, (.of i)
      exact ⟨gridt.empty, ⟨gridt.top_bottom _, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
    rw [ha1, ha2]
    use 1, (.of i), 1
    exact ⟨gridt.top_bottom _, ⟨gridt.empty, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
  | sides i =>
    intro _ _ b_is
    use (.of i), 1, 1
    rw [(FreeMonoid.prod_eq_one b_is.symm).1, (FreeMonoid.prod_eq_one b_is.symm).2]
    exact ⟨gridt.sides _, ⟨gridt.sides _, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
  | top_left i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of' b_is.symm) with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · rw [ha1, ha2]
      use (.of i), 1, 1
      exact ⟨gridt.sides _, ⟨gridt.top_left _, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
    · rw [ha1, ha2]
      use 1, 1, 1
      exact ⟨gridt.top_left _, ⟨gridt.empty, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
  | adjacent i =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of' b_is.symm) with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · rw [ha1, ha2]
      rename_i k l m n
      use .of i, 1, .of (k) * .of i
      exact ⟨gridt.sides i, ⟨gridt.adjacent i k l, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
    · rw [ha1, ha2]
      rename_i k l m n
      use .of i * .of k, .of k * .of i, 1
      exact ⟨gridt.adjacent i k l, ⟨gridt_sides_word _, ⟨⟨rfl⟩,
        ⟨by simp [gridt.length, gridt_length_side_side_word]⟩⟩⟩⟩
  | separated i j h =>
    intro _ _ b_is
    rcases (FreeMonoid.prod_eq_of' b_is.symm) with ⟨⟨ha1⟩, ⟨ha2⟩⟩ | ⟨⟨ha1⟩, ⟨ha2⟩⟩
    · rw [ha1, ha2]
      use .of i, 1, .of j
      exact ⟨gridt.sides _, ⟨gridt.separated _ _ h, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
    rw [ha1, ha2]
    use .of i, .of j, 1
    exact ⟨gridt.separated _ _ h, ⟨gridt.sides _, ⟨⟨rfl⟩, ⟨by simp [gridt.length]⟩⟩⟩⟩
  | vertical _ _ h1_ih h2_ih =>
    intro f₁ f₂ f_is
    rcases h1_ih f₁ f₂ f_is with ⟨l, m, n, hg1, hg2, ⟨heq⟩, ⟨len1⟩⟩
    rcases h2_ih m n heq with ⟨o, p, q, hg3, hg4, ⟨heq'⟩, ⟨len2⟩⟩
    use l * o, p, q
    exact ⟨gridt.vertical hg1 hg3, ⟨gridt.vertical hg2 hg4, ⟨⟨heq'⟩,
      ⟨by simp [gridt.length, len1, len2]; omega⟩⟩⟩⟩
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    intro fi₁ fi₂ fi_is
    rcases FreeMonoid.prod_eq_prod' fi_is with ha | hb
    · rcases ha with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
      rcases h2_ih m fi₂ hm2 with ⟨u, k₁, k₂, g1⟩
      use u, h * k₁, k₂
      rw [hm1]
      exact ⟨gridt.horizontal h1 g1.1, ⟨g1.2.1, ⟨⟨by rw [mul_assoc, g1.2.2.1.1]⟩,
        ⟨by simp [gridt.length, g1.2.2.2.1]; omega⟩⟩⟩⟩
    rcases hb with ⟨m, ⟨hm1⟩, ⟨hm2⟩⟩
    rcases h1_ih fi₁ m hm1 with ⟨u, h₁, h₂, g1, g2, ⟨hh⟩, ⟨len⟩⟩
    use u, h₁, (h₂ * k)
    rw [hm2]
    exact ⟨g1, ⟨gridt.horizontal g2 h2, ⟨⟨by rw [← mul_assoc, hh]⟩,
      ⟨by simp [gridt.length, len]; omega⟩ ⟩⟩⟩

theorem same_type_same_length (g1 : gridt a b c d) (g2 : gridt e f g h) : a = e → b = f → g1.length = g2.length := by
  induction g1 generalizing e f g h with
  | empty =>
    intro ha hb
    simp [gridt.length]
    exact (gridt_length_all_ones g2 ha.symm hb.symm).symm
  | top_bottom i =>
    intro ha hb
    simp [gridt.length]
    exact (gridt_length_top_bottom g2 ha.symm hb.symm).symm
  | sides i =>
    intro ha hb
    simp [gridt.length]
    exact (gridt_length_side_side g2 ha.symm hb.symm).symm
  | top_left i =>
    intro ha hb
    simp [gridt.length]
    exact (gridt_length_top_left g2 ha.symm hb.symm).symm
  | adjacent i k h1 =>
    intro ha hb
    simp [gridt.length]
    exact (gridt_length_adjacent g2 ha.symm hb.symm h1).symm
  | separated i j h1 =>
    intro ha hb
    simp [gridt.length]
    exact (gridt_length_separated g2 ha.symm hb.symm h1).symm
  | vertical h1 h2 h1_ih h2_ih =>
    rename_i k l m n o p q
    intro ko l_is
    rcases splittable_horizontally_of_gridn g2 _ _ ko.symm with ⟨r, s, t, g21, g22, ⟨mid_is⟩, ⟨len⟩⟩
    rw [len, gridt.length]
    specialize h1_ih g21 rfl l_is
    specialize h2_ih g22 rfl (unicity_c h1 g21 rfl l_is).2.1.symm
    omega
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i k l m n o p q
    intro ko l_is
    rcases splittable_vertically_of_gridn g2 _ _ l_is.symm with ⟨r, s, t, g21, g22, ⟨mid_is⟩, ⟨len⟩⟩
    rw [len, gridt.length]
    specialize h1_ih g21 ko rfl
    specialize h2_ih g22 (unicity_c h1 g21 ko rfl).1.1.symm rfl
    omega

theorem all_ones_length_pg (h : PartialGrid a b c d e) : a = [(none, false)] → b = [(none, true)] → h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i =>
      intro h1
      simp [to_up] at h1
    | adjacent i k h =>
      intro h1
      simp [to_up] at h1
    | separated i j h =>
      intro h1
      simp [to_up] at h1
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem top_bottom_length_pg (h : PartialGrid a b c d e) : a = [(none, false)] → b = [(some i, true)] → h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i =>  simp [PartialGrid.length]
    | sides i =>  simp [PartialGrid.length]
    | top_left i =>
      intro ha
      simp [to_up] at ha
    | adjacent i k h =>
      intro ha
      simp [to_up] at ha
    | separated i j h =>
      intro ha
      simp [to_up] at ha
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem side_side_length_pg {a b c d e i} (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(none, true)] → h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i =>  simp [PartialGrid.length]
    | sides i =>  simp [PartialGrid.length]
    | top_left i =>
      intro ha hb
      simp [to_over] at hb
    | adjacent i k h =>
      intro ha hb
      simp [to_over] at hb
    | separated i j h =>
      intro ha hb
      simp [to_over] at hb
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem top_left_length_pg {a b c d e i} (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some i, true)] →
  remove_ones (c ++ d ++ e) = [] → h.length = 1 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h =>simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro ha hb rm
    rw [ha, hb] at rm
    simp [remove_ones] at rm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem adjacent_length_pg (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some j, true)] →
    remove_ones (c ++ d ++ e) = [(j, true), (i, true), (j, false), (i, false)] → i.dist j = 1 → h.length = 1 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h => simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro a_is b_is rm
    simp [a_is, b_is, remove_ones] at rm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

theorem separated_length_pg (h : PartialGrid a b c d e) : a = [(some i, false)] → b = [(some k, true)] →
    remove_ones (c ++ d ++ e) = [(k, true), (i, false)] → i.dist k > 1 → h.length = 1 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp
    | top_bottom i => simp
    | sides i => simp
    | top_left i => simp [PartialGrid.length]
    | adjacent i k h => simp [PartialGrid.length]
    | separated i j h => simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    intro a_is b_is rm
    simp [a_is, b_is, remove_ones] at rm
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 b_is with hb | hb
    · have H := PartialGrid.top_length_pos g1
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.top_length_pos g2
    rw [hb.2] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro a_is b_is
    rcases List.append_eq_singleton_iff.1 a_is with hb | hb
    · have H := PartialGrid.left_length_pos g2
      rw [hb.1] at H
      simp at H
    have H := PartialGrid.left_length_pos g1
    rw [hb.2] at H
    simp at H

def split_vertically_pg' (h : PartialGrid a b c d e)  := ∀ b₁ b₂, b = b₁ ++ b₂ →
  b₁.length > 0 → b₂.length > 0 →
  (Σ mid c1 d1 c2 d2,
  (h1 : PartialGrid a b₁ c1 d1 mid) × (h2 : PartialGrid mid b₂ c2 d2 e) ×
  PLift (c ++ d = c1 ++ d1 ++ c2 ++ d2) ×
  PLift (h.length = h1.length + h2.length)) ⊕
  (Σ d1 d2, (h1 : PartialGrid a b₁ c d1 []) × PLift (h.length = h1.length) ×
    PLift (e = []) × PLift (d = d1 ++ d2) × PLift (b₂ = d2))

def List.append_eq_singleton_C (h : a ++ b = [c]) : PLift (a = [] ∧ b = [c]) ⊕ PLift (a = [c] ∧ b = []) := by
  induction a with
  | nil =>
    simp [List.append_eq_singleton_iff] at h
    exact Sum.inl ⟨rfl, h⟩
  | cons x xs ih =>
    simp at h
    right
    constructor
    simp [h]

def List.append_eq_append' {a b c d : List α} (h : a ++ b = c ++ d) :
    (Σ from_middle, PLift (c = a ++ from_middle) × PLift (b = from_middle ++ d)) ⊕
    (Σ to_middle, PLift (a = c ++ to_middle) × PLift (d = to_middle ++ b)) :=
  FreeMonoid.prod_eq_prod' h

def List.cases_C (a : List α) : PLift (a = []) ⊕ PLift (a.length > 0) :=
  match ha : a.length with
  | 0 => Sum.inl ⟨List.length_eq_zero_iff.mp ha⟩
  | Nat.succ n => Sum.inr ⟨by simp⟩

theorem not_both_empty : PartialGrid a b c d e → d = [] → e = [] → False := by
  intro h
  induction h with
  | single_gridt h =>
    intro ha hb
    simp [to_up] at hb
    rename_i c _
    match c with
    | [] => simp at hb
    | c1 :: c2 => simp at hb
  | empty a b ha ha1 hb hb1 =>
    intro h1
    apply congr_arg List.length at h1
    simp [List.length] at h1
    rw [h1.1] at ha
    simp at ha
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    exact g2_ih
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro h1
    apply g2_ih
    simp at h1
    exact h1.2.2
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    intro h1 h2
    simp at h2
    apply g2_ih h1
    exact h2.1
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro h1 h2
    simp at h1
    apply g1_ih h1.2.2 h2

theorem not_both_empty_early : PartialGrid a b c d e → c = [] → d = [] → False := by
  intro h
  induction h with
  | single_gridt h =>
    intro ha hb
    simp [to_over] at ha
    rename_i c
    match c with
    | [] => simp at ha
    | c1 :: c2 => simp at ha
  | empty a b ha ha1 hb hb1 =>
    intro _ h1
    apply congr_arg List.length at h1
    simp [List.length] at h1
    rw [h1.1] at ha
    simp at ha
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    intro h1 h2
    simp at h1
    exact g1_ih h1.1 rfl
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    intro h1 h2
    simp at h2
    exact g2_ih h2.2.1 h2.2.2
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    exact g2_ih
  | vertical_append g1 g2 h g1_ih g2_ih =>
    intro h1 h2
    simp at h2
    exact g2_ih h1 h2.1

theorem pg_not_mid_right_empty : PartialGrid a b c [] [] → False := fun h => not_both_empty h rfl rfl

noncomputable def PartialGrid.extend_bottom_w_len (h : PartialGrid a b c d e) (a2) (h2 : is_false a2) (h3 : a2 ≠ []) :
    (h1 : PartialGrid (a2 ++ a) b [] (a2 ++ c ++ d) e) × PLift (h.length = h1.length):= by
  induction h with
  | single_gridt h =>
    cases a2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i d
      rw [List.append_nil]
      have H := PartialGrid.vertical_append_one (PartialGrid.single_gridt h)
        (PartialGrid.empty (head :: tail) (to_over d) (by simp) h2 to_over_len_pos is_true_over)
      use PartialGrid.vertical_append_one (PartialGrid.single_gridt h)
        (PartialGrid.empty (head :: tail) (to_over d) (by simp) h2 to_over_len_pos is_true_over)
      constructor
      simp [PartialGrid.length]
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, ← List.append_assoc]
    use PartialGrid.empty (a2 ++ a) b (by rw [List.length_append]; omega) (is_false_of_false_false h2 ha1) (by assumption) hb
    simp [PartialGrid.length]
    exact ⟨trivial⟩
  | horizontal_append_one g1 g2 ih1 ih2 =>
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    have H : a2 ++ bot1 ++ [] ++ bot2 ++ mid2 = a2 ++ (bot1 ++ bot2) ++ mid2 := by simp
    rw [← H]
    use PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos_iff.mpr h3)) ih1.1 g2
    simp [PartialGrid.length]
    exact ih1.2
  | horizontal_append h g1 g2 ih1 ih2 =>
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    rw [← List.append_assoc, ← List.append_assoc]
    use PartialGrid.horizontal_append (by simp; exact Or.inl (List.length_pos_iff.mpr h3)) ih1.1 g2
    simp [PartialGrid.length]
    exact ih1.2
  | vertical_append_one g1 g2 ih1 ih2 =>
    rw [← List.append_assoc]
    use PartialGrid.vertical_append_one g1 ih2.1
    simp [PartialGrid.length]
    exact ih2.2
  | vertical_append g1 g2 h ih1 ih2 =>
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    use PartialGrid.vertical_append g1 ih2.1 h
    simp [PartialGrid.length]
    exact ih2.2

noncomputable def splittable_vertically_of_pg' (h : PartialGrid a b c d e) : split_vertically_pg' h := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp only [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | top_bottom i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | sides i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | top_left i =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | adjacent i k h =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
    | separated i j h =>
      intro b₁ b₂ b_is b₁_len b₂_len
      simp only [to_over] at b_is
      apply congr_arg List.length at b_is
      simp [List.length_cons, List.length_nil, zero_add, List.length_append] at b_is
      omega
  | empty a b ha ha1 hb hb1 =>
    intro b₁ b₂ b_is b₁_len b₂_len
    right
    use a ++ b₁
    have itb₁ : is_true b₁ := by
      rw [b_is] at hb1
      exact (is_true_append hb1).1
    use b₂
    use PartialGrid.empty a b₁ ha ha1 b₁_len itb₁
    constructor
    · exact ⟨by simp [PartialGrid.length]⟩
    constructor
    · exact ⟨rfl⟩
    constructor
    · constructor
      rw [b_is]
      simp
    exact ⟨rfl⟩
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    intro b₃ b₄ b_is b₃_len b₄_len
    rcases List.append_eq_append' b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
    · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
      · left
        rw [silly, List.append_nil] at one
        rw [silly, List.nil_append] at two
        rw [one.1, ← two.1]
        use up1, bot1, [], bot2, mid2
        use g1, g2
        simp [one.1, two.1, PartialGrid.length]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
      rcases g2_ih _ _ two.1 fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
      · left
        rw [one.1]
        use mid, (bot1 ++ c1), d1, c2, d2
        use PartialGrid.horizontal_append_one g1 h1
        use h2
        constructor
        · constructor
          rw [List.append_assoc, long, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
        constructor
        simp [PartialGrid.length, h_len, ← add_assoc]
      right
      rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
      rw [one.1]
      use d1, d2
      use PartialGrid.horizontal_append_one g1 h3
      constructor
      · exact ⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩
      exact end_is
    rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
    · left
      rw [silly, List.append_nil] at one
      rw [silly, List.nil_append] at two
      rw [← one.1, two.1]
      use up1, bot1, [], bot2, mid2, g1, g2
      simp [one.1, two.1, PartialGrid.length]
      exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    rcases g1_ih _ _ one.1 b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
    · left
      rw [two.1]
      use mid, c1, d1
      match d2 with
      | [] =>
        use c2 ++ bot2, mid2
        use h1
        use PartialGrid.horizontal_append_one h2 g2
        rw [List.append_nil, List.append_nil] at long
        constructor
        · rw [long]
          exact ⟨by simp⟩
        exact ⟨by simp [PartialGrid.length, h_len, ← add_assoc]⟩
      | d21 :: d22 =>
        use c2, d21 :: d22 ++ bot2 ++ mid2
        use h1
        use PartialGrid.horizontal_append (by simp) h2 g2
        repeat rw [List.append_nil] at long
        simp [long, h_len, PartialGrid.length, ← add_assoc]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    right
    rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
    have H := PartialGrid.left_length_pos g2
    rw [end_is.1.1] at H
    simp at H
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 b2 bot2 mid2 up2
    intro b₃ b₄ b_is b₃_len b₄_len
    rcases List.append_eq_append' b_is with ⟨from_middle, one, two⟩ | ⟨to_middle, one, two⟩
    · rcases List.cases_C from_middle with ⟨⟨silly⟩⟩ | ⟨⟨fm_l⟩⟩
      · left
        rw [silly, List.append_nil] at one
        rw [silly, List.nil_append] at two
        rw [one.1, ← two.1]
        use up1, bot1, mid1, bot2, mid2
        use g1, g2
        simp [one.1, two.1, PartialGrid.length]
        exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
      rcases g2_ih _ _ two.1 fm_l b₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
      · left
        rw [one.1]
        use mid, bot1, (mid1 ++ c1 ++ d1), c2, d2
        use PartialGrid.horizontal_append h g1 h1
        use h2
        constructor
        · constructor
          rw [List.append_assoc, long]
          simp
        constructor
        simp [PartialGrid.length, h_len, ← add_assoc]
      right
      rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
      rw [one.1]
      use (mid1 ++ bot2 ++ d1), d2
      use PartialGrid.horizontal_append h g1 h3
      constructor
      · exact ⟨by rw [PartialGrid.length, h_len.1, PartialGrid.length]⟩
      constructor
      · exact end_is.1
      constructor
      · rw [end_is.2.1.1]
        simp
        exact ⟨trivial⟩
      exact end_is.2.2
    rcases List.cases_C to_middle with ⟨⟨silly⟩⟩ | ⟨⟨tm_l⟩⟩
    · left
      rw [silly, List.append_nil] at one
      rw [silly, List.nil_append] at two
      rw [← one.1, two.1]
      use up1, bot1, mid1, bot2, mid2, g1, g2
      simp [one.1, two.1, PartialGrid.length]
      exact ⟨⟨trivial⟩, ⟨trivial⟩⟩
    rcases g1_ih _ _ one.1 b₃_len tm_l with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨h_len⟩⟩ | bad
    · left
      rw [two.1]
      use mid, c1, d1
      match d2 with
      | [] =>
        use c2 ++ bot2, mid2
        use h1
        use PartialGrid.horizontal_append_one h2 g2
        rw [List.append_nil] at long
        constructor
        · rw [← List.append_assoc,← List.append_assoc, long]
          exact ⟨by simp⟩
        exact ⟨by simp [PartialGrid.length, h_len, ← add_assoc]⟩
      | d21 :: d22 =>
        use c2, d21 :: d22 ++ bot2 ++ mid2
        use h1
        use PartialGrid.horizontal_append (by simp) h2 g2
        simp [← List.append_assoc, long, h_len, PartialGrid.length, ← add_assoc]
        exact ⟨⟨by simp⟩, ⟨trivial⟩⟩
    right
    rcases bad with ⟨d1, d2, h3, h_len, end_is⟩
    have H := PartialGrid.left_length_pos g2
    rw [end_is.1.1] at H
    simp at H
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 up1 a2 bot2 mid2 up2
    intro a₃ a₄ a_is a₃_len a₄_len
    rcases g1_ih _ _ a_is a₃_len a₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨len⟩⟩ | bad
    · match d1 with
      | [] =>
        match d2 with
        | [] =>
          left
          rw [List.append_nil, List.append_nil, List.append_nil] at long
          have hc1 : c1.length > 0 := by
            match c1 with
            | [] =>
              exact (not_both_empty_early h1 rfl rfl).elim
            | co :: ct => simp
          have hc2 : c2.length > 0 := by
             match c2 with
            | [] =>
              exact (not_both_empty_early h2 rfl rfl).elim
            | co :: ct => simp
          rcases g2_ih _ _ long hc1 hc2 with ⟨mid2, c3, d3, c4, d4, i1, i2, long1, len1⟩ | bad
          · use mid2 ++ mid, c3, d3, c4, d4
            use PartialGrid.vertical_append_one h1 i1
            use PartialGrid.vertical_append_one h2 i2
            constructor
            · exact long1
            constructor
            simp [PartialGrid.length, len1.1, len]
            omega
          rcases bad with ⟨d1, d2, h3, len1⟩
          match up2 with
          | [] =>
            use mid, bot2, d1, c2, []
            use PartialGrid.vertical_append_one h1 h3
            use h2
            constructor
            · constructor
              rw [List.append_assoc, List.append_assoc]
              apply (List.append_right_inj bot2).mpr
              rw [List.append_nil, len1.2.2.1.1]
              simp
              exact len1.2.2.2.1.symm
            constructor
            simp [PartialGrid.length, len, ← len1.1.1]
            omega
          | d21 :: d22 =>
            exfalso
            simp at len1
            exact len1.2.1.1
        | d21 :: d22 =>
          have H : is_true bot1 := by exact g2.top_frontier_is_true
          simp at long
          rw [long] at H
          have H2 := middle_frontier_nil_or_caps h2
          rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
          · simp at H2
            exact H2.1.elim
          rw [spec.1] at H
          specialize H (front, false)
          simp [is_true] at H
          exact (H ⟨trivial⟩).1.elim
      | d11 :: d12 =>
        have H : is_true bot1 := by exact g2.top_frontier_is_true
        simp only [List.append_nil, List.append_assoc] at long
        rw [long] at H
        have H2 := middle_frontier_nil_or_caps h1
        rcases H2 with H2 | ⟨front, mid, caboose, spec⟩
        · simp at H2
          exact H2.1.elim
        rw [spec.1] at H
        specialize H (front, false)
        simp [is_true] at H
        exact (H ⟨trivial⟩).1.elim
    rcases bad with ⟨d1, d2, h3, ⟨len⟩, up1_is, ⟨d1h2_empty⟩, ⟨a2h4⟩⟩
    rw [up1_is.1] at g1
    right
    exact (pg_not_mid_right_empty g1).elim
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 a2 bot2 mid2 up2
    intro a₃ a₄ a_is a₃_len a₄_len
    rcases g1_ih _ _ a_is a₃_len a₄_len with ⟨mid, c1, d1, c2, d2, h1, h2, ⟨long⟩, ⟨len⟩⟩ | bad
    · match d1 with
      | [] =>
        have both_c : is_true (c1 ++ c2) :=
            is_true_of_true_true h1.bottom_frontier_is_true h2.bottom_frontier_is_true
        have bot1_is : bot1 = c1 ++ c2 := by
          rw [List.append_nil] at long
          rcases middle_frontier_nil_or_caps g1 with H | ⟨front, mid, caboose, spec⟩
          · rw [H.1] at h
            simp at h
          rw [spec.1] at long
          rcases middle_frontier_nil_or_caps h2 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp [H.1] at long
            rw [← long] at both_c
            specialize both_c (front, false)
            simp [is_true] at both_c
            exact (both_c ⟨trivial⟩).1.elim
          rw [spec1.1] at long
          rcases list_splits_somewhere long with ⟨h1⟩ | ⟨tm, one, two⟩ | ⟨fm, one, two⟩
          · exact h1.1
          · match tm with
            | [] =>
              simp at one
              exact one
            | (a, true) :: a1 =>
              simp at two
            | (a, false) :: a1 =>
              have H : is_true bot1 := g2.top_frontier_is_true
              rw [one] at H
              specialize H (a, false)
              simp at H
              exact (H ⟨trivial⟩).1.elim
          match fm with
          | [] =>
            rw [List.append_nil] at one
            exact one
          | (a, true) :: a1 =>
            simp at two
          | (a, false) :: a1 =>
            rw [← one] at both_c
            specialize both_c (a, false)
            simp at both_c
            exact (both_c ⟨trivial⟩).1.elim
        have mid_is : mid1 = d2 := by
          simp [bot1_is] at long
          exact long
        have c1_len : c1.length > 0 := by
          match c1 with
          | [] =>
            exact (not_both_empty_early h1 rfl rfl).elim
          | c11 :: c12 => simp
        match c2 with
        | [] =>
          left
          use up2 ++ mid, bot2, mid2, [], up2++ [] ++ d2
          rw [List.append_nil] at bot1_is
          subst bot1_is
          use PartialGrid.vertical_append_one h1 g2
          match up2 with
          | [] =>
            use h2
            constructor
            · constructor
              simp [mid_is]
            simp [PartialGrid.length, len]
            exact ⟨by omega⟩
          | up21 :: up22 =>
            use (PartialGrid.extend_bottom_w_len h2 (up21 :: up22) (PartialGrid.right_frontier_is_false g2) (by simp)).1
            constructor
            · constructor
              simp [mid_is]
            constructor
            simp [PartialGrid.length, len,
              (PartialGrid.extend_bottom_w_len h2 (up21 :: up22) (PartialGrid.right_frontier_is_false g2) (by simp)).2.1]
            omega
        | c21 :: c22 =>
          left
          rcases g2_ih _ _  bot1_is c1_len (by simp) with
              ⟨mid3, c3, d3, c4, d4, i1, i2, long1, len1⟩ | ⟨d1, d2', h3, ⟨len1⟩, rest⟩
          · use mid3 ++ mid, c3, d3, c4
            match d2 with
            | [] =>
              exfalso
              rw [mid_is] at h
              simp at h
            | d21 :: d22 =>
              use d4 ++ up2 ++ d21 :: d22
              use PartialGrid.vertical_append_one h1 i1
              use PartialGrid.vertical_append h2 i2 (by simp)
              constructor
              · constructor
                rw [← List.append_assoc, ← List.append_assoc, long1.1, mid_is]
                simp
              constructor
              simp [PartialGrid.length, len1.1, len]
              omega
          use mid, bot2, d1, c21::c22, d2
          use PartialGrid.vertical_append_one h1 h3
          use h2
          constructor
          · constructor
            rw [rest.2.1.1, mid_is, rest.1.1, rest.2.2.1]
            simp
          simp [PartialGrid.length, len1, len]
          exact ⟨by omega⟩
      | d11 :: d12 =>
        have H0 : is_true bot1 := by exact g2.top_frontier_is_true
        have bot1_is : bot1 = c1 := by
          rcases middle_frontier_nil_or_caps h1 with H | ⟨front, mid, caboose, spec⟩
          · simp at H
            exact H.1.elim
          rw [spec.1] at long
          rcases middle_frontier_nil_or_caps g1 with H | ⟨front1, mid1, caboose1, spec1⟩
          · simp [H.1] at long
            rw [long] at H0
            specialize H0 (front, false)
            simp [is_true] at H0
            specialize H0 ⟨trivial⟩
            exact H0.1.elim
          rw [spec1.1] at long
          simp at long
          rcases list_splits_somewhere long with ⟨h1⟩ | ⟨tm, one, two⟩ | ⟨fm, one, two⟩
          · exact h1.1
          · match tm with
            | [] =>
              simp at one
              exact one
            | (a, true) :: a1 =>
              simp at two
            | (a, false) :: a1 =>
              rw [one] at H0
              specialize H0 (a, false)
              simp at H0
              exact (H0 ⟨trivial⟩).1.elim
          match fm with
          | [] =>
            rw [List.append_nil] at one
            exact one
          | (a, true) :: a1 =>
            simp at two
          | (a, false) :: a1 =>
            have H36 : is_true c1 := h1.bottom_frontier_is_true
            rw [← one] at H36
            specialize H36 (a, false)
            simp at H36
            exact (H36 ⟨trivial⟩).1.elim
        simp [bot1_is] at long
        match c1 with
        | [] =>
          rw [bot1_is] at g2
          exfalso
          have H := PartialGrid.top_length_pos g2
          simp at H
        | c11 :: c12 =>
          left
          use mid, bot2, mid2 ++ up2 ++ (d11 :: d12), c2, d2
          subst bot1_is
          use PartialGrid.vertical_append h1 g2 (by simp)
          use h2
          constructor
          · constructor
            simp [long]
          simp [PartialGrid.length, len]
          exact ⟨by omega⟩
    rcases bad with ⟨d1, d2, h3, ⟨len⟩, ⟨up1_nil⟩, ⟨mid1_is⟩, ⟨a4d2⟩⟩
    right
    use mid2++ up2 ++d1, d2
    have H : d1.length > 0 := by
      match d1 with
      | [] =>
        exfalso
        apply not_both_empty h3 rfl rfl
      | d11 :: d12 => simp
    use PartialGrid.vertical_append h3 g2 H
    constructor
    · simp [PartialGrid.length, len]
      exact ⟨trivial⟩
    constructor
    · exact ⟨up1_nil⟩
    constructor
    · constructor
      simp [mid1_is]
    exact ⟨a4d2⟩

noncomputable def PartialGrid.extend_side_w_len  (h : PartialGrid a b c d e) (b2) (h2 : is_true b2) (h3 : b2 ≠ []) :
    (h1 : PartialGrid a (b ++ b2) c (d ++ e ++ b2) []) × PLift  (h.length = h1.length) := by
  induction h with
  | single_gridt h =>
    cases b2 with
    | nil => simp at h3
    | cons head tail =>
      rename_i c d
      have H : [] ++ to_over d = to_over d ++ [] := by simp
      rw [List.nil_append]
      have H1 := PartialGrid.horizontal_append_one (PartialGrid.single_gridt h)
          (PartialGrid.empty (to_up c) (head :: tail) to_up_len_pos is_false_up (by simp) h2)
      rw [← H] at H1
      use H1
      sorry
  | empty a b ha ha1 hb hb =>
    rw [List.append_nil, List.append_assoc]
    use PartialGrid.empty a (b ++ b2) ha ha1 (by rw [List.length_append]; omega) (is_true_of_true_true hb h2)
    simp [PartialGrid.length]
    exact ⟨trivial⟩
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rw [List.append_assoc]
    use PartialGrid.horizontal_append_one g1 g2_ih.1
    simp [PartialGrid.length]
    exact g2_ih.2
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 b3 bot3 mid3 up3
    have H1 : mid1 ++ bot3 ++ (mid3 ++ up3 ++ b2) = mid1 ++ bot3 ++ mid3 ++ up3 ++ b2 := by simp
    rw [List.append_assoc, ← H1]
    use PartialGrid.horizontal_append h g1 g2_ih.1
    simp [PartialGrid.length]
    exact g2_ih.2
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    rename_i a1 b1 bot1 up1 a3 bot3 mid3 up3
    have H : mid3 ++ (up3 ++ up1) ++ b2 = mid3 ++ up3 ++ ([] ++ up1 ++ b2) := by simp
    rw [H]
    use PartialGrid.vertical_append g1_ih.1 g2 (by simp; exact Or.inr (List.length_pos_iff.mpr h3))
    simp [PartialGrid.length]
    exact g1_ih.2
  | vertical_append g1 g2 h g1_ih g2_ih =>
    rename_i a1 b1 bot1 mid1 up1 a3 bot3 mid3 up3
    have H : mid3 ++ up3 ++ mid1 ++ up1 ++ b2 = mid3 ++ up3 ++ (mid1 ++ up1 ++ b2) := by simp
    rw [H]
    use PartialGrid.vertical_append g1_ih.1 g2 (by simp; exact Or.inr (Or.inr (List.length_pos_iff.mpr h3)))
    simp [PartialGrid.length]
    exact g1_ih.2

theorem horizontal_one_helper (g1 : PartialGrid a1 b1 bot1 [] up1)
    (g2 : PartialGrid up1 b2 bot2 mid2 up2)
    (rm : remove_ones (a1 ++ (b1 ++ b2)) = remove_ones (bot1 ++ bot2 ++ mid2 ++ up2)) :
    remove_ones a1 ++ remove_ones b1 = remove_ones bot1 ++ remove_ones up1 := by
  induction a1 using List.reverseRecOn generalizing b1 bot1 up1 b2 bot2 mid2 up2 with
  | nil =>
    have H := PartialGrid.left_length_pos g1
    simp at H
  | append_singleton front caboose ih =>
    sorry


theorem skeleton_length_pg (h : PartialGrid a b c d e) : remove_ones (a ++ b) = remove_ones (c ++ d ++ e) → h.length = 0 := by
  induction h with
  | single_gridt h =>
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i =>
      intro rm
      simp [to_up, to_over, remove_ones] at rm
    | adjacent i k h =>
      intro rm
      simp [to_up, to_over, remove_ones] at rm
    | separated i j h =>
      intro rm
      simp [to_up, to_over, remove_ones] at rm
  | empty a b ha ha1 hb hb => simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    simp only [remove_ones_append, List.append_nil] at g1_ih
    simp only [remove_ones_append, List.append_assoc] at g2_ih
    intro rm
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    have hg1 : g1.length = 0 := by
      apply g1_ih
      sorry
    have hg2 : g2.length = 0 := by
      apply g2_ih
      sorry
    rw [PartialGrid.length, hg1, hg2]
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    simp only [remove_ones_append, List.append_nil] at g1_ih
    simp only [remove_ones_append, List.append_assoc] at g2_ih
    intro rm
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    have hg1 : g1.length = 0 := by
      apply g1_ih
      sorry
    have hg2 : g2.length = 0 := by
      apply g2_ih
      sorry
    rw [PartialGrid.length, hg1, hg2]
  | vertical_append_one g1 g2 g1_ih g2_ih =>
    simp only [remove_ones_append, List.append_nil] at g1_ih
    simp only [remove_ones_append, List.append_assoc] at g2_ih
    intro rm
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    have hg1 : g1.length = 0 := by
      apply g1_ih
      sorry
    have hg2 : g2.length = 0 := by
      apply g2_ih
      sorry
    rw [PartialGrid.length, hg1, hg2]
  | vertical_append g1 g2 h g1_ih g2_ih =>
    simp only [remove_ones_append, List.append_nil] at g1_ih
    simp only [remove_ones_append, List.append_assoc] at g2_ih
    intro rm
    rename_i a1 b1 bot1 up1 b2 bot2 mid2 up2
    have hg1 : g1.length = 0 := by
      apply g1_ih
      sorry
    have hg2 : g2.length = 0 := by
      apply g2_ih
      sorry
    rw [PartialGrid.length, hg1, hg2]

theorem same_type_same_length_pg (g1 : PartialGrid a b c d e) (g2 : PartialGrid a1 b1 c1 d1 e1) :
    a = a1 → b = b1 → remove_ones (c ++ d++ e) = remove_ones (c1 ++ d1 ++ e1) → g1.length = g2.length := by
  induction g1 generalizing g2 with
  | single_gridt h =>
    rename_i f g l m
    intro a1_is a2_is rm
    cases h with
    | empty =>
      simp [PartialGrid.length]
      simp [to_up] at a1_is
      simp [to_over] at a2_is
      exact (all_ones_length_pg _ a1_is.symm a2_is.symm).symm
    | top_bottom i =>
      simp [PartialGrid.length]
      simp [to_up] at a1_is
      simp [to_over] at a2_is
      exact (top_bottom_length_pg _ a1_is.symm a2_is.symm).symm
    | sides i =>
      simp [PartialGrid.length]
      simp [to_up] at a1_is
      simp [to_over] at a2_is
      exact (side_side_length_pg _ a1_is.symm a2_is.symm).symm
    | top_left i =>
      simp [PartialGrid.length]
      simp [to_up] at a1_is
      simp [to_over] at a2_is
      simp only [to_over, List.append_nil, to_up, List.cons_append, List.nil_append, remove_ones] at rm
      exact (top_left_length_pg _ a1_is.symm a2_is.symm rm.symm).symm
    | adjacent i j h =>
      simp [PartialGrid.length]
      simp [to_up] at a1_is
      simp [to_over] at a2_is
      simp only [to_over_cons_cons, to_over_singleton, List.append_nil, to_up_cons_cons,
        to_up_singleton, List.cons_append, List.nil_append, remove_ones] at rm
      exact (adjacent_length_pg _ a1_is.symm a2_is.symm rm.symm h).symm
    | separated i j h =>
      simp [PartialGrid.length]
      simp [to_up] at a1_is
      simp [to_over] at a2_is
      simp only [to_over, List.map_cons, List.map_nil, List.append_nil, to_up, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append, remove_ones] at rm
      exact (separated_length_pg _ a1_is.symm a2_is.symm rm.symm (or_dist_iff.mpr h)).symm
  | empty a b ha ha1 hb hb1 =>
    intro a1_is a2_is rm
    simp [PartialGrid.length]
    rw [a1_is, a2_is, List.nil_append, List.append_nil] at rm
    exact (skeleton_length_pg _ rm).symm
  | horizontal_append_one g1 g2 g1_ih g2_ih => sorry
  | horizontal_append h g1 g2 g1_ih g2_ih => sorry
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry

theorem unique_g_pg_c
    (g1 : PartialGrid a2 b2 bot2 [] up2)
    (ha : to_up a1 = a2)
    (b4_is : to_over b4 = b2)
    (b9 : gridt a1 b4 b6 b7) : to_up b6 = up2 ∧ to_over b7 = bot2 := by
    have H := gridt_of_PartialGrid g1
    unfold gridt_option at H
    have H3 := unicity_c b9 H
    sorry

theorem to_up_inj (h : to_up a = to_up b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons head tail =>
      simp [to_up] at h
      have H2 : List.getLast? [(none, false)] =
        List.getLast? ((List.map (fun x ↦ (some x, false)) tail).reverse ++ [(some head, false)]) := by
        rw [h]
      simp at H2
  | cons head tail ih =>
    cases b with
    | nil =>
      simp [to_up] at h
      have H2 : List.getLast? [(none, false)] =
        List.getLast? ((List.map (fun x ↦ (some x, false)) tail).reverse ++ [(some head, false)]) := by
        rw [h]
      simp at H2
    | cons headb tailb =>
      simp [to_up] at h
      have H2 : List.getLast? ((List.map (fun x ↦ (some x, false)) tail).reverse ++ [(some head, false)]) =
        List.getLast? ((List.map (fun x ↦ (some x, false)) tailb).reverse ++ [(some headb, false)]) := by
        rw [h]
      simp at H2
      simp [H2]
      apply ih
      rw [← H2] at h
      simp at h
      cases tail with
      | nil =>
        cases tailb with
        | nil => rfl
        | cons t1 t2 => simp at h
      | cons t1 t2 =>
        cases tailb with
        | nil =>
          simp at h
        | cons t3 t4 =>
          simp only [to_up]
          simp at h
          simp [h]

theorem to_over_inj (h : to_over a = to_over b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons head tail =>
      simp [to_over] at h
  | cons head tail ih =>
    cases b with
    | nil =>
      simp [to_over] at h
    | cons headb tailb =>
      simp [to_over] at h
      simp [h]
      apply ih
      cases tail with
      | nil =>
        cases tailb with
        | nil => rfl
        | cons t1 t2 => simp at h
      | cons t3 t4 =>
        cases tailb with
        | nil => simp at h
        | cons t1 t2 =>
          simp [to_over]
          simp at h
          exact h.2

theorem straight_pg_sm_g (h : PartialGrid a b c d e) (h1 : gridt a1 b1 f g)
    : a <+: to_up a1 → b <+: to_over b1 → h.length ≤ h1.length := by
  induction h generalizing a1 b1 f g with
  | single_gridt h =>
    intro ha hb
    cases h with
    | empty => simp [PartialGrid.length]
    | top_bottom i => simp [PartialGrid.length]
    | sides i => simp [PartialGrid.length]
    | top_left i =>
      simp [PartialGrid.length]
      rcases ha with ⟨ra, hra⟩
      rcases hb with ⟨rb, hrb⟩
      have H1 : ∃ rra, a1 = .of i * rra := by sorry
      have H2 : ∃ rrb, b1 = .of i * rrb := by sorry
      rcases H1 with ⟨rra, dsa⟩
      rcases H2 with ⟨rrb, dsb⟩
      rcases splittable_horizontally_of_gridn h1 _ _ dsa with ⟨rest, c1, c2, g1, g2, ⟨c_is⟩, ⟨len1⟩⟩
      rcases splittable_vertically_of_gridn g1 _ _ dsb with ⟨rest2, d1, d2, g3, g4, ⟨d_is⟩, ⟨len2⟩⟩
      rw [len1, len2, gridt_length_top_left g3 rfl rfl]
      omega
      -- rw [PartialGrid.length, gridt_length_top_left h1 _ (to_over_inj hb)]
    | adjacent i k h =>
      sorry -- rw [PartialGrid.length, gridt_length_adjacent h1 (to_up_inj ha) (to_over_inj hb) h]
    | separated i j h =>
      sorry --rw [PartialGrid.length, gridt_length_separated h1 (to_up_inj ha) (to_over_inj hb) (or_dist_iff.mpr h)]
  | empty a b ha ha1 hb hb =>
    simp [PartialGrid.length]
  | horizontal_append_one g1 g2 g1_ih g2_ih =>
    rename_i a2 b2 bot2 up2 b3 bot3 mid3 up3
    intro ha hb
    have b2_ne_nil : b2 ≠ [] := by
      intro hb2
      rw [hb2] at g1
      have H := PartialGrid.top_length_pos g1
      simp at H
    have b3_neq_nil : b3 ≠ [] := by
      intro hb3
      rw [hb3] at g2
      have H := PartialGrid.top_length_pos g2
      simp at H
    have H : ∃ b4 b5, to_over b5 = b3 ∧ to_over b4 = b2 ∧ ((b4 ++ b5) <+: b1) := by
      sorry
    rcases H with ⟨b4, b5, b5_is, b4_is, H⟩
    rcases H with ⟨rest, hr⟩
    rcases splittable_vertically_of_gridn h1 _ _ hr.symm with ⟨b6, b7, b8, b9, gt, ⟨g_is⟩, ⟨len⟩⟩
    specialize g1_ih b9 ha
    rw [len]
    have b45_ne_nil : b4 ++ b5 ≠ [] := by
      intro hb45
      have hb4 : b4 = [] ∧ b5 = [] := List.append_eq_nil_iff.mp hb45
      rw [hb4.1] at b4_is
      rw [hb4.2] at b5_is
      simp [to_over] at b4_is
      simp [to_over] at b5_is
      rw [← b4_is, ← b5_is] at hb
      cases b1 with
      | h0 =>
        change _ <+: [(none, true)] at hb
        simp [List.cons_prefix_cons, List.prefix_nil, List.cons_ne_self, and_false] at hb
      | ih x xs =>
        change _ <+: (some x, true) :: List.map (fun x ↦ (some x, true)) xs at hb
        simp at hb
    have nonsense : b2 <+: to_over (Append.append b4 b5)  := by
      have h1 : b2 <+: to_over b4 := by
        rw [b4_is]
      simp [b45_ne_nil, to_over]
      cases h : Append.append b4 b5
      · apply (b45_ne_nil h).elim
      rename_i head tail
      simp only
      rw [← h]
      change b2 <+: List.map (fun x ↦ (some x, true)) (b4 ++ b5)
      rw [List.map_append]
      refine List.prefix_of_append ?_
      sorry


    specialize g1_ih nonsense
    simp [PartialGrid.length]
    apply Nat.add_le_add g1_ih
    apply g2_ih
    --have hb6 : to_up b6 = up2 := (unique_g_pg_c g1 ha b4_is b9).1
    sorry
    sorry
  | horizontal_append h g1 g2 g1_ih g2_ih =>
    rename_i a3 b3 bot3 mid3 up3 b4 bot4 mid4 up4
    intro ha hb
    have b3_ne_nil : b3 ≠ [] := by
      intro hb3
      rw [hb3] at g1
      have H := PartialGrid.top_length_pos g1
      simp at H
    have b4_neq_nil : b4 ≠ [] := by
      intro hb4
      rw [hb4] at g2
      have H := PartialGrid.top_length_pos g2
      simp at H
    have H : ∃ b5 b6, to_over b6 = b4 ∧ to_over b5 = b3 ∧ b1 = b5 ++ b6 := by
      sorry
    rcases H with ⟨b5, b6, b6_is, b5_is, H⟩
    rcases splittable_vertically_of_gridn h1 b5 b6 H with ⟨b7, b8, b9, b10, gt, ⟨g_is⟩, ⟨len⟩⟩
    specialize g1_ih b10 ha
    rw [len]
    specialize g1_ih b5_is
    simp [PartialGrid.length]
    apply Nat.add_le_add g1_ih
    have hb7 : to_up b7 = up3 := by sorry
    apply g2_ih _ hb7 b6_is
  | vertical_append_one g1 g2 g1_ih g2_ih => sorry
  | vertical_append g1 g2 h g1_ih g2_ih => sorry
