import BraidProject.StepTwo_C_basic_eq
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
