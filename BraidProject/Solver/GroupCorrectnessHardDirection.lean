import BraidProject.BraidLocalization
import BraidProject.Solver.GroupCorrectness
import BraidProject.Solver.MonoidCorrectnessHardDirection

namespace Braid

theorem braid_word_solver_true_of_BraidGroupInf_eq
    (h : BraidGroupInf.mk (FreeGroup.mk a) = BraidGroupInf.mk (FreeGroup.mk b)) :
    braid_word_solver a b = true := by
  apply monoid_solver_true_of_BraidMonoidInf_eq
  rcases dede : (reverse_word (a ++ (FreeGroup.invRev b))).ordered with ⟨d, e, hde⟩
  have d_is : (reverse_word (a ++ FreeGroup.invRev b)).ordered.fst = d := by aesop
  have e_is : (reverse_word (a ++ FreeGroup.invRev b)).ordered.2.1 = e := by
    rw [dede]
  rw [d_is, e_is]
  have H2 := SemiThueData.reversing.to_braid_group_equiv ((reverse_word (a ++ (FreeGroup.invRev b))).derivation)
  rw [hde.1.2.2, ← FreeGroup.mul_mk, map_mul, h, ← FreeGroup.inv_mk,
    map_inv, mul_inv_cancel, ← FreeGroup.mul_mk, map_mul] at H2
  apply (mul_left_inj (BraidGroupInf.mk (FreeGroup.mk e))⁻¹).mpr at H2
  rw [one_mul, mul_inv_cancel_right, ← map_inv, FreeGroup.inv_mk] at H2
  have := braidMonoid_mk_eq_of_braidGroup_mk_eq_of_positive H2 hde.1.1 (FreeGroup.invRev_true hde.1.2.1)
  rw [← this]
  simp only [List.map_reverse, FreeGroup.invRev, List.map_map]
  rfl

theorem braid_word_solver_correct : braid_word_solver a b ↔
    BraidGroupInf.mk (FreeGroup.mk a) = BraidGroupInf.mk (FreeGroup.mk b) :=
  ⟨BraidGroupInf.eq_of_braid_word_solver_true, braid_word_solver_true_of_BraidGroupInf_eq⟩

--start with elements of the free group
def free_group_elem_braid_solver (a b : FreeGroup ℕ) : Bool := by
  apply @Quot.lift₂ _ _ _ FreeGroup.Red.Step FreeGroup.Red.Step braid_word_solver _ _ a b
  · intro a1 b1 c1 relsy
    have HAC := Quot.sound relsy
    change FreeGroup.mk _ = FreeGroup.mk _ at HAC
    cases hi : braid_word_solver a1 b1
    · symm
      apply eq_false_of_ne_true
      intro h1
      apply BraidGroupInf.eq_of_braid_word_solver_true at h1
      rw [← HAC] at h1
      apply braid_word_solver_true_of_BraidGroupInf_eq at h1
      aesop
    apply braid_word_solver_correct.1 at hi
    symm
    apply braid_word_solver_true_of_BraidGroupInf_eq
    rw [← HAC, hi]
  intro a1 b1 c1 relsy
  have HBC := Quot.sound relsy
  change FreeGroup.mk _ = FreeGroup.mk _ at HBC
  cases hi : braid_word_solver a1 c1
  · symm
    apply eq_false_of_ne_true
    intro h1
    apply BraidGroupInf.eq_of_braid_word_solver_true at h1
    rw [← HBC] at h1
    apply braid_word_solver_true_of_BraidGroupInf_eq at h1
    aesop
  apply braid_word_solver_correct.1 at hi
  symm
  apply braid_word_solver_true_of_BraidGroupInf_eq
  rw [← HBC, hi]

theorem free_group_elem_braid_solver_correct : free_group_elem_braid_solver a b ↔
    BraidGroupInf.mk a = BraidGroupInf.mk b := by
  rcases Quot.exists_rep a with ⟨a, rfl⟩
  rcases Quot.exists_rep b with ⟨b, rfl⟩
  exact braid_word_solver_correct

def braid_solver (a b : BraidGroupInf) : Bool := by
  apply Quotient.lift₂ free_group_elem_braid_solver _ a b
  intro a b c d hac hbd
  have HAC := Quotient.sound hac
  change BraidGroupInf.mk a = BraidGroupInf.mk c at HAC
  have HBD := Quotient.sound hbd
  change BraidGroupInf.mk b = BraidGroupInf.mk d at HBD
  cases hi : free_group_elem_braid_solver a b
  · symm
    apply eq_false_of_ne_true
    intro h1
    apply free_group_elem_braid_solver_correct.1 at h1
    rw [← HAC, ← HBD] at h1
    apply free_group_elem_braid_solver_correct.2 at h1
    aesop
  apply free_group_elem_braid_solver_correct.1 at hi
  symm
  apply free_group_elem_braid_solver_correct.2
  aesop

theorem braid_solver_correct {a b : BraidGroupInf} : braid_solver a b ↔ a = b := by
  rcases Quotient.exists_rep a with ⟨a, rfl⟩
  rcases Quotient.exists_rep b with ⟨b, rfl⟩
  exact free_group_elem_braid_solver_correct

instance braid_decidable :
    DecidableEq (BraidGroupInf) := by
  intro a b
  by_cases h : braid_solver a b = true
  · exact isTrue (braid_solver_correct.mp h)
  exact isFalse (by
      intro hEq
      apply braid_solver_correct.mpr at hEq
      aesop)

--can be done in this manner because we have an instance of Decidable on BraidGroupInf
def solver_nonsense (a b : BraidGroupInf) : Bool := a = b
