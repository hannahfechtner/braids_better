import BraidProject.BraidLocalization
import BraidProject.Solver.GroupCorrectness
import BraidProject.Solver.MonoidCorrectnessHardDirection

namespace Braid

set_option maxHeartbeats 2000000
theorem solver_g_correct_other_direction :
    BraidGroupInf.mk (FreeGroup.mk a) =
    BraidGroupInf.mk (FreeGroup.mk b) →
    group_solver a b = true := by
  intro h
  unfold group_solver
  apply correct_other_dir
  rcases dede : (reverse_word (a ++ (FreeGroup.invRev b))).ordered with ⟨d, e, hde⟩
  have d_is : (reverse_word (a ++ FreeGroup.invRev b)).ordered.fst = d := by aesop
  have e_is : (reverse_word (a ++ FreeGroup.invRev b)).ordered.2.1 = e := by
    rw [dede]
  rw [d_is, e_is]
  have H2 := SemiThueData_reversing_to_braid_group_equiv ((reverse_word (a ++ (FreeGroup.invRev b))).steps)
  rw [hde.1.2.2, ← FreeGroup.mul_mk, map_mul, h, ← FreeGroup.inv_mk,
    map_inv, mul_inv_cancel, ← FreeGroup.mul_mk, map_mul] at H2
  apply (mul_left_inj (BraidGroupInf.mk
    (FreeGroup.mk e))⁻¹).mpr at H2
  rw [one_mul, mul_inv_cancel_right, ← map_inv, FreeGroup.inv_mk] at H2
  have := braidMonoid_mk_eq_of_braidGroup_mk_eq_of_positive H2 hde.1.1 (FreeGroup.invRev_true hde.1.2.1)
  rw [← this]
  simp [FreeGroup.invRev]
  rfl

theorem solver_g_correct : group_solver a b ↔
  BraidGroupInf.mk (FreeGroup.mk a) =
  BraidGroupInf.mk (FreeGroup.mk b) := by
  constructor
  · exact solver_g_correct_one_direction
  exact solver_g_correct_other_direction


--start with elements of the free group
def solver_fg (a b : FreeGroup ℕ) : Bool := by
  apply @Quot.lift₂ _ _ _ FreeGroup.Red.Step FreeGroup.Red.Step group_solver _ _ a b
  · intro a1 b1 c1 relsy
    have HAC := Quot.sound relsy
    change FreeGroup.mk _ = FreeGroup.mk _ at HAC
    cases hi : group_solver a1 b1
    · symm
      apply eq_false_of_ne_true
      intro h1
      apply solver_g_correct_one_direction at h1
      rw [← HAC] at h1
      apply solver_g_correct_other_direction at h1
      aesop
    apply solver_g_correct.1 at hi
    symm
    apply solver_g_correct_other_direction
    rw [← HAC, hi]
  intro a1 b1 c1 relsy
  have HBC := Quot.sound relsy
  change FreeGroup.mk _ = FreeGroup.mk _ at HBC
  cases hi : group_solver a1 c1
  · symm
    apply eq_false_of_ne_true
    intro h1
    apply solver_g_correct_one_direction at h1
    rw [← HBC] at h1
    apply solver_g_correct_other_direction at h1
    aesop
  apply solver_g_correct.1 at hi
  symm
  apply solver_g_correct_other_direction
  rw [← HBC, hi]

theorem solver_fg_correct : solver_fg a b ↔
    BraidGroupInf.mk a =
    BraidGroupInf.mk b := by
  rcases Quot.exists_rep a with ⟨a, rfl⟩
  rcases Quot.exists_rep b with ⟨b, rfl⟩
  exact solver_g_correct

def braid_solver (a b : BraidGroupInf) : Bool := by
  apply Quotient.lift₂ solver_fg _ a b
  intro a b c d hac hbd
  have HAC := Quotient.sound hac
  change BraidGroupInf.mk a = BraidGroupInf.mk c at HAC
  have HBD := Quotient.sound hbd
  change BraidGroupInf.mk b = BraidGroupInf.mk d at HBD
  cases hi : solver_fg a b
  · symm
    apply eq_false_of_ne_true
    intro h1
    apply solver_fg_correct.1 at h1
    rw [← HAC, ← HBD] at h1
    apply solver_fg_correct.2 at h1
    aesop
  apply solver_fg_correct.1 at hi
  symm
  apply solver_fg_correct.2
  aesop

theorem braid_solver_correct {a b : BraidGroupInf} : braid_solver a b ↔ a = b := by
  rcases Quotient.exists_rep a with ⟨a, rfl⟩
  rcases Quotient.exists_rep b with ⟨b, rfl⟩
  exact solver_fg_correct

instance braid_decidable_helper :
    DecidableEq (BraidGroupInf) := by
  intro a b
  by_cases h : braid_solver a b = true
  · exact isTrue (braid_solver_correct.mp h)
  exact isFalse (by
      intro hEq
      apply braid_solver_correct.mpr at hEq
      aesop)

def solver_nonsense (a b : BraidGroupInf) : Bool := a = b
