import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Continuous

open Set Real

theorem sub_eq_zero_mine {a b : ℝ} : a-b = 0 → a = b := by
  intro h
  have H : a-b + b = 0 + b := by
    rw [h]
  simp at H
  exact H

theorem mean_value_ratio
    {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℝ}
    (hfcont : ContinuousOn f (Icc a b)) (hgcont : ContinuousOn g (Icc a b))
    (hfdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hgdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x) :
    ∃ x ∈ Ioo a b, (f b - f a) * deriv g x = (g b - g a) * deriv f x := by
  let F := fun x ↦ f x * (g b - g a) - g x * (f b - f a)
  have hFcont : ContinuousOn F (Icc a b) := by
    apply ContinuousOn.sub
    · exact .mul (hfcont) continuousOn_const
    · exact .mul (hgcont) continuousOn_const
  have hFdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ F x := by
    intro x hx
    have H1 : DifferentiableAt ℝ (fun x ↦ f x * (g b - g a)) x :=
      DifferentiableAt.mul_const (hfdiff x hx) (g b - g a)
    have H2 : DifferentiableAt ℝ (fun x ↦ g x * (f b - f a)) x :=
      (hgdiff x hx).mul_const _
    exact (DifferentiableAt.sub_iff_right H1).mpr H2
  have hFab : F a = F b := by
    ring
  obtain ⟨x, hx, hF'⟩ := exists_deriv_eq_zero hab hFcont hFab
  use x, hx
  rw [deriv_sub] at hF'
  apply sub_eq_zero_mine at hF'
  rw [deriv_mul_const, deriv_mul_const] at hF'
  rw [mul_comm] at hF'
  rw [hF', mul_comm]
  · apply hgdiff _ hx
  · apply hfdiff _ hx
  · exact DifferentiableAt.mul_const (hfdiff _ hx) _
  exact DifferentiableAt.mul_const (hgdiff _ hx) _
