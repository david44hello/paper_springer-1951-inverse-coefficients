import Springer.HerglotzCoefficients
import Springer.TimeChange

noncomputable section
open MeasureTheory Set Complex Filter
open scoped Topology
namespace Springer

/-- The single moment transform appearing in the time derivative on a fixed contour. -/
def velocityTransform (μ : Measure Circle) (z : ℂ) :=
  ∫ ξ : Circle, (ξ:ℂ)/(1-(ξ:ℂ)*z) ∂μ

private theorem den_ne {z : ℂ} (hz : ‖z‖<1) (ξ : Circle) : 1-(ξ:ℂ)*z≠0 := by
  intro he
  have H := congrArg norm (sub_eq_zero.mp he)
  simp at H
  linarith

theorem velocityTransform_eq (μ : Measure Circle) [IsProbabilityMeasure μ] {z : ℂ} (hz : z∈disc) :
    velocityTransform μ z=if z=0 then circleMoment μ 1 else (circleResolvent μ z-1)/z := by
  by_cases hn : z=0
  · simp [hn,velocityTransform,circleMoment]
  rw [ite_eq_right hn,eq_div_iff hn]
  have hD : ∀ ξ : Circle, 1-(ξ:ℂ)*z≠0 := den_ne (by simpa [disc] using hz)
  have hi : Integrable (fun ξ : Circle => (1-(ξ:ℂ)*z)⁻¹) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop (disch := exact hD)) (HasCompactSupport.of_compactSpace _)
  rw [velocityTransform,circleResolvent,←integral_mul_const]
  have h1 : (1:ℂ)=∫ _ : Circle, (1:ℂ) ∂μ := by simp
  conv_rhs => rhs; rw [h1]
  rw [←integral_sub hi (integrable_const (1:ℂ))]
  apply integral_congr_ae
  filter_upwards with ξ
  field_simp [hD ξ]
  <;> ring

/-- This works on any measurable parameter space, including time times the contour
angle. Only the moments of the moving measures and the disk argument are needed. -/
theorem measurable_velocityTransform {T : Type*} [MeasurableSpace T]
    (μ : T → Measure Circle) [∀ x, IsProbabilityMeasure (μ x)] {z : T → ℂ}
    (hm : ∀ k, Measurable (fun x => circleMoment (μ x) k)) (hz : Measurable z)
    (hd : ∀ x, z x∈disc) : Measurable (fun x => velocityTransform (μ x) (z x)) := by
  have hR : Measurable (fun x => circleResolvent (μ x) (z x)) := by
    have he : (fun x => circleResolvent (μ x) (z x)) =
        fun x => ∑' k : ℕ, z x^k*circleMoment (μ x) k := funext
      (fun x => (resolvent_hasSum (μ x) (hd x)).tsum_eq.symm)
    rw [he]
    exact Measurable.tsum fun k => (hz.pow_const k).mul (hm k)
  simp_rw [velocityTransform_eq _ (hd _)]
  exact Measurable.ite (hz (measurableSet_singleton (0:ℂ))) (hm 1) ((hR.sub measurable_const).div hz)

theorem norm_velocityTransform {r : ℝ} (hr : r<1) (μ : Measure Circle) [IsProbabilityMeasure μ]
    {z : ℂ} (hz : ‖z‖≤r) : ‖velocityTransform μ z‖ ≤ 1/(1-r) := by
  unfold velocityTransform
  have hv : ∀ᵐ ξ : Circle ∂μ, ‖(ξ:ℂ)/(1-(ξ:ℂ)*z)‖≤1/(1-r) := by
    filter_upwards with ξ
    have h := norm_sub_norm_le (1:ℂ) ((ξ:ℂ)*z)
    simp [norm_mul] at h
    rw [norm_div,Circle.norm_coe]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)

  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hv

theorem flowVelocity_eq_transform (μ : Measure Circle) [IsProbabilityMeasure μ]
    {a z : ℂ} (ha : a≠0) (hn : z≠0) (hz : ‖z‖<1) :
    (∫ ξ : Circle, flowVelocity a (a/z) ξ ∂μ)=velocityTransform μ z/a := by
  rw [velocityTransform,←integral_div]
  apply integral_congr_ae
  filter_upwards with ξ
  dsimp [flowVelocity]
  rw [show a/z-a*ξ=(a/z)*(1-(ξ:ℂ)*z) by field_simp]
  have hD := den_ne hz ξ
  generalize he : 1-(ξ:ℂ)*z=e at hD ⊢
  field_simp [ha,hn,hD]
  <;> rw [←he] <;> ring

end Springer
