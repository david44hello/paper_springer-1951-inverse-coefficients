import Springer.CauchyFlow
import Springer.VelocityCoefficients
import Springer.FunctionalEvolution

noncomputable section
open Complex MeasureTheory Set Metric Filter
open scoped Topology Real
namespace Springer

theorem contourWeight_continuous {r : ℝ} (hr : 0<r) (n : ℕ) : Continuous (contourWeight r n) := by
  have hn (θ : ℝ) : circleMap 0 r θ≠0 := by
    intro he
    have H := Metric.mem_sphere.mp (circleMap_mem_sphere 0 hr.le θ)
    simp [he] at H
    linarith
  unfold contourWeight
  simp only [deriv_circleMap]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact fun θ => pow_ne_zero _ (hn θ)

theorem reciprocalVelocity_analytic {R : ℂ → ℂ} {a y : ℂ} {ξ : Circle}
    (hR : AnalyticAt ℂ R y) (hd : 1+y*(R y-a*ξ)≠0) :
    AnalyticAt ℂ (reciprocalVelocity R a ξ) y :=
  analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.mul
    ((analyticAt_const.add (analyticAt_id.mul (hR.sub analyticAt_const))).inv hd)))

/-- On a fixed circle in the shared disk, taking the Cauchy coefficient of the
velocity commutes with the circle probability integral. -/
theorem velocity_contour_swap (μ : Measure Circle) [IsProbabilityMeasure μ] {a : ℂ}
    {R : ℂ → ℂ} {r : ℝ} (hr : 0<r) (hR : AnalyticOnNhd ℂ R (closedBall 0 r))
    (hd : ∀ z∈closedBall 0 r, ∀ ξ : Circle, 1+z*(R z-a*ξ)≠0) (n : ℕ) :
    (∫ θ, contourWeight r n θ*(∫ ξ : Circle, reciprocalVelocity R a ξ (circleMap 0 r θ) ∂μ) ∂angleMeasure) =
      ∫ ξ : Circle, taylorCoeff (reciprocalVelocity R a ξ) n ∂μ := by
  let f := fun (p : ℝ × Circle) => contourWeight r n p.1 * reciprocalVelocity R a p.2 (circleMap 0 r p.1)
  have hR' : Continuous (fun θ : ℝ => R (circleMap 0 r θ)) :=
    hR.continuousOn.comp_continuous (continuous_circleMap _ _) (circleMap_mem_closedBall 0 hr.le)
  have hd' (q : ℝ × Circle) : 1+circleMap 0 r q.1*(R (circleMap 0 r q.1)-a*q.2)≠0 :=
    hd _ (circleMap_mem_closedBall _ hr.le _) _
  have hc : Continuous f := by
    have hR'' : Continuous (fun q : ℝ × Circle => R (circleMap 0 r q.1)) := hR'.comp continuous_fst
    have hW : Continuous (fun q : ℝ × Circle => contourWeight r n q.1) := (contourWeight_continuous hr n).comp continuous_fst
    have hξ : Continuous (fun q : ℝ × Circle => (q.2:ℂ)) := by fun_prop
    have hcircle : Continuous (fun q : ℝ × Circle => circleMap 0 r q.1) := by fun_prop
    have hden : Continuous (fun q : ℝ × Circle =>
        1+circleMap 0 r q.1*(R (circleMap 0 r q.1)-a*q.2)) :=
      continuous_const.add (hcircle.mul (hR''.sub (continuous_const.mul hξ)))
    exact hW.mul ((hξ.neg.div_const a).sub ((hξ.pow 2).mul (hcircle.mul (hden.inv₀ hd'))))
  have hi : Integrable f (angleMeasure.prod μ) := by
    unfold angleMeasure
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_univ)
  calc
    _ = ∫ θ, (∫ ξ : Circle, f (θ,ξ) ∂μ) ∂angleMeasure := by
      apply integral_congr_ae; filter_upwards with θ
      exact (integral_const_mul _ _).symm
    _ = ∫ ξ : Circle, (∫ θ, f (θ,ξ) ∂angleMeasure) ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae; filter_upwards with ξ
      apply Eq.symm
      apply taylorCoeff_contour hr
      apply DifferentiableOn.diffContOnCl_ball (U:=closedBall (0:ℂ) r) _ Subset.rfl
      intro y hy
      exact (reciprocalVelocity_analytic (hR y hy) (hd y hy ξ)).differentiableAt.differentiableWithinAt

theorem velocity_contour_zero (μ : Measure Circle) [IsProbabilityMeasure μ] {a : ℂ}
    {R : ℂ → ℂ} {r : ℝ} (hr : 0<r) (hR : AnalyticOnNhd ℂ R (closedBall 0 r))
    (hd : ∀ z∈closedBall 0 r, ∀ ξ : Circle, 1+z*(R z-a*ξ)≠0) :
    (∫ θ, contourWeight r 0 θ*(∫ ξ : Circle, reciprocalVelocity R a ξ (circleMap 0 r θ) ∂μ) ∂angleMeasure) =
      -(∫ ξ : Circle, (ξ:ℂ) ∂μ)/a := by
  rw [velocity_contour_swap μ hr hR hd]
  simp [reciprocalVelocity,integral_div,integral_neg]

theorem velocity_contour_succ (μ : Measure Circle) [IsProbabilityMeasure μ] {a : ℂ}
    {R : ℂ → ℂ} {r : ℝ} (hr : 0<r) (hR : AnalyticOnNhd ℂ R (closedBall 0 r))
    (hd : ∀ z∈closedBall 0 r, ∀ ξ : Circle, 1+z*(R z-a*ξ)≠0) (n : ℕ) :
    (∫ θ, contourWeight r (n+1) θ*(∫ ξ : Circle, reciprocalVelocity R a ξ (circleMap 0 r θ) ∂μ) ∂angleMeasure) =
      -(averagedDirection (storedRemainder R) (fun ξ => a*ξ-R 0) μ).coeff n := by
  rw [velocity_contour_swap μ hr hR hd]
  simp only [reciprocalVelocity_coeff (hR 0 (mem_closedBall_self hr.le)),averagedDirection,
    PowerSeries.coeff_mk,neg_mul,integral_neg]

end Springer
