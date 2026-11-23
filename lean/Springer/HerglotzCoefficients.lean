import Springer.HerglotzMeasurable
import Springer.Coefficients
noncomputable section
open Set Filter MeasureTheory Finset
open scoped Topology
namespace Springer

def circleResolvent (μ : Measure Circle) (z : ℂ) := ∫ ξ, (1-(ξ:ℂ)*z)⁻¹ ∂μ

def herglotzTransform (μ : Measure Circle) (z : ℂ) := ∫ ξ, (1+(ξ:ℂ)*z)/(1-(ξ:ℂ)*z) ∂μ

private theorem resolvent_nonzero {z : ℂ} (hz : z∈disc) (ξ : Circle) : 1-(ξ:ℂ)*z≠0 := by
  have h : ‖(ξ:ℂ)*z‖ < 1 := by simpa [norm_mul,disc] using hz
  intro he
  rw [←sub_eq_zero.mp he,norm_one] at h
  exact (lt_irrefl _ h)

theorem resolvent_hasSum (μ : Measure Circle) [IsProbabilityMeasure μ] {z : ℂ} (hz : z∈disc) :
    HasSum (fun k => z^k*circleMoment μ k) (circleResolvent μ z) := by
  have hn : ‖z‖<1 := by simpa [disc] using hz
  let F := fun (k : ℕ) (ξ : Circle) => ((ξ:ℂ)*z)^k
  have hi (k : ℕ) : Integrable (F k) μ :=
    Continuous.integrable_of_hasCompactSupport (by dsimp [F]; fun_prop) (HasCompactSupport.of_compactSpace _)
  have hnorm (k : ℕ) : (∫ ξ, ‖F k ξ‖ ∂μ)=‖z‖^k := by simp [F,norm_pow,norm_mul]
  have hsum : Summable (fun k => ∫ ξ, ‖F k ξ‖ ∂μ) := by
    simpa only [hnorm] using summable_geometric_of_lt_one (norm_nonneg _) hn
  have h := hasSum_integral_of_summable_integral_norm hi hsum
  have hval (ξ : Circle) : (∑' k, F k ξ)=(1-(ξ:ℂ)*z)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one (by simpa [norm_mul] using hn : ‖(ξ:ℂ)*z‖<1)).tsum_eq
  have hterm (k : ℕ) : (∫ ξ, F k ξ ∂μ)=z^k*circleMoment μ k := by
    simp only [F,mul_pow,integral_mul_const,integral_const_mul,circleMoment,mul_comm]
  simpa only [hval,hterm,circleResolvent] using h

theorem resolvent_series (μ : Measure Circle) [IsProbabilityMeasure μ] :
    HasFPowerSeriesAt (circleResolvent μ) (FormalMultilinearSeries.ofScalars ℂ (circleMoment μ)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ)<1 by norm_num)] with z hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul,zero_add] using resolvent_hasSum μ hz

theorem herglotz_eq_resolvent (μ : Measure Circle) [IsProbabilityMeasure μ] {z : ℂ} (hz : z∈disc) :
    herglotzTransform μ z=2*circleResolvent μ z-1 := by
  have hfun (ξ : Circle) : (1+(ξ:ℂ)*z)/(1-(ξ:ℂ)*z)=2*(1-(ξ:ℂ)*z)⁻¹-1 := by
    field_simp [resolvent_nonzero hz ξ]; ring
  have hi : Integrable (fun ξ : Circle => 2*(1-(ξ:ℂ)*z)⁻¹) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop (disch := exact resolvent_nonzero hz))
      (HasCompactSupport.of_compactSpace _)
  simp only [herglotzTransform,hfun,integral_sub hi (integrable_const _),integral_const_mul,circleResolvent]
  simp

theorem herglotz_taylor (μ : Measure Circle) [IsProbabilityMeasure μ] (n : ℕ) :
    taylorCoeff (herglotzTransform μ) (n+1)=2*circleMoment μ (n+1) := by
  have hs := resolvent_series μ
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff (n+1))
    (hs.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hs)
  have hcoeff : taylorCoeff (circleResolvent μ) (n+1)=circleMoment μ (n+1) := by
    simpa [taylorCoeff,FormalMultilinearSeries.coeff_ofScalars] using hc
  have he : herglotzTransform μ =ᶠ[𝓝 0] fun z => 2*circleResolvent μ z-1 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ)<1 by norm_num)] with z hz
    exact herglotz_eq_resolvent μ hz
  rw [taylorCoeff_congr he,taylorCoeff_sub (f:=fun z => 2*circleResolvent μ z) (g:=fun _ : ℂ => 1) (analyticAt_const.mul hs.analyticAt) analyticAt_const,
    taylorCoeff_const_mul,hcoeff]
  simp [taylorCoeff,iteratedDeriv_const]

end Springer
