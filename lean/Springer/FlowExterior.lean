import Springer.ActualCoefficientFlow

noncomputable section
open Set Filter Function Complex Metric Finset MeasureTheory
open scoped Topology NNReal
namespace Springer

private theorem taylorCoeff_hasSum_on {r : ℝ} (hr : 0<r) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) {y : ℂ} (hy : ‖y‖<r) :
    HasSum (fun j : ℕ => taylorCoeff f j*y^j) (f y) := by
  let R : ℝ≥0 := ⟨r,hr.le⟩
  have h := hf.differentiableOn.hasFPowerSeriesOnBall (R:=R) (show 0<R from hr)
  have ha := hf 0 (mem_closedBall_self hr.le)
  have e := h.hasFPowerSeriesAt.eq_formalMultilinearSeries ha.hasFPowerSeriesAt
  have hyR : y∈eball (0:ℂ) (R:ENNReal) := by
    rw [mem_eball_zero_iff,enorm_lt_coe]
    exact hy
  have hs := h.hasSum hyR
  rw [e] at hs
  simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,FormalMultilinearSeries.coeff_ofScalars,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,zero_add,mul_comm,taylorCoeff] using hs

/-- The exterior function and its Laurent coefficients use the same analytic germ
as the time-dependent coefficient equations. -/
def exteriorTrajectory (g : ℂ → ℂ) (φ : ℝ → ℂ → ℂ) (t : ℝ) (w : ℂ) :=
  w+timeRemainder g φ t w⁻¹

theorem actual_exterior_family {g : ℂ → ℂ} (hg : Sigma g) {w₀ : ℂ} {ρ : ℝ}
    (hr : 0<ρ) (hr1 : ρ<1) (hom : ∀ z∈exterior, ρ<‖g z-w₀‖) {p φ : ℝ → ℂ → ℂ}
    (h : NormalizedLoewnerData (flowDiskMap g w₀ ρ) ρ p φ) :
    ∃ K : ℝ, 0<K ∧
    (∀ t∈Icc (ρ^2) 1, AnalyticOnNhd ℂ (exteriorTrajectory g φ t) {w | K<‖w‖}) ∧
    (∀ t∈Icc (ρ^2) 1, ∀ w : ℂ, K<‖w‖ →
      exteriorTrajectory g φ t w = (Real.sqrt t:ℂ)/φ (elapsed t) (invFunOn g exterior w)⁻¹ ∧
      HasSum (fun k : ℕ => (storedRemainder (timeRemainder g φ t)).coeff k*(w⁻¹)^(k+1))
        (w+timeRemainder g φ t 0-exteriorTrajectory g φ t w)) ∧
    (∀ w : ℂ, K<‖w‖ → exteriorTrajectory g φ (ρ^2) w=w-w₀ ∧
      exteriorTrajectory g φ 1 w=invFunOn g exterior w) := by
  obtain ⟨r,D⟩ := exists_commonDisk hg hr
  obtain ⟨S,hS,hG⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp (inverse_germ hg).2.2.2)
  let c := min r S
  have hc : 0<c := lt_min D.positive hS
  have good (w : ℂ) (hw : c⁻¹<‖w‖) :
      w≠0 ∧ ‖w⁻¹‖<r ∧ g (invFunOn g exterior w)=w := by
    have hn := norm_pos_iff.mp ((inv_pos.mpr hc).trans hw)
    have hsmall : ‖w⁻¹‖<c := by
      rw [norm_inv]; exact (inv_lt_comm₀ (norm_pos_iff.mpr hn) hc).mpr hw
    have hu : w⁻¹∈ball (0:ℂ) S := by simpa using hsmall.trans_le (min_le_right r S)
    exact ⟨hn,hsmall.trans_le (min_le_left r S),by simpa only [inv_inv] using (hG hu (inv_ne_zero hn)).2⟩
  have hs : ρ^2≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (by linarith : 0≤1+ρ)]
  have rhs (t : ℝ) (ht : t∈Icc (ρ^2) 1) (w : ℂ) (hw : c⁻¹<‖w‖) :
      exteriorTrajectory g φ t w = (Real.sqrt t:ℂ)/φ (elapsed t) (invFunOn g exterior w)⁻¹ := by
    obtain ⟨hn,hy,_⟩ := good w hw
    have hy' : w⁻¹∈closedBall (0:ℂ) r := by simpa using hy.le
    rw [exteriorTrajectory,actual_timeRemainder D h hr ht hy' (inv_ne_zero hn),
      inverseCoordinate_actual (inv_ne_zero hn),inv_inv]
    ring
  refine ⟨c⁻¹,inv_pos.mpr hc,?_,?_,?_⟩
  · intro t ht w hw
    obtain ⟨hn,hy,_⟩ := good w hw
    have ha := D.slice_analytic h hr ht w⁻¹ (by simpa using hy.le)
    exact analyticAt_id.add (ha.comp (f:=fun z : ℂ => z⁻¹) (analyticAt_id.inv hn))
  · intro t ht w hw
    refine ⟨rhs t ht w hw,?_⟩
    have A := D.slice_analytic h hr ht
    have H := taylorCoeff_hasSum_on D.positive A (good w hw).2.1
    have htail := ((hasSum_nat_add_iff' 1).mpr H).neg
    simpa only [storedRemainder,PowerSeries.coeff_mk,neg_mul,exteriorTrajectory,sum_range_one,
      taylorCoeff_zero,pow_zero,mul_one,neg_sub,add_sub_add_left_eq_sub] using htail
  · intro w hw
    obtain ⟨hn,hy,hG⟩ := good w hw
    have he := D.actual w⁻¹ (by simpa using hy.le) (inv_ne_zero hn)
    simp only [inv_inv] at he
    have hi : (invFunOn g exterior w)⁻¹∈disc := by
      rw [disc,mem_ball,dist_zero_right,norm_inv,inv_lt_one₀ (zero_lt_one.trans (show 1<‖invFunOn g exterior w‖ from he))]
      exact he
    rw [rhs _ ⟨le_rfl,hs⟩ w hw,rhs _ ⟨hs,le_rfl⟩ w hw]
    exact flow_endpoints hr he hG hom (h.terminal hi) (h.initial hi)

end Springer
