import Springer.FlowContourLaw
import Springer.OddConclusions

noncomputable section
open Complex MeasureTheory Set Metric Filter
open scoped Real NNReal Topology
namespace Springer

/-- The actual Laurent coefficient paths and the weakly measurable law. The initial
center, initial time and terminal inverse are retained for the sharpened bound. -/
theorem actual_coefficient_flow {g : ℂ → ℂ} (hg : Sigma g) {ρ : ℝ} (hr : 0<ρ) (hr1 : ρ<1)
    {w : ℂ} (hom : ∀ z∈exterior, ρ<‖g z-w‖) {p φ : ℝ → ℂ → ℂ}
    (h : NormalizedLoewnerData (flowDiskMap g w ρ) ρ p φ) :
    ∃ μ : ℝ → Measure Circle,
      let R := timeRemainder g φ
      CoefficientFlow g (ρ^2) (fun t => storedRemainder (R t)) (fun t => R t 0) μ ∧
      R (ρ^2) 0 = -w ∧
      (∀ f : C(Circle,ℂ), Measurable (fun t => ∫ ξ, f ξ ∂μ t)) := by
  obtain ⟨r,D⟩ := exists_commonDisk hg hr
  obtain ⟨μ,prob,weak,path⟩ := h.path_laws hr hr1
  letI : ∀ t, IsProbabilityMeasure (μ t) := prob
  let s := ρ^2
  let R := timeRemainder g φ
  let A := fun (n : ℕ) (t : ℝ) => taylorCoeff (R t) n
  let B := contourSlope g φ μ s r
  have hs : s≤1 := by dsimp [s]; nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (by linarith : 0≤1+ρ)]
  have inc (n : ℕ) (t : ℝ) (ht : t∈Icc s 1) :
      A n t - A n s=∫ x : ℝ in s..t, B n x := D.contour_increment h hr hr1 μ weak path ht n
  have hi (n : ℕ) (x : ℝ) (hx : x∈Icc s 1) : IntervalIntegrable (B n) volume s x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1]
    exact (weighted_field_integrable D h hr hr1 μ weak n s x).integral_prod_right
  have hac (n : ℕ) : AbsolutelyContinuousOnInterval (A n) s 1 := by
    let C := ‖contourWeight r n 0‖*(2/ρ)
    apply coefficient_ac_of_increment hs (C:=Real.toNNReal (C*angleMeasure.real univ)) _ _
      _ (hi n) (inc n)
    intro t ht
    have hle : ∀ᵐ θ ∂angleMeasure, ‖contourWeight r n θ*contourField g φ μ s t (circleMap 0 r θ)‖≤C := by
      filter_upwards with θ
      rw [norm_mul,contourWeight_norm r n θ]
      exact mul_le_mul_of_nonneg_left (D.field_bound h hr hr1 μ _ (circleMap_mem_closedBall _ D.positive.le _)) (norm_nonneg _)
    exact (norm_integral_le_of_norm_le_const hle).trans (Real.le_coe_toNNReal _)
  have hAE := simultaneous_coefficient_deriv hs A B (fun n => hi n 1 ⟨hs,le_rfl⟩) inc
  have hreplace (n : ℕ) (t : ℝ) (ht : t∈Icc s 1) :
      B n t=∫ θ, contourWeight r n θ*(∫ ξ : Circle,
        reciprocalVelocity (R t) (Real.sqrt t) ξ (circleMap 0 r θ) ∂μ t) ∂angleMeasure := by
    apply integral_congr_ae
    filter_upwards with θ
    have hn : circleMap 0 r θ≠0 := by
      intro he
      have hh := Metric.mem_sphere.mp (circleMap_mem_sphere 0 D.positive.le θ)
      simp [he] at hh
      linarith [D.positive]
    rw [D.field_eq_integral h hr hr1 μ ht (circleMap_mem_closedBall _ D.positive.le _) hn]
  have hsI : s∈Icc s 1 := ⟨le_rfl,hs⟩
  have htI : (1:ℝ)∈Icc s 1 := ⟨hs,le_rfl⟩
  have hds := (h.at_origin _ (elapsed_mem hr hsI)).deriv
  have hde := (h.at_origin _ (elapsed_mem hr htI)).deriv
  have hds' : deriv (φ (Real.log (1/ρ))) 0=(ρ:ℂ) := by
    simpa only [s,elapsed_start hr,one_div,Real.log_inv,neg_neg,Real.exp_log hr] using hds
  have hde' : deriv (φ 0) 0=1 := by simpa using hde
  have h₀ := initial_flow_coefficients hg hr h.terminal hds' hom
  have h₁ := terminal_flow_coefficients hg h.initial hde'
  have hRs : R s=flowRemainder g (φ (Real.log (1/ρ))) ρ := by
    simp only [R,s,timeRemainder,Real.sqrt_sq hr.le,elapsed_start hr]
  have hR1 : R 1=flowRemainder g (φ 0) 1 := by simp [R,timeRemainder]
  refine ⟨μ, ?_⟩
  change CoefficientFlow g s (fun t => storedRemainder (R t)) (fun t => R t 0) μ ∧
    R s 0 = -w ∧ _
  refine ⟨?_,by rw [hRs]; exact h₀.1,weak⟩
  refine ⟨prob,by rw [hRs]; exact h₀.2,?_,by rw [hR1]; exact h₁.1,?_,?_,?_⟩
  · intro k; rw [hR1]; exact h₁.2 k
  · intro j; simpa only [A,storedRemainder,PowerSeries.coeff_mk,Pi.neg_def] using (hac (j+1)).neg
  · simpa only [A,taylorCoeff_zero] using hac 0
  · filter_upwards [hAE,ae_restrict_mem measurableSet_Icc] with t hd ht
    have han := D.slice_analytic h hr ht
    have hden (y : ℂ) (hy : y∈closedBall 0 r) := normalized_contour_denominator D h hr hr1 ht hy
    constructor
    · have hb := (hreplace 0 t ht).trans (velocity_contour_zero (μ t) D.positive han hden)
      simpa only [A,taylorCoeff_zero,hb] using hd 0
    · intro j
      have hb := (hreplace (j+1) t ht).trans (velocity_contour_succ (μ t) D.positive han hden j)
      simpa only [A,storedRemainder,PowerSeries.coeff_mk,hb,neg_neg,Pi.neg_def] using (hd (j+1)).neg

theorem disk_theorem_of_loewner (hL : NormalizedLoewnerRepresentation)
    {g : ℂ → ℂ} (hg : Sigma g) (m : ℕ) :
    DiskBound g m ∧ ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ) -
      diskWeight m*(1-‖forwardCoeff g 1‖^(m+1)) := by
  apply disk_theorem_of_coefficient_flow _ hg
  intro f hf ho
  obtain ⟨w,ρ,hr,hr1,hom⟩ := ho
  obtain ⟨p,φ,hφ⟩ := normalizedLoewner_of_omitted_disk hL hf w hr hr1 hom
  obtain ⟨μ,hF,_⟩ := actual_coefficient_flow hf hr hr1 hom hφ
  refine ⟨ρ^2,_,_,μ,sq_pos_of_pos hr,?_,hF⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (by linarith : 0≤1+ρ)]

end Springer
