import Springer.FlowGeometry

noncomputable section
open Complex MeasureTheory Metric Set Filter
open scoped Topology Real NNReal
namespace Springer

/-- Extend the velocity outside its physical time interval using a continuous
projection onto that interval. Its values on the interval are the actual ones. -/
def clipTime (s t : ℝ) := max s (min t 1)

theorem clipTime_mem {s : ℝ} (hs : s≤1) (t : ℝ) : clipTime s t∈Icc s 1 :=
  ⟨le_max_left _ _,max_le hs (min_le_right _ _)⟩

theorem clipTime_eq {s t : ℝ} (ht : t∈Icc s 1) : clipTime s t=t := by
  simp [clipTime,min_eq_left ht.2,max_eq_right ht.1]

def contourField (g : ℂ → ℂ) (φ : ℝ → ℂ → ℂ) (μ : ℝ → Measure Circle) (s t : ℝ) (y : ℂ) :=
  let v := clipTime s t;
  -velocityTransform (μ v) (φ (elapsed v) (inverseCoordinate g y))/(Real.sqrt v:ℂ)

theorem CommonDisk.field_measurable {g ψ : ℂ → ℂ} {ρ r : ℝ} {p φ : ℝ → ℂ → ℂ}
    (D : CommonDisk g ρ r) (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ) (hr1 : ρ<1)
    (μ : ℝ → Measure Circle) [∀ t, IsProbabilityMeasure (μ t)]
    (hm : ∀ f : C(Circle,ℂ), Measurable (fun t => ∫ ξ, f ξ ∂μ t)) :
    Measurable (fun q : ℝ × ℝ => contourField g φ μ (ρ^2) q.2 (circleMap 0 r q.1)) := by
  let v := clipTime (ρ^2)
  let z := fun θ : ℝ => inverseCoordinate g (circleMap 0 r θ)
  have hs : ρ^2≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (by linarith : 0≤1+ρ)]
  have ht (t : ℝ) : v t∈Icc (ρ^2) 1 := clipTime_mem hs t
  have hl (t : ℝ) := elapsed_mem hr (ht t)
  have hz (θ : ℝ) : z θ∈disc := by
    simpa [z,disc] using (D.small _ (circleMap_mem_closedBall _ D.positive.le θ)).trans (by linarith : ρ/4<1)
  have hvC : Continuous v := by change Continuous (fun t : ℝ => max (ρ^2) (min t 1)); fun_prop
  have hlC : Continuous (fun t => elapsed (v t)) := continuous_iff_continuousAt.mpr fun t =>
    (elapsed_deriv ((sq_pos_of_pos hr).trans_le (ht t).1)).continuousAt.comp hvC.continuousAt
  have hzC : Continuous z := D.coordinate.continuousOn.comp_continuous (continuous_circleMap _ _)
    (circleMap_mem_closedBall _ D.positive.le)
  let F := fun θ t : ℝ => φ (elapsed (v t)) (z θ)
  have hF : Measurable (Function.uncurry F) := by
    apply measurable_uncurry_of_continuous_of_measurable
    · intro t
      exact (h.analytic _ (hl t)).continuousOn.comp_continuous hzC hz
    · intro θ
      have hL : 0≤Real.log (1/ρ) := Real.log_nonneg ((one_le_div hr).mpr hr1.le)
      have hc := (h.path_ac _ (hz θ)).continuousOn
      rw [uIcc_of_le hL] at hc
      exact (hc.comp_continuous hlC hl).measurable
  have mφ (q : ℝ × ℝ) : Function.uncurry F q∈disc := h.maps _ (hl _) (hz _)
  let M := fun q : ℝ × ℝ => μ (v q.2)
  have moments (k : ℕ) : Measurable (fun q => circleMoment (M q) k) := by
    let χ : C(Circle,ℂ) := ⟨fun ξ => (ξ:ℂ)^k,by fun_prop⟩
    exact (hm χ).comp (hvC.measurable.comp measurable_snd)
  letI : ∀ q, IsProbabilityMeasure (M q) := fun q => inferInstanceAs (IsProbabilityMeasure (μ (v q.2)))
  exact (measurable_velocityTransform M moments hF mφ).neg.div
    (Complex.continuous_ofReal.measurable.comp (Real.continuous_sqrt.measurable.comp (hvC.measurable.comp measurable_snd)))

theorem CommonDisk.field_bound {g ψ : ℂ → ℂ} {ρ r : ℝ} {p φ : ℝ → ℂ → ℂ}
    (D : CommonDisk g ρ r) (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ) (hr1 : ρ<1)
    (μ : ℝ → Measure Circle) [∀ t, IsProbabilityMeasure (μ t)] (t : ℝ) {y : ℂ}
    (hy : y∈closedBall 0 r) : ‖contourField g φ μ (ρ^2) t y‖ ≤ 2/ρ := by
  let v := clipTime (ρ^2) t
  have hs : ρ^2≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (by linarith : 0≤1+ρ)]
  have hv := clipTime_mem hs t
  have hz : inverseCoordinate g y∈disc := by simpa [disc] using (D.small y hy).trans (by linarith : ρ/4<1)
  have hl := elapsed_mem hr hv
  have hφ := (h.radial_bounds hr hl hz (D.small y hy).le).2
  have hhalf : ‖φ (elapsed v) (inverseCoordinate g y)‖≤1/2 := by linarith [D.small y hy]
  have hV := norm_velocityTransform (by norm_num : (1/2:ℝ)<1) (μ v) hhalf
  norm_num at hV
  have hroot : ρ≤Real.sqrt v := by
    have := Real.sqrt_le_sqrt hv.1
    rwa [Real.sqrt_sq hr.le] at this
  change ‖-velocityTransform (μ v) _ / (Real.sqrt v:ℂ)‖ ≤ 2/ρ
  rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg v)]
  exact div_le_div₀ (by norm_num) hV hr hroot

theorem contourWeight_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖contourWeight r n θ‖=‖contourWeight r n 0‖ := by
  simp [contourWeight,deriv_circleMap,norm_div,norm_mul,norm_pow]

theorem weighted_field_integrable {g ψ : ℂ → ℂ} {ρ r : ℝ} {p φ : ℝ → ℂ → ℂ}
    (D : CommonDisk g ρ r) (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ) (hr1 : ρ<1)
    (μ : ℝ → Measure Circle) [∀ t, IsProbabilityMeasure (μ t)]
    (hm : ∀ f : C(Circle,ℂ), Measurable (fun t => ∫ ξ, f ξ ∂μ t)) (n : ℕ) (a b : ℝ) :
    Integrable (fun q : ℝ × ℝ => contourWeight r n q.1*contourField g φ μ (ρ^2) q.2 (circleMap 0 r q.1))
      (angleMeasure.prod (volume.restrict (Ioc a b))) := by
  apply (integrable_const (‖contourWeight r n 0‖*(2/ρ))).mono'
    (((contourWeight_continuous D.positive n).measurable.comp measurable_fst).mul
      (D.field_measurable h hr hr1 μ hm)).aestronglyMeasurable
  filter_upwards with q
  simp only [Pi.mul_apply,Function.comp_apply]
  rw [norm_mul,contourWeight_norm r n q.1]
  exact mul_le_mul_of_nonneg_left (D.field_bound h hr hr1 μ _ (circleMap_mem_closedBall _ D.positive.le _))
    (norm_nonneg _)

end Springer
