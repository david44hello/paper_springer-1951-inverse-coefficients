import Springer.SchwarzRepresentation
import Springer.HerglotzCoefficients
noncomputable section
open Set Metric MeasureTheory Complex Real Filter
open scoped Topology ENNReal
namespace Springer

private def angleLaw : Measure ℝ :=
  ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioc 0 (2*Real.pi))

private instance : IsProbabilityMeasure angleLaw := by
  constructor
  rw [angleLaw,Measure.smul_apply,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,smul_eq_mul,
    ←ENNReal.ofReal_mul (by positivity),inv_mul_cancel₀ (by positivity),ENNReal.ofReal_one]

private def uniformCircle : Measure Circle := angleLaw.map Circle.exp

private instance : IsProbabilityMeasure uniformCircle :=
  (Measure.isProbabilityMeasure_map_iff Circle.exp.continuous.measurable.aemeasurable).mpr inferInstance

private theorem uniform_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℂ → E) (hc : Continuous (fun ξ : Circle => f ξ)) :
    (∫ ξ : Circle, f (ξ:ℂ) ∂uniformCircle)=Real.circleAverage f 0 1 := by
  rw [uniformCircle,integral_map Circle.exp.continuous.measurable.aemeasurable hc.aestronglyMeasurable,
    angleLaw,integral_smul_measure,Real.circleAverage,intervalIntegral.integral_of_le (by positivity)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp [circleMap,Circle.coe_exp]

private def radialLaw (f : ℂ → ℂ) : Measure Circle :=
  (uniformCircle.withDensity (fun ξ => ENNReal.ofReal (f ξ).re)).map (fun ξ => ξ⁻¹)

private theorem continuous_boundary {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f disc) :
    Continuous (fun ξ : Circle => f ξ) := by
  apply hf.continuousOn.comp_continuous (by fun_prop)
  intro ξ
  simp [disc,closure_ball]

private theorem radial_probability {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f disc) (h0 : f 0=1)
    (hpos : ∀ ξ : Circle, 0≤(f ξ).re) : IsProbabilityMeasure (radialLaw f) := by
  have hc := continuous_boundary hf
  have hi := hc.integrable_of_hasCompactSupport (μ:=uniformCircle) (HasCompactSupport.of_compactSpace _)
  have mean : (∫ ξ : Circle, f ξ ∂uniformCircle)=1 := by
    rw [uniform_integral f hc]
    have hf' : DiffContOnCl ℂ f (ball 0 |(1:ℝ)|) := by simpa [disc] using hf
    exact hf'.circleAverage.trans h0
  have norm : (∫ ξ : Circle, (f ξ).re ∂uniformCircle)=1 := by
    change (∫ ξ : Circle, RCLike.re (f ξ) ∂uniformCircle)=1
    rw [integral_re hi,mean]; rfl
  apply (Measure.isProbabilityMeasure_map_iff (by fun_prop : AEMeasurable (fun ξ : Circle => ξ⁻¹) _)).mpr
  constructor
  have hin : Integrable (fun ξ : Circle => (f ξ).re) uniformCircle :=
    (continuous_re.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,←ofReal_integral_eq_lintegral_ofReal
    hin
    (ae_of_all _ hpos),norm,ENNReal.ofReal_one]

theorem circle_kernel_continuous {z : ℂ} (hz : z∈disc) :
    Continuous (fun ξ : Circle => (1+(ξ:ℂ)*z)/(1-(ξ:ℂ)*z)) := by
  have h (ξ : Circle) : 1-(ξ:ℂ)*z≠0 := by
    have hn : ‖(ξ:ℂ)*z‖<1 := by simpa [disc,norm_mul] using hz
    intro eq; rw [←sub_eq_zero.mp eq,norm_one] at hn; exact lt_irrefl _ hn
  fun_prop (disch := exact h)

theorem herglotz_closed_disk {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f disc) (h0 : f 0=1)
    (hpos : ∀ ξ : Circle, 0≤(f ξ).re) :
    ∃ μ : ProbabilityMeasure Circle, EqOn f (herglotzTransform (μ : Measure Circle)) disc := by
  refine ⟨⟨radialLaw f,radial_probability hf h0 hpos⟩,?_⟩
  intro z hz
  have hc := continuous_boundary hf
  have hme : Measurable (fun ξ : Circle => ENNReal.ofReal (f ξ).re) :=
    (ENNReal.continuous_ofReal.comp (continuous_re.comp hc)).measurable
  change f z=∫ ξ : Circle, (1+(ξ:ℂ)*z)/(1-(ξ:ℂ)*z) ∂radialLaw f
  rw [radialLaw,integral_map (by fun_prop : AEMeasurable (fun ξ : Circle => ξ⁻¹) _)
    (circle_kernel_continuous hz).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hme (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) _]
  have e (ξ : Circle) : (ENNReal.ofReal (f ξ).re).toReal • ((1+((ξ⁻¹:Circle):ℂ)*z)/(1-((ξ⁻¹:Circle):ℂ)*z)) =
      herglotzRieszKernel 0 z (ξ:ℂ) • ((f ξ).re:ℂ) := by
    rw [ENNReal.toReal_ofReal (hpos ξ),herglotzRieszKernel_def,Circle.coe_inv]
    simp only [sub_zero,smul_eq_mul,Complex.real_smul]
    have hn : (ξ:ℂ)≠0 := Circle.coe_ne_zero _
    have hd : (ξ:ℂ)-z≠0 := by
      intro h; have he := sub_eq_zero.mp h
      have hz' : ‖z‖<1 := by simpa [disc] using hz
      rw [←he,Circle.norm_coe] at hz'; exact lt_irrefl _ hz'
    have he : 1-(ξ:ℂ)⁻¹*z≠0 := by
      intro h
      have hh := sub_eq_zero.mp h
      field_simp [hn] at hh
      exact hd (by linear_combination hh)
    field_simp [he,hn,hd] <;> ring
  simp_rw [e]
  rw [uniform_integral (fun ζ : ℂ => herglotzRieszKernel 0 z ζ • ((f ζ).re:ℂ))]
  · exact (schwarz_average hf h0 hz).symm
  · have hns : z∉sphere (0:ℂ) |(1:ℝ)| := by rw [abs_one]; exact sphere_disjoint_ball.notMem_of_mem_right hz
    have hk := (continuousOn_herglotzRieszKernel_sphere hns).comp_continuous
      (by fun_prop : Continuous (fun ξ : Circle => (ξ:ℂ))) (by intro ξ; simp)
    exact hk.smul (continuous_ofReal.comp (continuous_re.comp hc))

end Springer
