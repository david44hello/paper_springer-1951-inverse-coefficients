import Springer.LoewnerInput
import Springer.RadialPath
import Springer.FlowMeasurability

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology
namespace Springer

theorem exp_neg_elapsed {t : ℝ} (ht : 0<t) : Real.exp (-elapsed t)=Real.sqrt t := by
  rw [elapsed,neg_div,neg_neg,Real.exp_half,Real.exp_log ht]

private theorem complex_intervalIntegrable_of_ac_deriv {s t : ℝ} (hst : s≤t)
    {f v : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f s t)
    (hd : ∀ᵐ x ∂volume.restrict (Icc s t), HasDerivAt f (v x) x) :
    IntervalIntegrable v volume s t := by
  have hp (L : ℂ →L[ℝ] ℝ) : IntervalIntegrable (fun x => L (v x)) volume s t := by
    have hac := L.lipschitzWith.comp_absolutelyContinuousOnInterval hf
    apply hac.intervalIntegrable_deriv.congr_ae
    rw [uIoc_of_le hst]
    filter_upwards [hd.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))] with x hx
    exact (L.hasFDerivAt.comp_hasDerivAt x hx).deriv
  rw [intervalIntegrable_iff,←IntegrableOn.re_im_iff]
  exact ⟨intervalIntegrable_iff.mp (hp Complex.reCLM),intervalIntegrable_iff.mp (hp Complex.imCLM)⟩

theorem trajectory_increment {s b : ℝ} (hsb : s≤b) {f v : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f s b)
    (hd : ∀ᵐ x ∂volume.restrict (Icc s b), HasDerivAt f (v x) x) {t : ℝ} (ht : t∈Icc s b) :
    f t-f s=∫ x : ℝ in s..t, v x := by
  have hsub : Icc s t ⊆ Icc s b := Icc_subset_Icc_right ht.2
  have hus : uIcc s t ⊆ uIcc s b := by simpa [uIcc_of_le ht.1,uIcc_of_le hsb] using hsub
  have hd' := hd.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  exact complex_increment_of_ac ht.1 (hf.mono hus) (complex_intervalIntegrable_of_ac_deriv ht.1 (hf.mono hus) hd') hd'

theorem NormalizedLoewnerData.radial_bounds {ψ : ℂ → ℂ} {ρ : ℝ} {p φ : ℝ → ℂ → ℂ}
    (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ) {l : ℝ} (hl : l∈Icc 0 (Real.log (1/ρ)))
    {z : ℂ} (hz : z∈disc) (hsmall : ‖z‖≤ρ/4) :
    (ρ/2)*‖z‖≤‖φ l z‖ ∧ ‖φ l z‖≤‖z‖ := by
  have he1 : Real.exp (-l) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hl.1])
  have heρ : ρ≤Real.exp (-l) := by
    rw [←Real.exp_log hr]
    apply Real.exp_le_exp.mpr
    have ht := hl.2
    change l≤Real.log (1/ρ) at ht
    rw [one_div,Real.log_inv] at ht
    linarith
  have he : ‖(Real.exp (-l):ℂ)‖=Real.exp (-l) := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have maps : MapsTo (φ l) disc (Metric.closedBall 0 1) :=
    (h.maps l hl).mono_right Metric.ball_subset_closedBall
  exact ⟨disk_uniform_lower (h.analytic l hl).differentiableOn (h.maps l hl) (h.fixed_zero l hl)
    (h.at_origin l hl) (he.trans_le he1) (heρ.trans_eq he.symm) hz hsmall,
    Complex.norm_le_norm_of_mapsTo_ball (h.analytic l hl).differentiableOn maps (h.fixed_zero l hl)
      (by simpa [disc] using hz)⟩

/-- Pointwise evolution and the weak law on the entire common reciprocal-coordinate
cutoff. Exceptional times may depend on the disk argument. -/
theorem NormalizedLoewnerData.path_laws {ψ : ℂ → ℂ} {ρ : ℝ} {p φ : ℝ → ℂ → ℂ}
    (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ) (hr1 : ρ<1) :
    ∃ ν : ℝ → Measure Circle, (∀ t, IsProbabilityMeasure (ν t)) ∧
      (∀ f : C(Circle,ℂ), Measurable (fun t => ∫ ξ, f ξ ∂ν t)) ∧
      ∀ z : ℂ, z≠0 → ‖z‖ ≤ ρ/4 →
        AbsolutelyContinuousOnInterval (fun t => (Real.sqrt t:ℂ)/φ (elapsed t) z) (ρ^2) 1 ∧
        (∀ᵐ t ∂volume.restrict (Icc (ρ^2) 1), HasDerivAt (fun x => (Real.sqrt x:ℂ)/φ (elapsed x) z)
          (-velocityTransform (ν t) (φ (elapsed t) z)/(Real.sqrt t:ℂ)) t) := by
  let J := Icc (0:ℝ) (Real.log (1/ρ))
  obtain ⟨μ,N,hN,hnull,hprob,_,hrep,hweak⟩ :=
    herglotz_measurable_probabilities (volume.restrict J) h.p_meas h.p_good
  letI : ∀ l, IsProbabilityMeasure (μ l) := hprob
  refine ⟨fun t => μ (elapsed t),fun _ => inferInstance,fun f => (hweak f).comp (by unfold elapsed; fun_prop),?_⟩
  intro z hn hsmall
  have hz : z∈disc := by simpa [disc] using (show ‖z‖<1 by linarith)
  have hz0 := norm_pos_iff.mpr hn
  let δ := (ρ/2)*‖z‖
  have hδ : 0<δ := mul_pos (by linarith) hz0
  have hbound (l : ℝ) (hl : l∈J) : δ≤‖φ l z‖ ∧ ‖φ l z‖≤‖z‖ := h.radial_bounds hr hl hz hsmall
  have hout : ∀ᵐ l ∂volume.restrict J, l∉N := by simpa [ae_iff] using hnull
  have hd : ∀ᵐ l ∂volume.restrict J, HasDerivAt (fun s => φ s z)
        (-φ l z*(∫ ξ, flowKernel (φ l z) ξ ∂μ l)) l := by
    filter_upwards [h.path_deriv z hz,hout,ae_restrict_mem measurableSet_Icc] with l hd hN' hl
    rw [hrep l hN' (h.maps l hl hz)] at hd
    exact hd
  refine ⟨radial_path_ac (φ:=fun l => φ l z) (r:=‖z‖) hr hr1 μ (by simpa [disc] using hz) hδ hbound (h.path_ac z hz) hd,?_⟩
  filter_upwards [elapsed_ae hr hd,ae_restrict_mem measurableSet_Icc] with t ht hti
  have htp : 0<t := (sq_pos_of_pos hr).trans_le hti.1
  have hl := elapsed_mem hr hti
  have hφn := norm_pos_iff.mp (hδ.trans_le (hbound _ hl).1)
  have hφd : ‖φ (elapsed t) z‖<1 := (hbound _ hl).2.trans_lt (by simpa [disc] using hz)
  have ht' := flow_timeChange (φ:=fun l => φ l z) htp (μ (elapsed t)) hφn hφd ht
  have hn' : (Real.sqrt t:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr htp).ne'
  simpa only [flowVelocity_eq_transform _ hn' hφn hφd,neg_div] using ht'

end Springer
