import Springer.FlowRegularity

noncomputable section
open Set MeasureTheory Complex Filter
open scoped NNReal Topology
namespace Springer

theorem norm_herglotz_kernel_bound {r : ℝ} (hr : r<1) {z : ℂ} (hz : ‖z‖≤r) (ξ : Circle) :
    ‖flowKernel z ξ‖ ≤ (1+r)/(1-r) := by
  have he : ‖(ξ:ℂ)*z‖=‖z‖ := by simp [norm_mul]
  have h1 : ‖1+(ξ:ℂ)*z‖ ≤ 1+r := (norm_add_le _ _).trans (by simpa [he] using add_le_add_left hz 1)
  have h2 : 1-r ≤ ‖1-(ξ:ℂ)*z‖ := by
    have H := norm_sub_norm_le (1:ℂ) ((ξ:ℂ)*z)
    rw [norm_one,he] at H
    linarith
  rw [flowKernel,norm_div]
  exact div_le_div₀ (by linarith [norm_nonneg z]) h1 (sub_pos.mpr hr) h2

theorem radial_path_ac {ρ : ℝ} (hr : 0<ρ) (hr1 : ρ<1) {φ : ℝ → ℂ}
    (μ : ℝ → Measure Circle) [∀ l, IsProbabilityMeasure (μ l)] {r δ : ℝ} (hr' : r<1) (hδ : 0<δ)
    (hbound : ∀ l∈Icc 0 (Real.log (1/ρ)), δ≤‖φ l‖ ∧ ‖φ l‖≤r)
    (hac : AbsolutelyContinuousOnInterval φ 0 (Real.log (1/ρ)))
    (hd : ∀ᵐ l ∂volume.restrict (Icc 0 (Real.log (1/ρ))),
      HasDerivAt φ (-φ l*(∫ ξ, flowKernel (φ l) ξ ∂μ l)) l) :
    AbsolutelyContinuousOnInterval (fun t => (Real.sqrt t:ℂ)/φ (elapsed t)) (ρ^2) 1 := by
  let L := Real.log (1/ρ)
  have hL : 0≤L := Real.log_nonneg ((one_le_div hr).mpr hr1.le)
  let C : ℝ≥0 := ⟨(1+r)/(1-r),div_nonneg (by linarith [norm_nonneg (φ 0),(hbound 0 ⟨le_rfl,hL⟩).2])
    (sub_nonneg.mpr hr'.le)⟩
  have hvel : ∀ᵐ l ∂volume.restrict (Icc 0 L),
      HasDerivAt φ (-φ l*(∫ ξ, flowKernel (φ l) ξ ∂μ l)) l ∧
        ‖-φ l*(∫ ξ, flowKernel (φ l) ξ ∂μ l)‖ ≤ C := by
    filter_upwards [hd,ae_restrict_mem measurableSet_Icc] with l hl hI
    refine ⟨hl, ?_⟩
    have hφ := (hbound _ hI).2
    have hK : ‖∫ ξ, flowKernel (φ l) ξ ∂μ l‖ ≤ C := by
      change _ ≤ (1+r)/(1-r)
      simpa only [probReal_univ,mul_one] using
        norm_integral_le_of_norm_le_const (μ:=μ l) (Filter.Eventually.of_forall (norm_herglotz_kernel_bound hr' hφ))
    rw [norm_mul,norm_neg]
    exact (mul_le_mul_of_nonneg_right (hφ.trans hr'.le) (norm_nonneg _)).trans (by simpa using hK)
  have hf := lipschitz_of_ac_velocity hL C hac hvel
  obtain ⟨K,hK⟩ := elapsed_lipschitz (sq_pos_of_pos hr)
  have hmap : MapsTo elapsed (Icc (ρ^2) 1) (Icc 0 L) := fun _ ht => elapsed_mem hr ht
  have hφ := hf.comp hK hmap
  obtain ⟨J,hJ⟩ := inv_lipschitz_away hδ
  have hm : MapsTo (φ ∘ elapsed) (Icc (ρ^2) 1) {z | δ≤‖z‖} := fun x hx => (hbound _ (hmap hx)).1
  have hR : ρ^2≤1 := by nlinarith [sq_nonneg (1-ρ),mul_nonneg (sub_nonneg.mpr hr1.le) (by linarith : 0≤1+ρ)]
  have invAC : AbsolutelyContinuousOnInterval (fun t => (φ (elapsed t))⁻¹) (ρ^2) 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K:=J*(C*K))
    rw [uIcc_of_le hR]
    exact hJ.comp hφ hm
  have hs : ContDiffOn ℝ 1 Real.sqrt (uIcc (ρ^2) 1) := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    exact (Real.contDiffAt_sqrt ((sq_pos_of_pos hr).trans_le hx.1).ne').contDiffWithinAt
  have hs' := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hs.absolutelyContinuousOnInterval
  simpa only [div_eq_mul_inv,Pi.smul_def,smul_eq_mul,Pi.mul_def,Function.comp_def,Complex.ofRealCLM_apply] using hs'.smul invAC

end Springer
