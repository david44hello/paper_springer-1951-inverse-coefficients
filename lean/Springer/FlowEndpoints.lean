import Springer.LaurentFlow
import Springer.VelocityCoefficients

noncomputable section
open Set Filter Function Complex
open scoped Topology
namespace Springer

private theorem inverse_of_exterior_in_disc {z : ℂ} (hz : z∈exterior) : z⁻¹ ∈ disc := by
  rw [disc,Metric.mem_ball,dist_zero_right,norm_inv,inv_lt_one₀ (zero_lt_one.trans hz)]
  exact hz

theorem terminal_laurent_germ {g φ : ℂ → ℂ} (hg : Sigma g) (he : EqOn φ id disc)
    (hd : deriv φ 0=1) : flowLaurentProfile g φ 1 =ᶠ[𝓝 0] inverseProfile g := by
  have h0 : φ 0=0 := he (by simp [disc])
  filter_upwards [eventually_nhdsWithin_iff.mp (inverse_germ hg).2.2.2] with y hy
  by_cases hn : y=0
  · simp [hn,flowLaurentProfile_zero g hd one_ne_zero,inverseProfile]
  have hex := (hy hn).1
  rw [flowLaurentProfile_actual 1 h0 hn hex,he (inverse_of_exterior_in_disc hex)]
  simp [inverseProfile,profile,hn]

theorem initial_laurent_germ {g φ : ℂ → ℂ} (hg : Sigma g) {ρ : ℝ} (hr : 0<ρ) {w : ℂ}
    (he : EqOn φ (flowDiskMap g w ρ) disc) (hd : deriv φ 0=(ρ:ℂ))
    (hom : ∀ v∈exterior, ρ<‖g v-w‖) :
    flowLaurentProfile g φ (ρ:ℂ) =ᶠ[𝓝 0] fun y => 1-w*y := by
  have h0 : φ 0=0 := (he (by simp [disc])).trans (flowDiskMap_zero _ _ _)
  have hb : (ρ:ℂ)≠0 := by exact_mod_cast hr.ne'
  filter_upwards [eventually_nhdsWithin_iff.mp (inverse_germ hg).2.2.2] with y hy
  by_cases hn : y=0
  · simp [hn,flowLaurentProfile_zero g hd hb]
  obtain ⟨hex,hgG⟩ := hy hn
  have hG : invFunOn g exterior y⁻¹≠0 := norm_pos_iff.mp (zero_lt_one.trans hex)
  have hw : y⁻¹-w≠0 := by rw [←hgG]; exact norm_pos_iff.mp (hr.trans (hom _ hex))
  rw [flowLaurentProfile_actual _ h0 hn hex,he (inverse_of_exterior_in_disc hex),
    flowDiskMap_eq_div (inv_ne_zero hG),inv_inv,hgG]
  field_simp
  <;> ring

theorem initial_flow_coefficients {g φ : ℂ → ℂ} (hg : Sigma g) {ρ : ℝ} (hr : 0<ρ) {w : ℂ}
    (he : EqOn φ (flowDiskMap g w ρ) disc) (hd : deriv φ 0=(ρ:ℂ))
    (hom : ∀ v∈exterior, ρ<‖g v-w‖) :
    flowRemainder g φ (ρ:ℂ) 0 = -w ∧ storedRemainder (flowRemainder g φ ρ)=0 := by
  have h := initial_laurent_germ hg hr he hd hom
  have h0 := h.eq_of_nhds
  have d : deriv (flowLaurentProfile g φ ρ) 0 = -w := by
    rw [h.deriv_eq]
    simpa [id_eq, Pi.sub_def] using (((hasDerivAt_id (0:ℂ)).const_mul w).const_sub 1).deriv
  have E : flowRemainder g φ ρ =ᶠ[𝓝 0] fun _ => -w := by
    filter_upwards [h] with y hy
    by_cases hn : y=0
    · simp [hn,flowRemainder,d]
    · rw [flowRemainder,dslope_of_ne _ hn,slope_def_field,hy,h0,sub_zero]
      field_simp
      <;> ring
  refine ⟨E.eq_of_nhds, ?_⟩
  ext k
  rw [storedRemainder,PowerSeries.coeff_mk,taylorCoeff_congr E (k+1)]
  simp [taylorCoeff,iteratedDeriv_const]

theorem terminal_flow_coefficients {g φ : ℂ → ℂ} (hg : Sigma g) (he : EqOn φ id disc)
    (hd : deriv φ 0=1) : flowRemainder g φ 1 0=0 ∧
      ∀ k, (storedRemainder (flowRemainder g φ 1)).coeff k = -inverseCoeff g (k+1) := by
  have h := terminal_laurent_germ hg he hd
  have hA := (inverse_germ hg).1.congr h.symm
  refine ⟨?_,?_⟩
  · rw [flowRemainder,dslope_same,h.deriv_eq,(inverse_germ hg).2.1]
  · intro k
    rw [storedRemainder,PowerSeries.coeff_mk,flowRemainder,taylorCoeff_dslope hA,taylorCoeff_congr h]
    rfl

end Springer
