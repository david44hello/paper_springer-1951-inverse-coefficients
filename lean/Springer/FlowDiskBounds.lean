import Springer.FlowNormalization

noncomputable section
open Set Complex Filter Asymptotics
open scoped Topology
namespace Springer

/-- Schwarz's lemma of order two gives a uniform substitute for Koebe near zero.
It applies to every member of a family of disk self-maps with a common lower bound
on the derivative at the origin. -/
theorem disk_quadratic_error {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disc)
    (hm : MapsTo f disc disc) (h0 : f 0=0) {b : ℂ} (hb : HasDerivAt f b 0)
    (hb1 : ‖b‖ ≤ 1) {z : ℂ} (hz : z∈disc) : ‖f z - b*z‖ ≤ 2*‖z‖^2 := by
  let F := fun v : ℂ => f v-b*v
  have hF : DifferentiableOn ℂ F disc := hf.sub (by fun_prop)
  have hz0 : F 0=0 := by simp [F,h0]
  have hd : HasDerivAt F 0 0 := by
    simpa [F,id_eq,Pi.sub_def] using hb.sub ((hasDerivAt_id (0:ℂ)).const_mul b)
  have hmap : MapsTo F disc (Metric.closedBall (F 0) 2) := by
    intro v hv
    have h₁ : ‖f v‖ < 1 := by simpa [disc] using hm hv
    have h₂ : ‖v‖ < 1 := by simpa [disc] using hv
    rw [hz0,Metric.mem_closedBall,dist_zero_right]
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    have he : ‖b‖*‖v‖ ≤ 1*‖v‖ := mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
    linarith
  have hl : (fun v => F v-F 0) =o[𝓝 0] (fun v : ℂ => ‖v-0‖^(1:ℕ)) := by
    simpa using hd.isLittleO.norm_right
  have H := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hF hmap hl hz
  simpa only [hz0,dist_zero_right,div_one, Nat.reduceAdd,F] using H

theorem disk_uniform_lower {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disc)
    (hm : MapsTo f disc disc) (h0 : f 0=0) {b : ℂ} (hb : HasDerivAt f b 0)
    (hb1 : ‖b‖ ≤ 1) {ρ : ℝ} (hr : ρ≤‖b‖) {z : ℂ} (hz : z∈disc) (hsmall : ‖z‖≤ρ/4) :
    (ρ/2)*‖z‖ ≤ ‖f z‖ := by
  have H := disk_quadratic_error hf hm h0 hb hb1 hz
  have ht := norm_sub_le (f z) (f z-b*z)
  rw [sub_sub_cancel, norm_mul] at ht
  have hr' := mul_le_mul_of_nonneg_right hr (norm_nonneg z)
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (norm_nonneg z)
  nlinarith

/-- With z=1/G(w), this bounds the change of inverse map uniformly in time. -/
theorem disk_reciprocal_error {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disc)
    (hm : MapsTo f disc disc) (h0 : f 0=0) {b : ℂ} (hb : HasDerivAt f b 0)
    (hb1 : ‖b‖ ≤ 1) {ρ : ℝ} (hρ : 0<ρ) (hr : ρ≤‖b‖)
    {z : ℂ} (hz : z∈disc) (hn : z≠0) (hsmall : ‖z‖≤ρ/4) :
    ‖b/f z-z⁻¹‖ ≤ 4/ρ := by
  have hu := disk_quadratic_error hf hm h0 hb hb1 hz
  have hl := disk_uniform_lower hf hm h0 hb hb1 hr hz hsmall
  have hnz := norm_pos_iff.mpr hn
  have hnf : 0<‖f z‖ := lt_of_lt_of_le (mul_pos (by linarith) hnz) hl
  have hfz := norm_pos_iff.mp hnf
  have heq : b/f z-z⁻¹=(b*z-f z)/(f z*z) := by field_simp
  rw [heq,norm_div,norm_mul,norm_sub_rev,div_le_div_iff₀ (mul_pos hnf hnz) hρ]
  calc
    ‖f z-b*z‖*ρ ≤ (2*‖z‖^2)*ρ := mul_le_mul_of_nonneg_right hu hρ.le
    _ = 4*((ρ/2)*‖z‖)*‖z‖ := by ring
    _ ≤ 4*‖f z‖*‖z‖ := by gcongr
    _ = _ := by ring

end Springer
