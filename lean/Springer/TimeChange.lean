import Springer.FlowDiskBounds

noncomputable section
open Set Complex MeasureTheory
namespace Springer

def elapsed (t : ℝ) := -Real.log t/2

theorem elapsed_deriv {t : ℝ} (ht : 0<t) : HasDerivAt elapsed (-(1/(2*t))) t := by
  apply ((Real.hasDerivAt_log ht.ne').neg.div_const 2).congr_deriv
  field_simp

@[simp] theorem elapsed_one : elapsed 1=0 := by simp [elapsed]

theorem elapsed_start {ρ : ℝ} (hρ : 0<ρ) : elapsed (ρ^2)=Real.log (1/ρ) := by
  rw [elapsed,Real.log_pow, one_div,Real.log_inv]; push_cast; ring

theorem elapsed_mem {ρ t : ℝ} (hr : 0<ρ) (ht : t∈Icc (ρ^2) 1) :
    elapsed t∈Icc 0 (Real.log (1/ρ)) := by
  have htp : 0<t := (sq_pos_of_pos hr).trans_le ht.1
  have h₁ := Real.log_nonpos htp.le ht.2
  have h₂ := Real.log_le_log (sq_pos_of_pos hr) ht.1
  rw [←elapsed_start hr]
  unfold elapsed
  constructor <;> linarith

/-- The inverse exponential time map sends null sets to null sets. -/
theorem elapsed_ae {ρ : ℝ} (hr : 0<ρ) {p : ℝ → Prop}
    (h : ∀ᵐ l ∂volume.restrict (Icc 0 (Real.log (1/ρ))), p l) :
    ∀ᵐ t ∂volume.restrict (Icc (ρ^2) 1), p (elapsed t) := by
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff] at h ⊢
  let bad := {l : ℝ | ¬(l∈Icc 0 (Real.log (1/ρ)) → p l)}
  let rev := fun l : ℝ => Real.exp (-2*l)
  have hrev : DifferentiableOn ℝ rev bad := by dsimp [rev]; fun_prop
  apply measure_mono_null _ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hrev h)
  intro t ht
  push_neg at ht
  have ht' : t∈Icc (ρ^2) 1 ∧ ¬p (elapsed t) := by simpa using ht
  refine ⟨elapsed t, fun good => ht'.2 (good (elapsed_mem hr ht'.1)), ?_⟩
  have hp : 0<t := (sq_pos_of_pos hr).trans_le ht'.1.1
  simp only [rev,elapsed,show -2*(-Real.log t/2)=Real.log t by ring,Real.exp_log hp]

def flowKernel (z : ℂ) (ξ : Circle) := (1+(ξ:ℂ)*z)/(1-(ξ:ℂ)*z)

def flowVelocity (a Y : ℂ) (ξ : Circle) := (ξ:ℂ)/a+(ξ:ℂ)^2/(Y-a*ξ)

private theorem kernel_denom {z : ℂ} (hz : ‖z‖<1) (ξ : Circle) : 1-(ξ:ℂ)*z≠0 := by
  intro h
  have e := congrArg norm (sub_eq_zero.mp h)
  simp [norm_mul] at e
  linarith

private theorem y_denom {z a : ℂ} (ha : a≠0) (hn : z≠0) (hz : ‖z‖<1) (ξ : Circle) :
    a/z-a*ξ≠0 := by
  have H := kernel_denom hz ξ
  rw [show a/z-a*ξ=(a/z)*(1-(ξ:ℂ)*z) by field_simp]
  exact mul_ne_zero (div_ne_zero ha hn) H

theorem velocity_kernel_identity {z a : ℂ} (ha : a≠0) (hn : z≠0) (hz : ‖z‖<1) (ξ : Circle) :
    (a/z)/(2*a^2)*(1-flowKernel z ξ) = -flowVelocity a (a/z) ξ := by
  have h₁ := kernel_denom hz ξ
  have h₂ := y_denom ha hn hz ξ
  unfold flowKernel flowVelocity
  rw [show a/z-a*ξ=(a/z)*(1-(ξ:ℂ)*z) by field_simp]
  generalize he : 1-(ξ:ℂ)*z = e at h₁ ⊢
  field_simp [ha,hn,h₁]
  <;> rw [←he] <;> ring

/-- Change from elapsed Loewner time to t and expand the Herglotz kernel. The
derivative hypothesis is pointwise, so it also applies on a common conull set. -/
theorem flow_timeChange {φ : ℝ → ℂ} {t : ℝ} (ht : 0<t) (μ : Measure Circle)
    [IsProbabilityMeasure μ] (hn : φ (elapsed t)≠0) (hz : ‖φ (elapsed t)‖<1)
    (hφ : HasDerivAt φ (-φ (elapsed t)*(∫ ξ : Circle, flowKernel (φ (elapsed t)) ξ ∂μ)) (elapsed t)) :
    HasDerivAt (fun x => (Real.sqrt x:ℂ)/φ (elapsed x))
      (-(∫ ξ : Circle, flowVelocity (Real.sqrt t) ((Real.sqrt t:ℂ)/φ (elapsed t)) ξ ∂μ)) t := by
  let z := φ (elapsed t)
  let a : ℂ := Real.sqrt t
  have ha : a≠0 := by dsimp [a]; exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hs : a^2=(t:ℂ) := by dsimp [a]; exact_mod_cast Real.sq_sqrt ht.le
  have hφt := hφ.scomp t (elapsed_deriv ht)
  have h := ((Real.hasDerivAt_sqrt ht.ne').ofReal_comp).div hφt hn
  apply h.congr_deriv
  let p := ∫ ξ : Circle, flowKernel z ξ ∂μ
  change ((↑(1/(2*Real.sqrt t):ℝ):ℂ)*z - a*((-(1/(2*t)):ℝ) • (-z*p)))/z^2=_
  have E : ((↑(1/(2*Real.sqrt t):ℝ):ℂ)*z - a*((-(1/(2*t)):ℝ) • (-z*p)))/z^2 =
      (a/z)/(2*a^2)*(1-p) := by
    simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_mul,
      Complex.ofReal_ofNat,Complex.ofReal_one]
    change ((1/(2*a))*z-a*(-(1/(2*(t:ℂ)))*(-z*p)))/z^2=_
    rw [←hs]
    field_simp [hn,ha]
    <;> ring
  rw [E]
  have hK : Integrable (flowKernel z) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold flowKernel
    exact (by fun_prop : Continuous (fun ξ : Circle => 1+(ξ:ℂ)*z)).div
      (by fun_prop : Continuous (fun ξ : Circle => 1-(ξ:ℂ)*z)) (kernel_denom hz)
  have hmean : 1-p=∫ ξ : Circle, (1-flowKernel z ξ) ∂μ := by
    rw [integral_sub (integrable_const (1:ℂ)) hK]; simp [p]
  rw [hmean,←integral_const_mul,←integral_neg]
  apply integral_congr_ae
  filter_upwards with ξ
  exact velocity_kernel_identity ha hn hz ξ

/-- An inverse branch at an exterior value supplies both endpoints of the
normalized disk evolution. -/
theorem flow_endpoints {g : ℂ → ℂ} {ρ : ℝ} (hr : 0<ρ) {w₀ w G : ℂ}
    (he : G∈exterior) (hG : g G=w) (hom : ∀ v∈exterior, ρ<‖g v-w₀‖)
    {φ : ℝ → ℂ → ℂ} (hstart : φ (Real.log (1/ρ)) G⁻¹=flowDiskMap g w₀ ρ G⁻¹)
    (hend : φ 0 G⁻¹=G⁻¹) :
    (Real.sqrt (ρ^2):ℂ)/φ (elapsed (ρ^2)) G⁻¹ = w-w₀ ∧
      (Real.sqrt 1:ℂ)/φ (elapsed 1) G⁻¹=G := by
  have hn : G≠0 := norm_pos_iff.mp (zero_lt_one.trans he)
  have hb : (ρ:ℂ)≠0 := by exact_mod_cast hr.ne'
  have hw : w-w₀≠0 := by simpa [hG] using norm_pos_iff.mp (hr.trans (hom G he))
  constructor
  · rw [Real.sqrt_sq hr.le,elapsed_start hr,hstart,flowDiskMap_eq_div (inv_ne_zero hn),inv_inv,hG]
    field_simp
  · simp [hend]

end Springer
