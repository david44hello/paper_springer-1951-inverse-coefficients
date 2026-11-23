import Springer.Basic

noncomputable section
open Set Complex Function
namespace Springer

/-- The reciprocal disk self-map used as the terminal map of the radial evolution.
Writing its denominator with the normalized profile removes the singularity at 0. -/
def flowDiskMap (g : ℂ → ℂ) (w : ℂ) (ρ : ℝ) (z : ℂ) :=
  (ρ:ℂ)*z / (profile g z-z*w)

@[simp] theorem flowDiskMap_zero (g : ℂ → ℂ) (w : ℂ) (ρ : ℝ) :
    flowDiskMap g w ρ 0=0 := by simp [flowDiskMap]

private theorem exterior_of_disk_inv {z : ℂ} (hz : z ∈ disc) (hn : z≠0) : z⁻¹∈exterior := by
  change 1<‖z⁻¹‖
  rw [norm_inv,one_lt_inv₀ (norm_pos_iff.mpr hn)]
  simpa [disc] using hz

theorem flowDiskMap_eq_div {g : ℂ → ℂ} {w z : ℂ} {ρ : ℝ} (hn : z≠0) :
    flowDiskMap g w ρ z=(ρ:ℂ)/(g z⁻¹-w) := by
  rw [flowDiskMap,profile,ite_eq_right hn,←mul_sub]
  by_cases he : g z⁻¹-w=0
  · simp [he]
  · field_simp

theorem flowDiskMap_properties {g : ℂ → ℂ} (hg : Sigma g) {w : ℂ} {ρ : ℝ}
    (hp : 0 < ρ) (homit : ∀ v ∈ exterior, ρ < ‖g v - w‖) :
    AnalyticOnNhd ℂ (flowDiskMap g w ρ) disc ∧
    MapsTo (flowDiskMap g w ρ) disc disc ∧ InjOn (flowDiskMap g w ρ) disc ∧
    HasDerivAt (flowDiskMap g w ρ) (ρ:ℂ) 0 := by
  have hr : (ρ:ℂ)≠0 := by exact_mod_cast hp.ne'
  have good {z : ℂ} (hz : z ∈ disc) (hn : z≠0) : g z⁻¹-w ≠ 0 :=
    norm_pos_iff.mp (hp.trans (homit _ (exterior_of_disk_inv hz hn)))
  have hden {z : ℂ} (hz : z∈disc) : profile g z-z*w ≠ 0 := by
    by_cases hn : z=0
    · simp [hn]
    · rw [profile,ite_eq_right hn,←mul_sub]
      exact mul_ne_zero hn (good hz hn)
  have nzero {z : ℂ} (hz : z ∈ disc) (hn : z≠0) : flowDiskMap g w ρ z ≠ 0 := by
    rw [flowDiskMap_eq_div hn]
    exact div_ne_zero hr (good hz hn)
  constructor
  · intro z hz
    exact (analyticAt_const.mul analyticAt_id).div
      ((hg.regular _ hz).sub (analyticAt_id.mul analyticAt_const)) (hden hz)
  constructor
  · intro z hz
    by_cases hn : z=0
    · simp [hn,disc]
    · rw [disc,Metric.mem_ball,dist_zero_right,flowDiskMap_eq_div hn,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,
        div_lt_one (norm_pos_iff.mpr (good hz hn))]
      exact homit _ (exterior_of_disk_inv hz hn)
  constructor
  · intro z hz v hv he
    by_cases hn : z=0
    · subst z
      by_contra hvn
      exact nzero hv (Ne.symm hvn) ((flowDiskMap_zero g w ρ).symm.trans he).symm
    by_cases hvn : v=0
    · subst v
      exact False.elim (nzero hz hn (he.trans (flowDiskMap_zero g w ρ)))
    rw [flowDiskMap_eq_div hn,flowDiskMap_eq_div hvn] at he
    apply inv_injective
    apply hg.univalent (exterior_of_disk_inv hz hn) (exterior_of_disk_inv hv hvn)
    simp only [div_eq_mul_inv] at he
    exact sub_left_inj.mp (inv_injective (mul_left_cancel₀ hr he))
  · have h0 : (0:ℂ)∈disc := by simp [disc]
    have hnum := (hasDerivAt_id (0:ℂ)).const_mul (ρ:ℂ)
    have hd := ((hg.regular _ h0).differentiableAt.hasDerivAt).sub ((hasDerivAt_id (0:ℂ)).mul_const w)
    change HasDerivAt (fun i : ℂ => (ρ:ℂ)*i/(profile g i-i*w)) (ρ:ℂ) 0
    simpa [Pi.div_def, Pi.sub_def, Function.comp_def, id_eq] using hnum.div hd (hden h0)

end Springer
