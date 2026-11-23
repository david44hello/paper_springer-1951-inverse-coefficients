import Springer.TimeChange
import Springer.Coefficients

noncomputable section
open Complex Set Filter Function
open scoped Topology
namespace Springer

/-- Reciprocal of the true inverse, using its analytic inverse profile at infinity. -/
def inverseCoordinate (g : ℂ → ℂ) (y : ℂ) := y / inverseProfile g y

theorem inverseCoordinate_actual {g : ℂ → ℂ} {y : ℂ} (hy : y≠0) :
    inverseCoordinate g y = (invFunOn g exterior y⁻¹)⁻¹ := by
  simp [inverseCoordinate,inverseProfile,profile,hy,div_eq_mul_inv,mul_inv_rev,mul_comm,mul_left_comm]

def flowLaurentProfile (g φ : ℂ → ℂ) (b : ℂ) (y : ℂ) :=
  b*inverseProfile g y / dslope φ 0 (inverseCoordinate g y)

def flowRemainder (g φ : ℂ → ℂ) (b : ℂ) := dslope (flowLaurentProfile g φ b) 0

theorem flowLaurentProfile_zero (g : ℂ → ℂ) {φ : ℂ → ℂ} {b : ℂ}
    (hd : deriv φ 0=b) (hb : b≠0) : flowLaurentProfile g φ b 0=1 := by
  simp [flowLaurentProfile,inverseCoordinate,inverseProfile,hd,hb]

theorem flowLaurentProfile_actual {g φ : ℂ → ℂ} (b : ℂ) (h0 : φ 0=0)
    {y : ℂ} (hy : y≠0) (hG : invFunOn g exterior y⁻¹ ∈ exterior) :
    flowLaurentProfile g φ b y=y*(b/φ ((invFunOn g exterior y⁻¹)⁻¹)) := by
  let G := invFunOn g exterior y⁻¹
  have hn : G≠0 := norm_pos_iff.mp (zero_lt_one.trans hG)
  rw [flowLaurentProfile,inverseCoordinate_actual hy,dslope_of_ne _ (inv_ne_zero hn),slope_def_field,h0,sub_zero,sub_zero]
  change b*profile (invFunOn g exterior) y/(φ G⁻¹/G⁻¹)=y*(b/φ G⁻¹)
  rw [profile,ite_eq_right hy]
  by_cases hφ : φ G⁻¹=0
  · simp [hφ]
  · change b*(y*G)/(φ G⁻¹/G⁻¹)=_
    field_simp
    <;> ring

/-- The radius depends only on the exterior map and the chosen reciprocal-coordinate
cutoff. All normalized univalent disk maps have their Laurent expansions there. -/
theorem common_flow_radius {g : ℂ → ℂ} (hg : Sigma g) {δ : ℝ} (hδ : 0<δ) :
    ∃ R : ℝ, 0<R ∧ (∀ y∈Metric.ball (0:ℂ) R, ‖inverseCoordinate g y‖ < δ) ∧
      ∀ (φ : ℂ → ℂ) (b : ℂ), AnalyticOnNhd ℂ φ disc → InjOn φ disc → φ 0=0 →
        deriv φ 0=b → b≠0 → AnalyticOnNhd ℂ (flowRemainder g φ b) (Metric.ball (0:ℂ) R) := by
  have hi := (inverse_germ hg).1
  have hne : inverseProfile g 0≠0 := by simp [inverseProfile]
  have hq : AnalyticAt ℂ (inverseCoordinate g) 0 := analyticAt_id.div hi hne
  have hsmall : ∀ᶠ y in 𝓝 (0:ℂ), ‖inverseCoordinate g y‖ < min δ 1 :=
    hq.continuousAt.norm.eventually_lt continuousAt_const (by simp [inverseCoordinate,hδ])
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp
    (hsmall.and (hi.eventually_analyticAt.and (hi.continuousAt.eventually_ne hne)))
  refine ⟨R,hR,fun y hy => (lt_min_iff.mp (hball hy).1).1,?_⟩
  intro φ b hφ hu h0 hd hb
  have hdisk : disc ∈ 𝓝 (0:ℂ) := Metric.ball_mem_nhds _ zero_lt_one
  have hop : IsOpen disc := Metric.isOpen_ball
  have hslope := ((Complex.differentiableOn_dslope hdisk).mpr hφ.differentiableOn).analyticOnNhd hop
  have hprof : AnalyticOnNhd ℂ (flowLaurentProfile g φ b) (Metric.ball (0:ℂ) R) := by
    intro y hy
    obtain ⟨hsm,hi',hne'⟩ := hball hy
    let v := inverseCoordinate g y
    have hv : v∈disc := by simpa [v,disc] using (lt_min_iff.mp hsm).2
    have hv' : AnalyticAt ℂ (inverseCoordinate g) y := analyticAt_id.div hi' hne'
    have hs : dslope φ 0 v ≠ 0 := by
      by_cases hn : v=0
      · simpa [hn,hd] using hb
      · rw [dslope_of_ne _ hn,slope_def_field,h0,sub_zero,sub_zero]
        apply div_ne_zero _ hn
        exact fun he => hn (hu hv (by simp [disc]) (he.trans h0.symm))
    exact (analyticAt_const.mul hi').div ((hslope v hv).comp (f:=inverseCoordinate g) hv') hs
  exact ((Complex.differentiableOn_dslope (Metric.ball_mem_nhds _ hR)).mpr hprof.differentiableOn).analyticOnNhd
    Metric.isOpen_ball

theorem taylorCoeff_dslope {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    taylorCoeff (dslope f 0) n = taylorCoeff f (n+1) := by
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hf.eventually_analyticAt
  have hF : AnalyticOnNhd ℂ f (Metric.ball 0 R) := fun z hz => hball hz
  have hds := ((Complex.differentiableOn_dslope (Metric.ball_mem_nhds _ hR)).mpr hF.differentiableOn).analyticOnNhd
    Metric.isOpen_ball 0 (Metric.mem_ball_self hR)
  have E : (fun x : ℂ => x^1*dslope f 0 x)=(fun x => f x-f 0) := by
    funext x
    simpa only [sub_zero,smul_eq_mul,pow_one] using sub_smul_dslope f 0 x
  have H := taylorCoeff_shift hds 1 (n+1)
  rw [E,taylorCoeff_sub hf analyticAt_const] at H
  simpa [taylorCoeff,iteratedDeriv_const] using H.symm

end Springer
