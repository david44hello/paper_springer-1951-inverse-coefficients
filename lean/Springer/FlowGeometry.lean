import Springer.LoewnerPath
import Springer.FlowEndpoints
import Springer.ContourVelocity

noncomputable section
open Set Complex Filter Function MeasureTheory Metric
open scoped Topology
namespace Springer

def timeRemainder (g : ℂ → ℂ) (φ : ℝ → ℂ → ℂ) (t : ℝ) :=
  flowRemainder g (φ (elapsed t)) (Real.sqrt t)

structure CommonDisk (g : ℂ → ℂ) (ρ r : ℝ) : Prop where
  positive : 0<r
  small : ∀ y∈closedBall 0 r, ‖inverseCoordinate g y‖<ρ/4
  actual : ∀ y∈closedBall 0 r, y≠0 → invFunOn g exterior y⁻¹∈exterior
  coordinate : AnalyticOnNhd ℂ (inverseCoordinate g) (closedBall 0 r)
  regular : ∀ (φ : ℂ → ℂ) (b : ℂ), AnalyticOnNhd ℂ φ disc → InjOn φ disc → φ 0=0 →
    deriv φ 0=b → b≠0 → AnalyticOnNhd ℂ (flowRemainder g φ b) (closedBall 0 r)

theorem exists_commonDisk {g : ℂ → ℂ} (hg : Sigma g) {ρ : ℝ} (hr : 0<ρ) :
    ∃ r, CommonDisk g ρ r := by
  obtain ⟨R,hR,hsm,hA⟩ := common_flow_radius hg (show 0<ρ/4 by linarith)
  have he := eventually_nhdsWithin_iff.mp (inverse_germ hg).2.2.2
  have hq : AnalyticAt ℂ (inverseCoordinate g) 0 :=
    analyticAt_id.div (inverse_germ hg).1 (by simp [inverseProfile])
  obtain ⟨S,hS,hB⟩ := Metric.mem_nhds_iff.mp (he.and hq.eventually_analyticAt)
  let r := min R S/2
  have hm : 0 < min R S := lt_min hR hS
  have h₁ : closedBall (0:ℂ) r ⊆ ball 0 R :=
    closedBall_subset_ball (show r<R by dsimp [r]; linarith [min_le_left R S])
  have h₂ : closedBall (0:ℂ) r ⊆ ball 0 S :=
    closedBall_subset_ball (show r<S by dsimp [r]; linarith [min_le_right R S])
  exact ⟨r, ⟨half_pos hm,fun y hy => hsm y (h₁ hy),fun y hy hn => ((hB (h₂ hy)).1 hn).1,
    fun _ hy => (hB (h₂ hy)).2,fun φ b ha hu h0 hd hb => (hA φ b ha hu h0 hd hb).mono h₁⟩⟩

theorem CommonDisk.coord_ne {g : ℂ → ℂ} {ρ r : ℝ} (D : CommonDisk g ρ r)
    {y : ℂ} (hy : y∈closedBall 0 r) (hn : y≠0) : inverseCoordinate g y≠0 := by
  rw [inverseCoordinate_actual hn]
  exact inv_ne_zero (norm_pos_iff.mp (zero_lt_one.trans (D.actual y hy hn)))

theorem actual_timeRemainder {g ψ : ℂ → ℂ} {ρ r t : ℝ} {p φ : ℝ → ℂ → ℂ}
    (D : CommonDisk g ρ r) (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ)
    (ht : t∈Icc (ρ^2) 1) {y : ℂ} (hy : y∈closedBall 0 r) (hn : y≠0) :
    timeRemainder g φ t y=(Real.sqrt t:ℂ)/φ (elapsed t) (inverseCoordinate g y)-y⁻¹ := by
  have htp := (sq_pos_of_pos hr).trans_le ht.1
  have hl := elapsed_mem hr ht
  have h0 := h.fixed_zero _ hl
  have hd := (h.at_origin _ hl).deriv
  rw [exp_neg_elapsed htp] at hd
  have hb : (Real.sqrt t:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr htp).ne'
  rw [timeRemainder,flowRemainder,dslope_of_ne _ hn,slope_def_field,
    flowLaurentProfile_zero g hd hb,flowLaurentProfile_actual _ h0 hn (D.actual y hy hn),
    sub_zero,inverseCoordinate_actual hn]
  ring_nf
  <;> field_simp

theorem CommonDisk.slice_analytic {g ψ : ℂ → ℂ} {ρ r t : ℝ} {p φ : ℝ → ℂ → ℂ}
    (D : CommonDisk g ρ r) (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ) (ht : t∈Icc (ρ^2) 1) :
    AnalyticOnNhd ℂ (timeRemainder g φ t) (closedBall 0 r) := by
  have hl := elapsed_mem hr ht
  have ht' := (sq_pos_of_pos hr).trans_le ht.1
  apply D.regular _ _ (h.analytic _ hl) (h.univalent _ hl) (h.fixed_zero _ hl)
  · simpa only [exp_neg_elapsed ht'] using (h.at_origin _ hl).deriv
  · exact_mod_cast (Real.sqrt_pos.mpr ht').ne'

theorem normalized_contour_denominator {g ψ : ℂ → ℂ} {ρ r t : ℝ} {p φ : ℝ → ℂ → ℂ}
    (D : CommonDisk g ρ r) (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ) (hr1 : ρ<1)
    (ht : t∈Icc (ρ^2) 1) {y : ℂ} (hy : y∈closedBall 0 r) (ξ : Circle) :
    1+y*(timeRemainder g φ t y-(Real.sqrt t:ℂ)*ξ)≠0 := by
  by_cases hn : y=0
  · simp [hn]
  let z := inverseCoordinate g y
  let v := φ (elapsed t) z
  let a : ℂ := Real.sqrt t
  have hz : z∈disc := by simpa [disc] using (D.small y hy).trans (by linarith : ρ/4<1)
  have hl := elapsed_mem hr ht
  have h0 := h.fixed_zero _ hl
  have hv : v≠0 := fun e => D.coord_ne hy hn
    (h.univalent _ hl hz (by simp [disc]) (e.trans h0.symm))
  have hv' : ‖v‖<1 := by simpa [v,disc] using h.maps _ hl hz
  have ha : a≠0 := by dsimp [a]; exact_mod_cast (Real.sqrt_pos.mpr ((sq_pos_of_pos hr).trans_le ht.1)).ne'
  have hξ : 1-(ξ:ℂ)*v ≠ 0 := by
    intro hh
    have he := congrArg norm (sub_eq_zero.mp hh)
    simp at he
    linarith
  rw [actual_timeRemainder D h hr ht hy hn]
  change 1+y*(a/v-y⁻¹-a*ξ)≠0
  rw [show 1+y*(a/v-y⁻¹-a*ξ)=y*a/v*(1-(ξ:ℂ)*v) by field_simp; ring]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero hn ha) hv) hξ

end Springer
