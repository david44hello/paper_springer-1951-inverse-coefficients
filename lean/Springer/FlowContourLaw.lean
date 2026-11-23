import Springer.FlowContourBounds

noncomputable section
open Set Filter Complex MeasureTheory Metric
open scoped Topology Real NNReal
namespace Springer

theorem CommonDisk.field_eq_integral {g ψ : ℂ → ℂ} {ρ r t : ℝ} {p φ : ℝ → ℂ → ℂ}
    (D : CommonDisk g ρ r) (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ) (hr1 : ρ<1)
    (μ : ℝ → Measure Circle) [∀ t, IsProbabilityMeasure (μ t)] (ht : t∈Icc (ρ^2) 1)
    {y : ℂ} (hy : y∈closedBall 0 r) (hn : y≠0) :
    contourField g φ μ (ρ^2) t y =
      ∫ ξ : Circle, reciprocalVelocity (timeRemainder g φ t) (Real.sqrt t) ξ y ∂μ t := by
  let z := inverseCoordinate g y
  let v := φ (elapsed t) z
  let a : ℂ := Real.sqrt t
  have hl := elapsed_mem hr ht
  have hz : z∈disc := by simpa [z,disc] using (D.small y hy).trans (by linarith : ρ/4<1)
  have h0 := h.fixed_zero _ hl
  have hv : v≠0 := fun e => D.coord_ne hy hn (h.univalent _ hl hz (by simp [disc]) (e.trans h0.symm))
  have hv1 : ‖v‖<1 := by simpa [v,disc] using h.maps _ hl hz
  have ha : a≠0 := by dsimp [a]; exact_mod_cast (Real.sqrt_pos.mpr ((sq_pos_of_pos hr).trans_le ht.1)).ne'
  rw [contourField,clipTime_eq ht]
  change -velocityTransform (μ t) v/a=_
  rw [neg_div,← flowVelocity_eq_transform _ ha hv hv1,←integral_neg]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [reciprocalVelocity,actual_timeRemainder D h hr ht hy hn]
  change -( (ξ:ℂ)/a + (ξ:ℂ)^2/(a/v-a*ξ)) =
    -(ξ:ℂ)/a - (ξ:ℂ)^2*(y*(1+y*(a/v-y⁻¹-a*ξ))⁻¹)
  have e : 1+y*(a/v-y⁻¹-a*ξ)=y*(a/v-a*ξ) := by field_simp; ring
  rw [e,mul_inv_rev]
  field_simp [hn]
  <;> ring

def contourSlope (g : ℂ → ℂ) (φ : ℝ → ℂ → ℂ) (μ : ℝ → Measure Circle)
    (s r : ℝ) (n : ℕ) (t : ℝ) :=
  ∫ θ, contourWeight r n θ*contourField g φ μ s t (circleMap 0 r θ) ∂angleMeasure

theorem CommonDisk.contour_increment {g ψ : ℂ → ℂ} {ρ r : ℝ} {p φ : ℝ → ℂ → ℂ}
    (D : CommonDisk g ρ r) (h : NormalizedLoewnerData ψ ρ p φ) (hr : 0<ρ) (hr1 : ρ<1)
    (μ : ℝ → Measure Circle) [∀ t, IsProbabilityMeasure (μ t)]
    (hm : ∀ f : C(Circle,ℂ), Measurable (fun t => ∫ ξ, f ξ ∂μ t))
    (hpath : ∀ z : ℂ, z≠0 → ‖z‖≤ρ/4 →
      AbsolutelyContinuousOnInterval (fun t => (Real.sqrt t:ℂ)/φ (elapsed t) z) (ρ^2) 1 ∧
      (∀ᵐ t ∂volume.restrict (Icc (ρ^2) 1), HasDerivAt (fun x => (Real.sqrt x:ℂ)/φ (elapsed x) z)
        (-velocityTransform (μ t) (φ (elapsed t) z)/(Real.sqrt t:ℂ)) t))
    {t : ℝ} (ht : t∈Icc (ρ^2) 1) (n : ℕ) :
    taylorCoeff (timeRemainder g φ t) n-taylorCoeff (timeRemainder g φ (ρ^2)) n =
      ∫ x : ℝ in ρ^2..t, contourSlope g φ μ (ρ^2) r n x := by
  have hs : ρ^2 ≤ 1 := ht.1.trans ht.2
  have hinit : ρ^2 ∈ Icc (ρ^2) 1 := ⟨le_rfl,hs⟩
  have reg (x : ℝ) (hx : x∈Icc (ρ^2) 1) := D.slice_analytic h hr hx
  have hi (x : ℝ) (hx : x∈Icc (ρ^2) 1) : Integrable
      (fun θ => contourWeight r n θ*timeRemainder g φ x (circleMap 0 r θ)) angleMeasure := by
    have H := (reg x hx).continuousOn.comp_continuous (continuous_circleMap _ _) (circleMap_mem_closedBall _ D.positive.le)
    exact ((contourWeight_continuous D.positive n).mul H).continuousOn.integrableOn_compact isCompact_Icc
  apply taylorCoeff_increment D.positive ht.1 (timeRemainder g φ) (contourField g φ μ (ρ^2))
    ((reg _ hinit).differentiableOn.diffContOnCl_ball Subset.rfl)
    ((reg _ ht).differentiableOn.diffContOnCl_ball Subset.rfl) n (hi _ hinit) (hi _ ht)
    (weighted_field_integrable D h hr hr1 μ hm n _ _)
  intro θ
  let y := circleMap 0 r θ
  have hy : y∈closedBall 0 r := circleMap_mem_closedBall _ D.positive.le _
  have hn : y≠0 := by
    intro he
    have hh := Metric.mem_sphere.mp (circleMap_mem_sphere 0 D.positive.le θ)
    change dist y 0=r at hh
    simp [he] at hh
    linarith [D.positive]
  obtain ⟨hac,hd⟩ := hpath (inverseCoordinate g y) (D.coord_ne hy hn) (D.small y hy).le
  have he := trajectory_increment hs hac hd ht
  rw [actual_timeRemainder D h hr ht hy hn,actual_timeRemainder D h hr hinit hy hn,sub_sub_sub_cancel_right]
  apply he.trans
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le ht.1] at hx
  simp only [y,contourField,clipTime_eq (show x∈Icc (ρ^2) 1 from ⟨hx.1,hx.2.trans ht.2⟩)]

end Springer
