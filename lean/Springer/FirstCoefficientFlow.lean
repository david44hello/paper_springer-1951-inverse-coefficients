import Springer.ActualCoefficientFlow

noncomputable section
open Set MeasureTheory
namespace Springer

theorem CoefficientFlow.first_norm_le {g : ℂ → ℂ} (hg : Sigma g) {s : ℝ} (hs : s≤1) {H P μ}
    (h : CoefficientFlow g s H P μ) : ‖forwardCoeff g 1‖ ≤ 1-s := by
  letI : ∀ t, IsProbabilityMeasure (μ t) := h.prob
  let f := fun t => (H t).coeff 0
  let v := fun t => ∫ ξ : Circle, (ξ:ℂ)^2 ∂μ t
  have hac : AbsolutelyContinuousOnInterval (fun x : ℝ => x) s 1 :=
    LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  have hD : ∀ᵐ x ∂volume.restrict (Icc s 1), HasDerivAt f (v x) x ∧ ‖v x‖ ≤ deriv (fun t : ℝ => t) x := by
    filter_upwards [h.ode] with x hx
    constructor
    · simpa only [f,v,averagedDirection_zero] using hx.2 0
    · have hh : ∀ᵐ ξ : Circle ∂μ x, ‖(ξ:ℂ)^2‖ ≤ 1 :=
        Filter.Eventually.of_forall (fun ξ => by simp)
      change ‖∫ ξ : Circle, (ξ:ℂ)^2 ∂μ x‖ ≤ deriv id x
      rw [(hasDerivAt_id x).deriv]
      simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hh
  have hp := comparison_integrate hs (h.coeffAC 0) hac hD
  have e : f 1=forwardCoeff g 1 := by change (H 1).coeff 0=_; rw [h.terminal]; simp [inverse_first_eq_neg_forward hg]
  have es : f s=0 := by simp [f,h.initial]
  change ‖f 1-f s‖ ≤ 1-s at hp
  simpa only [e,es,sub_zero] using hp

theorem firstCoeff_norm_le_of_loewner (hL : NormalizedLoewnerRepresentation) {g : ℂ → ℂ}
    (hg : Sigma g) : ‖forwardCoeff g 1‖≤1 := by
  let C : Set (ℂ × ℂ) := {p | ‖p.1‖≤1}
  have hclosed : IsClosed C := isClosed_le continuous_fst.norm continuous_const
  apply closed_coeff_constraint hclosed 1 1 _ hg
  intro f hf ho
  obtain ⟨w,ρ,hr,hr1,hom⟩ := ho
  obtain ⟨p,φ,hφ⟩ := normalizedLoewner_of_omitted_disk hL hf w hr hr1 hom
  obtain ⟨μ,hF,_⟩ := actual_coefficient_flow hf hr hr1 hom hφ
  have hs : ρ^2≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (by linarith : 0≤1+ρ)]
  exact (hF.first_norm_le hf hs).trans (sub_le_self _ (sq_nonneg ρ))

theorem odd_numerical_of_loewner (hL : NormalizedLoewnerRepresentation) {g : ℂ → ℂ}
    (hg : Sigma g) (m : ℕ) :
    ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ) ∧
      (‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ) → ‖forwardCoeff g 1‖=1) := by
  have hd := (disk_theorem_of_loewner hL hg m).1
  have hb := firstCoeff_norm_le_of_loewner hL hg
  exact ⟨hd.odd hb,hd.firstCoeff_of_equality hb⟩

end Springer
