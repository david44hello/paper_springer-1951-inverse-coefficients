import Challenge.ActualCoefficientFlow

/- Frozen input: Springer/FirstCoefficientFlow.lean -/
noncomputable section
open Set MeasureTheory
namespace Springer

theorem CoefficientFlow.first_norm_le {g : ℂ → ℂ} (hg : Sigma g) {s : ℝ} (hs : s≤1) {H P μ}
    (h : CoefficientFlow g s H P μ) : ‖forwardCoeff g 1‖ ≤ 1-s := by sorry

theorem odd_numerical_of_loewner (hL : NormalizedLoewnerRepresentation) {g : ℂ → ℂ}
    (hg : Sigma g) (m : ℕ) :
    ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ) ∧
      (‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ) → ‖forwardCoeff g 1‖=1) := by sorry

end Springer
end
