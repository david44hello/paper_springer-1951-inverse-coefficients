import Challenge.FlowGeometry
import Challenge.OddConclusions

/- Frozen input: Springer/ActualCoefficientFlow.lean -/
noncomputable section
open Complex MeasureTheory Set Metric Filter
open scoped Real NNReal Topology
namespace Springer

theorem actual_coefficient_flow {g : ℂ → ℂ} (hg : Sigma g) {ρ : ℝ} (hr : 0<ρ) (hr1 : ρ<1)
    {w : ℂ} (hom : ∀ z∈exterior, ρ<‖g z-w‖) {p φ : ℝ → ℂ → ℂ}
    (h : NormalizedLoewnerData (flowDiskMap g w ρ) ρ p φ) :
    ∃ μ : ℝ → Measure Circle,
      let R := timeRemainder g φ
      CoefficientFlow g (ρ^2) (fun t => storedRemainder (R t)) (fun t => R t 0) μ ∧
      R (ρ^2) 0 = -w ∧
      (∀ f : C(Circle,ℂ), Measurable (fun t => ∫ ξ, f ξ ∂μ t)) := by sorry

theorem disk_theorem_of_loewner (hL : NormalizedLoewnerRepresentation)
    {g : ℂ → ℂ} (hg : Sigma g) (m : ℕ) :
    DiskBound g m ∧ ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ) -
      diskWeight m*(1-‖forwardCoeff g 1‖^(m+1)) := by sorry

end Springer
end
