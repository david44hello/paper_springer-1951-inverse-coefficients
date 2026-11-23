import Challenge.ActualCoefficientFlow

/- Frozen input: Springer/FlowExterior.lean -/
noncomputable section
open Set Filter Function Complex Metric Finset MeasureTheory
open scoped Topology NNReal
namespace Springer

def exteriorTrajectory (g : ℂ → ℂ) (φ : ℝ → ℂ → ℂ) (t : ℝ) (w : ℂ) :=
  w+timeRemainder g φ t w⁻¹

theorem actual_exterior_family {g : ℂ → ℂ} (hg : Sigma g) {w₀ : ℂ} {ρ : ℝ}
    (hr : 0<ρ) (hr1 : ρ<1) (hom : ∀ z∈exterior, ρ<‖g z-w₀‖) {p φ : ℝ → ℂ → ℂ}
    (h : NormalizedLoewnerData (flowDiskMap g w₀ ρ) ρ p φ) :
    ∃ K : ℝ, 0<K ∧
    (∀ t∈Icc (ρ^2) 1, AnalyticOnNhd ℂ (exteriorTrajectory g φ t) {w | K<‖w‖}) ∧
    (∀ t∈Icc (ρ^2) 1, ∀ w : ℂ, K<‖w‖ →
      exteriorTrajectory g φ t w = (Real.sqrt t:ℂ)/φ (elapsed t) (invFunOn g exterior w)⁻¹ ∧
      HasSum (fun k : ℕ => (storedRemainder (timeRemainder g φ t)).coeff k*(w⁻¹)^(k+1))
        (w+timeRemainder g φ t 0-exteriorTrajectory g φ t w)) ∧
    (∀ w : ℂ, K<‖w‖ → exteriorTrajectory g φ (ρ^2) w=w-w₀ ∧
      exteriorTrajectory g φ 1 w=invFunOn g exterior w) := by sorry

end Springer
end
