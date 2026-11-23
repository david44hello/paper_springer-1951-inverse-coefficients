import Challenge.ActualCoefficientFlow
import Challenge.OddConclusions

/- Frozen input: Springer/OddTheorems.lean -/
noncomputable section
open Set Complex
namespace Springer

theorem odd_theorem_of_loewner_and_area (hL : NormalizedLoewnerRepresentation)
    {g : ℂ → ℂ} (hg : Sigma g) (ha : AreaBound g) :
    (∀ m, ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ)) ∧
    ((∃ m, ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ)) ↔
      ∃ θ : ℝ, EqOn g (slitMap (Complex.exp ((θ:ℂ)*I))) exterior) ∧
    (∀ θ : ℝ, EqOn g (slitMap (Complex.exp ((θ:ℂ)*I))) exterior →
      ∀ m, ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ)) := by sorry

theorem omitted_disk_improvement_of_loewner (hL : NormalizedLoewnerRepresentation)
    {g : ℂ → ℂ} (hg : Sigma g) (w : ℂ) {ρ : ℝ} (hr : 0<ρ) (hr1 : ρ<1)
    (hom : ∀ z∈exterior, ρ<‖g z-w‖) (m : ℕ) :
    ‖inverseCoeff g (2*m+1)+(diskWeight m:ℂ)*(forwardCoeff g 1)^(m+1)‖ ≤
      (1-(1/2:ℝ)^m)*(catalan m:ℝ) -
      ((∑ k∈Finset.range (m+1), ((2*m).choose (2*k):ℝ)*(catalan (m-k):ℝ)*
        ‖w‖^(2*k)*ρ^(2*(m-k+1))) - diskWeight m*ρ^(2*m+2)) := by sorry

end Springer
end
