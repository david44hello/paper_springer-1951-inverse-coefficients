import Challenge.ComparisonFromFlow
import Challenge.AreaRigidity

/- Frozen input: Springer/OddConclusions.lean -/
noncomputable section
open Set MeasureTheory Complex
namespace Springer

structure CoefficientFlow (g : ℂ → ℂ) (s : ℝ) (H : ℝ → PowerSeries ℂ) (P : ℝ → ℂ)
    (μ : ℝ → Measure Circle) : Prop where
  prob : ∀ t, IsProbabilityMeasure (μ t)
  initial : H s=0
  terminal : ∀ k, (H 1).coeff k = -inverseCoeff g (k+1)
  center : P 1=0
  coeffAC : ∀ j, AbsolutelyContinuousOnInterval (fun t => (H t).coeff j) s 1
  centerAC : AbsolutelyContinuousOnInterval P s 1
  ode : ∀ᵐ t ∂volume.restrict (Icc s 1),
    HasDerivAt P (-(∫ ξ : Circle, (ξ:ℂ) ∂μ t)/(Real.sqrt t:ℂ)) t ∧
    CoeffDerivAt H (averagedDirection (H t) (fun ξ : Circle => (Real.sqrt t:ℂ)*ξ-P t) (μ t)) t

theorem catalan_factorial_real (m : ℕ) :
    (catalan m:ℝ) = ((2*m).factorial:ℝ)/((m.factorial:ℝ)*((m+1).factorial:ℝ)) := by sorry

end Springer
end
