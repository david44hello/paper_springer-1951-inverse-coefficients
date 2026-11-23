import Challenge.ComparisonStep
import Challenge.DiskConsequences
import Challenge.Comparison
import Challenge.ReciprocalResidue
import Challenge.ModelSeries
import Challenge.FunctionalDerivative
import Challenge.FunctionalRegularity
import Challenge.FunctionalEvolution

/- Frozen input: Springer/ComparisonFromFlow.lean -/
noncomputable section
open Set Finset Complex MeasureTheory
namespace Springer

theorem comparison_of_flow {s : ℝ} (hs : 0 < s) (H : ℝ → PowerSeries ℂ) (P : ℝ → ℂ)
    (μ : ℝ → Measure Circle) [∀ t, IsProbabilityMeasure (μ t)] (hinit : H s=0)
    (hH : ∀ j, AbsolutelyContinuousOnInterval (fun t => (H t).coeff j) s 1)
    (hP : AbsolutelyContinuousOnInterval P s 1)
    (hd : ∀ᵐ t ∂volume.restrict (Set.Icc s 1),
      HasDerivAt P (-(∫ ξ : Circle, (ξ:ℂ) ∂μ t)/(Real.sqrt t:ℂ)) t ∧
      CoeffDerivAt H (averagedDirection (H t) (fun ξ : Circle => (Real.sqrt t:ℂ)*ξ-P t) (μ t)) t) :
    ∀ n t, t∈Set.Icc s 1 → ∀ u, u∈Set.Icc 0 1 → ∀ c : ℂ,
      ‖comparisonValue (H t) u c n‖ ≤ comparisonBound (P t) u t c n := by sorry

end Springer
end
