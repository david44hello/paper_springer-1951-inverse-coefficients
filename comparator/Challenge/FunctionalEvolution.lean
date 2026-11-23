import Challenge.ReciprocalResidue
import Challenge.ModelSeries
import Challenge.FunctionalDerivative

/- Frozen input: Springer/FunctionalEvolution.lean -/
noncomputable section
open PowerSeries Finset MeasureTheory
namespace Springer

def averagedDirection (H : PowerSeries ℂ) (a : Circle → ℂ) (μ : Measure Circle) : PowerSeries ℂ :=
  PowerSeries.mk fun j => ∫ ξ, (ξ:ℂ)^2*(reciprocalDirection H (a ξ)).coeff j ∂μ

end Springer
end
