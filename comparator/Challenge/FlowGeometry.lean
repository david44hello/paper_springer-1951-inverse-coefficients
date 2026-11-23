import Challenge.LoewnerInput
import Challenge.Comparison
import Challenge.TimeChange
import Challenge.HerglotzCoefficients
import Challenge.LaurentFlow
import Challenge.VelocityCoefficients
import Mathlib
import Challenge.Basic
import Challenge.FunctionalEvolution

/- Frozen input: Springer/FlowGeometry.lean -/
noncomputable section
open Set Complex Filter Function MeasureTheory Metric
open scoped Topology
namespace Springer

def timeRemainder (g : ℂ → ℂ) (φ : ℝ → ℂ → ℂ) (t : ℝ) :=
  flowRemainder g (φ (elapsed t)) (Real.sqrt t)

end Springer
end
