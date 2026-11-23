import Challenge.ReciprocalResidue
import Challenge.Basic

/- Frozen input: Springer/VelocityCoefficients.lean -/
noncomputable section
open Finset PowerSeries Set Filter Complex
open scoped Topology
namespace Springer

def storedRemainder (R : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => -taylorCoeff R (k+1))

end Springer
end
