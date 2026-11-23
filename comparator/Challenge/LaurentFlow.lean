import Challenge.TimeChange
import Challenge.Basic

/- Frozen input: Springer/LaurentFlow.lean -/
noncomputable section
open Complex Set Filter Function
open scoped Topology
namespace Springer

def inverseCoordinate (g : ℂ → ℂ) (y : ℂ) := y / inverseProfile g y

def flowLaurentProfile (g φ : ℂ → ℂ) (b : ℂ) (y : ℂ) :=
  b*inverseProfile g y / dslope φ 0 (inverseCoordinate g y)

def flowRemainder (g φ : ℂ → ℂ) (b : ℂ) := dslope (flowLaurentProfile g φ b) 0

end Springer
end
