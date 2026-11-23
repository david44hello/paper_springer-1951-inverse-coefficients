import Challenge.FunctionalDerivative

/- Frozen input: Springer/ReciprocalResidue.lean -/
noncomputable section
open PowerSeries Finset
namespace Springer

def reciprocalDenom (H : PowerSeries ℂ) (a : ℂ) : PowerSeries ℂ := 1-C a*X-X^2*H

def reciprocalDirection (H : PowerSeries ℂ) (a : ℂ) := (reciprocalDenom H a)⁻¹

end Springer
end
