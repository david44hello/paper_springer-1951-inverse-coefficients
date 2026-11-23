import Challenge.Comparison

/- Frozen input: Springer/ComparisonStep.lean -/
noncomputable section
open MeasureTheory Set Finset Complex
open scoped ComplexConjugate
namespace Springer

def comparisonValue (H : PowerSeries ℂ) (u : ℝ) (c : ℂ) (n : ℕ) :=
  expShift c (functionalCoeff H (u:ℂ)) (2*n) - modelV (u:ℂ) (H.coeff 0) (2*n)

def comparisonBound (P : ℂ) (u t : ℝ) (c : ℂ) (n : ℕ) :=
  comparisonPolynomial u t n (‖c-(u:ℂ)*P‖^2)

end Springer
end
