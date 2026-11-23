import Challenge.ModelSeries
import Challenge.Chord

/- Frozen input: Springer/Comparison.lean -/
noncomputable section
open MeasureTheory Set Finset Complex
namespace Springer

def expShift {R : Type*} [Field R] (c : R) (F : ℕ → R) (m : ℕ) : R :=
  ∑ k ∈ range (m+1), c^k / k.factorial * F (m-k)

def comparisonPolynomial (u t : ℝ) (n : ℕ) (q : ℝ) :=
  (∑ k ∈ range (n+1), (modelU u t (2*(n-k)) / (2*k).factorial) * q^k) -
    modelV u t (2*n)

end Springer
end
