import Challenge.Basic

/- Frozen input: Springer/ResidueFunctional.lean -/
noncomputable section
open Finset PowerSeries
namespace Springer

def shiftedResidue {R : Type*} [CommSemiring R] (H : PowerSeries R) (j l : ℕ) : R :=
  if l≤j then (H^(l+1)).coeff (j-l) else 0

def functionalCoeff {R : Type*} [Field R] (H : PowerSeries R) (u : R) (m : ℕ) :=
  ∑ j ∈ range (m+1), u^j*(1-u)^(m-j)/(j.factorial*((m-j+1).factorial:R))*shiftedResidue H j (m-j)

end Springer
end
