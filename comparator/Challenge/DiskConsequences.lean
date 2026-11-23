import Challenge.Basic
import Challenge.Slit

/- Frozen input: Springer/DiskConsequences.lean -/
noncomputable section
open Set Complex Filter Finset
open scoped Topology
namespace Springer

def diskWeight (m : ℕ) : ℝ := (1/2:ℝ)^m * (catalan m:ℝ)

def DiskBound (g : ℂ → ℂ) (m : ℕ) : Prop :=
  ‖inverseCoeff g (2*m+1) + (diskWeight m:ℂ)*(forwardCoeff g 1)^(m+1)‖ ≤
    (1-(1/2:ℝ)^m)*(catalan m:ℝ)

end Springer
end
