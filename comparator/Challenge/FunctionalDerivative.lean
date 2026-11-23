import Challenge.ResidueFunctional

/- Frozen input: Springer/FunctionalDerivative.lean -/
noncomputable section
open Finset PowerSeries Filter
open scoped Topology
namespace Springer

def CoeffDerivAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (H : 𝕜 → PowerSeries ℂ) (L : PowerSeries ℂ) (t : 𝕜) : Prop :=
  ∀ n, HasDerivAt (fun s => (H s).coeff n) (L.coeff n) t

end Springer
end
