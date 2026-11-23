import Challenge.Basic

/- Frozen input: Springer/HerglotzCoefficients.lean -/
noncomputable section
open Set Filter MeasureTheory Finset
open scoped Topology
namespace Springer

def herglotzTransform (μ : Measure Circle) (z : ℂ) := ∫ ξ, (1+(ξ:ℂ)*z)/(1-(ξ:ℂ)*z) ∂μ

end Springer
end
