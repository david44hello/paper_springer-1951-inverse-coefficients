import Challenge.HerglotzCoefficients

/- Frozen input: Springer/HerglotzFamily.lean -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Springer

def HerglotzRepresentation : Prop :=
  ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f disc → f 0=1 → (∀ z∈disc, 0<(f z).re) →
    ∃ ν : ProbabilityMeasure Circle, EqOn f (herglotzTransform (ν : Measure Circle)) disc

end Springer
end
