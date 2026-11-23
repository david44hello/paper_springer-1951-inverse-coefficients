import Challenge.Basic

/- Frozen input: Springer/ArcCoefficient.lean -/
noncomputable section
open Set Filter Function Complex Finset
open scoped Topology
namespace Springer

theorem even_four :
    Sigma arcMap ∧ arcMap '' exterior=circularArcᶜ ∧
      ‖inverseCoeff arcMap 4‖=3/4 ∧ sigmaBound 4=2/5 ∧ sigmaBound 4<‖inverseCoeff arcMap 4‖ := by sorry

end Springer
end
