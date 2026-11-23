import Challenge.DiskConsequences

/- Frozen input: Springer/AreaRigidity.lean -/
noncomputable section
open Set Filter Complex Finset
open scoped Topology
namespace Springer

def AreaBound (g : ℂ → ℂ) : Prop :=
  ∃ A : ℝ, A ≤ 1 ∧ HasSum (fun k : ℕ => (k:ℝ)*‖forwardCoeff g k‖^2) A

end Springer
end
