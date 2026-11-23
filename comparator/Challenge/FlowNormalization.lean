import Challenge.Basic

/- Frozen input: Springer/FlowNormalization.lean -/
noncomputable section
open Set Complex Function
namespace Springer

def flowDiskMap (g : ℂ → ℂ) (w : ℂ) (ρ : ℝ) (z : ℂ) :=
  (ρ:ℂ)*z / (profile g z-z*w)

end Springer
end
