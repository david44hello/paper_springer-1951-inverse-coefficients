import Challenge.Basic

/- Frozen input: Springer/Slit.lean -/
noncomputable section
open Set Function Filter Finset Polynomial
open scoped Topology Polynomial
namespace Springer

def slitMap (b z : ℂ) := z+b/z

end Springer
end
