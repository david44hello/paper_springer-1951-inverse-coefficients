import Challenge.ArcCoefficient
import Challenge.Basic

/- Frozen input: Springer/EvenTheorem.lean -/
noncomputable section
open Set
namespace Springer

theorem even_family {m : ℕ} (hm : 3 ≤ m) :
    Sigma (trinomialMap m) ∧
    ‖inverseCoeff (trinomialMap m) (2*m)‖ ≥ (1/(4*(m:ℝ)))*((2*m).choose m:ℝ)*(1-1/(m:ℝ))^(m-1) ∧
    sigmaBound (2*m)<(1/(4*(m:ℝ)))*((2*m).choose m:ℝ)*(1-1/(m:ℝ))^(m-1) := by sorry

theorem even_order_counterexamples {n : ℕ} (hn : Even n) (h4 : 4≤n) :
    ∃ g : ℂ → ℂ, Sigma g ∧ sigmaBound n<‖inverseCoeff g n‖ := by sorry

end Springer
end
