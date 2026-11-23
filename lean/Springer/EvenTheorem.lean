import Springer.ArcCoefficient
import Springer.TrinomialCoefficient
import Springer.BinomialComparison

noncomputable section
open Set
namespace Springer

/-- Theorem 1.4(b) for each of the stated trinomial maps. -/
theorem even_family {m : ℕ} (hm : 3 ≤ m) :
    Sigma (trinomialMap m) ∧
    ‖inverseCoeff (trinomialMap m) (2*m)‖ ≥ (1/(4*(m:ℝ)))*((2*m).choose m:ℝ)*(1-1/(m:ℝ))^(m-1) ∧
    sigmaBound (2*m)<(1/(4*(m:ℝ)))*((2*m).choose m:ℝ)*(1-1/(m:ℝ))^(m-1) := by
  have eq : (1/(4*(m:ℝ)))*((2*m).choose m:ℝ)=(m.centralBinom:ℝ)/(4*m) := by rw [Nat.centralBinom]; ring
  rw [eq]
  exact ⟨trinomial_sigma hm,even_coefficient_lower hm,even_lower_exceeds_springer hm⟩

theorem eighth_order_example :
    sigmaBound 8=130/81 ∧ (945/512:ℝ)≤‖inverseCoeff (trinomialMap 4) 8‖ ∧ (130/81:ℝ)<945/512 := by
  constructor
  · norm_num [sigmaBound,realBinom,Finset.prod_range_succ]
  · have H := even_coefficient_lower (m:=4) (by decide)
    change (70:ℝ)/(4*4)*(1-1/4)^3≤_ at H
    exact ⟨by convert H using 1 <;> norm_num,by norm_num⟩

/-- Springer's conjectured upper bound fails at every even order n ≥ 4. -/
theorem even_order_counterexamples {n : ℕ} (hn : Even n) (h4 : 4≤n) :
    ∃ g : ℂ → ℂ, Sigma g ∧ sigmaBound n<‖inverseCoeff g n‖ := by
  obtain ⟨m,rfl⟩ := hn
  rw [←two_mul]
  by_cases hm : m=2
  · subst m; exact ⟨_,even_four.1,even_four.2.2.2.2⟩
  · obtain ⟨hS,hlo,hσ⟩ := even_family (m:=m) (by omega)
    exact ⟨_,hS,hσ.trans_le hlo⟩

end Springer
