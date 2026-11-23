import Springer.ActualCoefficientFlow
import Springer.DiskRemark
noncomputable section
open Set Complex
namespace Springer

/-- Theorem 1.2 under the normalized Loewner existence theorem and the
exterior area bound for the given map. -/
theorem odd_theorem_of_loewner_and_area (hL : NormalizedLoewnerRepresentation)
    {g : ℂ → ℂ} (hg : Sigma g) (ha : AreaBound g) :
    (∀ m, ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ)) ∧
    ((∃ m, ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ)) ↔
      ∃ θ : ℝ, EqOn g (slitMap (Complex.exp ((θ:ℂ)*I))) exterior) ∧
    (∀ θ : ℝ, EqOn g (slitMap (Complex.exp ((θ:ℂ)*I))) exterior →
      ∀ m, ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ)) :=
  odd_theorem_of_area_and_disk hg ha (fun m => (disk_theorem_of_loewner hL hg m).1)

/-- Remark 7.1 for the specified omitted closed disk. -/
theorem omitted_disk_improvement_of_loewner (hL : NormalizedLoewnerRepresentation)
    {g : ℂ → ℂ} (hg : Sigma g) (w : ℂ) {ρ : ℝ} (hr : 0<ρ) (hr1 : ρ<1)
    (hom : ∀ z∈exterior, ρ<‖g z-w‖) (m : ℕ) :
    ‖inverseCoeff g (2*m+1)+(diskWeight m:ℂ)*(forwardCoeff g 1)^(m+1)‖ ≤
      (1-(1/2:ℝ)^m)*(catalan m:ℝ) -
      ((∑ k∈Finset.range (m+1), ((2*m).choose (2*k):ℝ)*(catalan (m-k):ℝ)*
        ‖w‖^(2*k)*ρ^(2*(m-k+1))) - diskWeight m*ρ^(2*m+2)) := by
  obtain ⟨p,φ,hφ⟩ := normalizedLoewner_of_omitted_disk hL hg w hr hr1 hom
  obtain ⟨μ,hflow,hcenter,_⟩ := actual_coefficient_flow hg hr hr1 hom hφ
  exact hflow.omitted_disk_improvement hg w hr hr1 hcenter m

end Springer
