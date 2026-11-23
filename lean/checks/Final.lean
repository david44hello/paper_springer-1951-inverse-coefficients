import Springer
open Springer Set Complex MeasureTheory
noncomputable section

example (loewner : NormalizedLoewnerRepresentation) {g : ℂ → ℂ} (hg : Sigma g) (m : ℕ) :
    ‖inverseCoeff g (2*m+1) + (1/2:ℂ)^m*(catalan m:ℂ)*(forwardCoeff g 1)^(m+1)‖ ≤
        (1-(1/2:ℝ)^m)*(catalan m:ℝ) ∧
      ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ) -
        (1/2:ℝ)^m*(catalan m:ℝ)*(1-‖forwardCoeff g 1‖^(m+1)) := by
  simpa [DiskBound, diskWeight] using disk_theorem_of_loewner loewner hg m

example (loewner : NormalizedLoewnerRepresentation) {g : ℂ → ℂ} (hg : Sigma g) (area : AreaBound g) :
    (∀ m, ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ)) ∧
    ((∃ m, ‖inverseCoeff g (2*m+1)‖ = (catalan m:ℝ)) ↔
      ∃ θ : ℝ, EqOn g (fun z => z+Complex.exp ((θ:ℂ)*I)/z) exterior) ∧
    (∀ θ : ℝ, EqOn g (fun z => z+Complex.exp ((θ:ℂ)*I)/z) exterior →
      ∀ m, ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ)) :=
  odd_theorem_of_loewner_and_area loewner hg area

example (u τ : ℝ) (m : ℕ) :
    modelU (R:=ℂ) u τ m = Complex.ofReal (modelU (R:=ℝ) u τ m) := modelU_ofReal u τ m
example (u τ : ℝ) (m : ℕ) :
    modelV (R:=ℂ) u τ m = Complex.ofReal (modelV (R:=ℝ) u τ m) := modelV_ofReal u τ m

#check actual_coefficient_flow
#check actual_exterior_family
#check disk_theorem_of_loewner
#check odd_theorem_of_loewner_and_area
#check omitted_disk_improvement_of_loewner
#print axioms actual_coefficient_flow
#print axioms actual_exterior_family
#print axioms disk_theorem_of_loewner
#print axioms odd_theorem_of_loewner_and_area
#print axioms omitted_disk_improvement_of_loewner
#print axioms comparison_of_flow
#print axioms chord_integral
#print axioms modelU_ofReal
#print axioms modelV_ofReal
#print axioms herglotz_representation
#print axioms loewner_trajectory_unique
#print axioms inverse_germ

example (loewner : NormalizedLoewnerRepresentation) {g : ℂ → ℂ} (hg : Sigma g) (m : ℕ) :
    ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ) ∧
      (‖inverseCoeff g (2*m+1)‖ = (catalan m:ℝ) → ‖forwardCoeff g 1‖ = 1) :=
  odd_numerical_of_loewner loewner hg m

#check odd_numerical_of_loewner
#print axioms odd_numerical_of_loewner
#print axioms CoefficientFlow.first_norm_le
#print axioms even_order_counterexamples
