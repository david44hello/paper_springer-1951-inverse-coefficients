-- Review of the main statements for Springer's inverse-coefficient conjecture.
-- Version 1.00. Independent type checks for the three printed main theorems.
import Springer.OddTheorems
import Springer.EvenTheorem

open Springer Set Complex

namespace SpringerReview

noncomputable section

private abbrev agreesWithSlit (g : ℂ → ℂ) (θ : ℝ) :=
  EqOn g (fun z => z + Complex.exp ((θ : ℂ) * I) / z) {z : ℂ | 1 < ‖z‖}

-- 1.2. Equality at some odd order identifies the map on its domain.
-- Each rotated slit map attains equality at every odd order.
#check (@odd_theorem_of_loewner_and_area :
  NormalizedLoewnerRepresentation → ∀ {g : ℂ → ℂ}, Sigma g →
  (∃ A : ℝ, A ≤ 1 ∧ HasSum (fun k : ℕ => (k : ℝ) * ‖forwardCoeff g k‖ ^ 2) A) →
  (∀ m : ℕ, ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m : ℝ)) ∧
  ((∃ m : ℕ, ‖inverseCoeff g (2*m+1)‖ = (catalan m : ℝ)) ↔
    ∃ θ : ℝ, agreesWithSlit g θ) ∧
  (∀ θ : ℝ, agreesWithSlit g θ → ∀ m : ℕ, ‖inverseCoeff g (2*m+1)‖ = (catalan m : ℝ)))
#check (catalan_factorial_real : ∀ m : ℕ,
  (catalan m : ℝ) = ((2*m).factorial : ℝ) / ((m.factorial : ℝ) * ((m+1).factorial : ℝ)))

-- 1.3. Expand the disk weight so that the sign, center and radius are checked.
private abbrev weight (m : ℕ) : ℝ := (1/2 : ℝ)^m * (catalan m : ℝ)
#check (@disk_theorem_of_loewner :
  NormalizedLoewnerRepresentation → ∀ {g : ℂ → ℂ}, Sigma g → ∀ m : ℕ,
  ‖inverseCoeff g (2*m+1) + (weight m : ℂ) * (forwardCoeff g 1)^(m+1)‖ ≤
      (1-(1/2 : ℝ)^m) * (catalan m : ℝ) ∧
  ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m : ℝ) - weight m * (1-‖forwardCoeff g 1‖^(m+1)))

-- 1.4. Check the existential conclusion and the stronger printed witness bounds.
#check (@even_order_counterexamples : ∀ {n : ℕ}, Even n → 4 ≤ n →
  ∃ g : ℂ → ℂ, Sigma g ∧ sigmaBound n < ‖inverseCoeff g n‖)
#check (even_four :
  Sigma (fun z : ℂ => z - 3/(4*z-2)) ∧
  arcMap '' exterior = {w : ℂ | ‖w-(3:ℂ)/2‖=2 ∧ w.re ≤ (1:ℝ)/2}ᶜ ∧
  ‖inverseCoeff arcMap 4‖ = (3:ℝ)/4 ∧ sigmaBound 4 = (2:ℝ)/5 ∧
  sigmaBound 4 < ‖inverseCoeff arcMap 4‖)
#check (@even_family : ∀ {m : ℕ}, 3 ≤ m →
  Sigma (fun z : ℂ => z+(1-1/(m:ℂ))/z+(1/(2*(m:ℂ)))/z^2) ∧
  ‖inverseCoeff (trinomialMap m) (2*m)‖ ≥
    (1/(4*(m:ℝ)))*((2*m).choose m:ℝ)*(1-1/(m:ℝ))^(m-1) ∧
  sigmaBound (2*m) < (1/(4*(m:ℝ)))*((2*m).choose m:ℝ)*(1-1/(m:ℝ))^(m-1))

#print axioms odd_theorem_of_loewner_and_area
#print axioms catalan_factorial_real
#print axioms disk_theorem_of_loewner
#print axioms actual_coefficient_flow
#print axioms even_order_counterexamples
#print axioms even_four
#print axioms even_family
#print axioms omitted_disk_improvement_of_loewner

end

end SpringerReview
