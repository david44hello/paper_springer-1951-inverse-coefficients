import Mathlib

/- Frozen input: Springer/Chord.lean -/
noncomputable section
open Set Complex MeasureTheory
open scoped ComplexConjugate
namespace Springer

def chordDirection (Z z : ℂ) : ℝ := (conj Z * z).re / ‖Z‖

theorem chord_integral (μ : Measure Circle) [IsProbabilityMeasure μ]
    {Φ : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) Φ) (Z : ℂ) {β : ℝ} (hβ : 0≤β) :
    (∫ ξ : Circle, Φ (‖Z+(β:ℂ)*ξ‖^2) ∂μ) ≤
      (1+chordDirection Z (∫ ξ : Circle, (ξ:ℂ) ∂μ))/2*Φ ((‖Z‖+β)^2) +
      (1-chordDirection Z (∫ ξ : Circle, (ξ:ℂ) ∂μ))/2*Φ ((‖Z‖-β)^2) := by sorry

end Springer
end
