import Springer.ComparisonFromFlow
import Springer.AreaRigidity

noncomputable section
open Set MeasureTheory Complex
namespace Springer

/-- The coefficient form used at the end of Lemma 3.1. These are its scalar
endpoint, continuity and differential conclusions. -/
structure CoefficientFlow (g : ℂ → ℂ) (s : ℝ) (H : ℝ → PowerSeries ℂ) (P : ℝ → ℂ)
    (μ : ℝ → Measure Circle) : Prop where
  prob : ∀ t, IsProbabilityMeasure (μ t)
  initial : H s=0
  terminal : ∀ k, (H 1).coeff k = -inverseCoeff g (k+1)
  center : P 1=0
  coeffAC : ∀ j, AbsolutelyContinuousOnInterval (fun t => (H t).coeff j) s 1
  centerAC : AbsolutelyContinuousOnInterval P s 1
  ode : ∀ᵐ t ∂volume.restrict (Icc s 1),
    HasDerivAt P (-(∫ ξ : Circle, (ξ:ℂ) ∂μ t)/(Real.sqrt t:ℂ)) t ∧
    CoeffDerivAt H (averagedDirection (H t) (fun ξ : Circle => (Real.sqrt t:ℂ)*ξ-P t) (μ t)) t

theorem CoefficientFlow.diskBound {g : ℂ → ℂ} (hg : Sigma g) {s : ℝ} (hs : 0<s) (hs1 : s≤1)
    {H P μ} (h : CoefficientFlow g s H P μ) (m : ℕ) : DiskBound g m := by
  letI : ∀ t, IsProbabilityMeasure (μ t) := h.prob
  have comp := comparison_of_flow hs H P μ h.initial h.coeffAC h.centerAC h.ode m 1 ⟨hs1,le_rfl⟩
    1 ⟨zero_le_one,le_rfl⟩ 0
  rw [h.center] at comp
  apply diskBound_of_comparison_endpoint h.terminal _ comp
  rw [h.terminal,inverse_first_eq_neg_forward hg,neg_neg]

/-- From the omitted-disk coefficient flow to the inequality and its triangle
consequence for every map, including index zero. -/
theorem disk_theorem_of_coefficient_flow
    (hFlow : ∀ g : ℂ → ℂ, Sigma g → OmitsDisk g →
      ∃ s H P μ, 0<s ∧ s≤1 ∧ CoefficientFlow g s H P μ) {g : ℂ → ℂ} (hg : Sigma g) (m : ℕ) :
    DiskBound g m ∧ ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ) -
      diskWeight m*(1-‖forwardCoeff g 1‖^(m+1)) := by
  have disk : DiskBound g m := diskBound_of_omitted_disk_bound (fun f hf hom => by
    obtain ⟨s,H,P,μ,hs,hs1,h⟩ := hFlow f hf hom
    exact h.diskBound hf hs hs1 m) hg
  exact ⟨disk,disk.refined⟩

theorem odd_theorem_of_area_and_disk {g : ℂ → ℂ} (hg : Sigma g) (ha : AreaBound g)
    (hd : ∀ m, DiskBound g m) :
    (∀ m, ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ)) ∧
    ((∃ m, ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ)) ↔
      ∃ θ : ℝ, EqOn g (slitMap (Complex.exp ((θ:ℂ)*I))) exterior) ∧
    (∀ θ : ℝ, EqOn g (slitMap (Complex.exp ((θ:ℂ)*I))) exterior →
      ∀ m, ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ)) := by
  refine ⟨fun m => (hd m).odd ha.first_le_one,⟨?_,?_⟩,odd_equality_of_eqOn_rotated_slit hg⟩
  · rintro ⟨m,hm⟩
    exact odd_equality_slit_of_area_and_disk hg ha (hd m) hm
  · rintro ⟨θ,hθ⟩
    exact ⟨0,odd_equality_of_eqOn_rotated_slit hg θ hθ 0⟩

theorem catalan_factorial_real (m : ℕ) :
    (catalan m:ℝ) = ((2*m).factorial:ℝ)/((m.factorial:ℝ)*((m+1).factorial:ℝ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show m≤2*m by omega)
  rw [show 2*m-m=m by omega,←Nat.centralBinom,←succ_mul_catalan_eq_centralBinom] at h
  apply (eq_div_iff (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m)
    (by exact_mod_cast Nat.factorial_ne_zero (m+1)))).mpr
  rw [Nat.factorial_succ,Nat.cast_mul]
  exact_mod_cast (by linear_combination h : catalan m*(m.factorial*((m+1)*m.factorial))=(2*m).factorial)

end Springer
