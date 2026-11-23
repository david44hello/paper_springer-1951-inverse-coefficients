import Springer.OddConclusions
noncomputable section
open Finset Set MeasureTheory
namespace Springer

/-- The factorial multiple of the model coefficient at the initial center. -/
theorem initial_comparison_mass (w : ℂ) (ρ : ℝ) (m : ℕ) :
    ((2*m).factorial:ℝ)*comparisonBound (-w) 1 (ρ^2) 0 m =
      (∑ k∈range (m+1), ((2*m).choose (2*k):ℝ)*(catalan (m-k):ℝ)*
        ‖w‖^(2*k)*ρ^(2*(m-k+1))) - diskWeight m*ρ^(2*m+2) := by
  unfold comparisonBound comparisonPolynomial diskWeight
  simp only [Complex.ofReal_one,one_mul,zero_sub,neg_neg,mul_sub,mul_sum]
  simp_rw [(model_endpoint (ρ^2) _).1,(model_endpoint (ρ^2) _).2]
  congr 1
  · apply sum_congr rfl
    intro k hk
    have hkm := Nat.le_of_lt_succ (mem_range.mp hk)
    have eq := Nat.choose_mul_factorial_mul_factorial (show 2*k≤2*m by omega)
    rw [show 2*m-2*k=2*(m-k) by omega] at eq
    have h : ((2*m).choose (2*k):ℝ)*((2*k).factorial:ℝ)*((2*(m-k)).factorial:ℝ)=((2*m).factorial:ℝ) := by
      exact_mod_cast eq
    rw [←h,←pow_mul,←pow_mul]
    have h₁ : ((2*k).factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h₂ : ((2*(m-k)).factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp [h₁,h₂]
  · rw [←pow_mul,show 2*(m+1)=2*m+2 by omega]
    have hn : ((2*m).factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp

/-- Remark 7.1 for the original center w and radius ρ of the omitted disk. -/
theorem CoefficientFlow.omitted_disk_improvement {g : ℂ → ℂ} (hg : Sigma g) (w : ℂ) {ρ : ℝ}
    (hr : 0<ρ) (hr1 : ρ<1) {H P μ} (h : CoefficientFlow g (ρ^2) H P μ) (hw : P (ρ^2)= -w) (m : ℕ) :
    ‖inverseCoeff g (2*m+1)+(diskWeight m:ℂ)*(forwardCoeff g 1)^(m+1)‖ ≤
      (1-(1/2:ℝ)^m)*(catalan m:ℝ) -
      ((∑ k∈range (m+1), ((2*m).choose (2*k):ℝ)*(catalan (m-k):ℝ)*
        ‖w‖^(2*k)*ρ^(2*(m-k+1))) - diskWeight m*ρ^(2*m+2)) := by
  letI : ∀ t, IsProbabilityMeasure (μ t) := h.prob
  have hx := comparison_of_flow_retained (sq_pos_of_pos hr) H P μ h.initial h.coeffAC h.centerAC h.ode
    m 1 (show (1:ℝ)∈Icc (ρ^2) 1 from ⟨by nlinarith [sq_nonneg (1-ρ),mul_pos hr (sub_pos.mpr hr1)],le_rfl⟩)
    1 ⟨zero_le_one,le_rfl⟩ 0
  rw [h.center,hw] at hx
  let N : ℝ := (2*m).factorial
  have hN : 0<N := by dsimp [N]; positivity
  have hb : (H 1).coeff 0=forwardCoeff g 1 := by rw [h.terminal,inverse_first_eq_neg_forward hg,neg_neg]
  have hL : comparisonValue (H 1) 1 0 m =
      -(inverseCoeff g (2*m+1)+(diskWeight m:ℂ)*(forwardCoeff g 1)^(m+1))/(N:ℂ) := by
    simp only [comparisonValue, Complex.ofReal_one,expShift_zero,functional_one,hb,
      (model_endpoint (forwardCoeff g 1) m).2,h.terminal]
    unfold diskWeight N
    push_cast
    ring
  have hR : comparisonBound 0 1 1 0 m=((1-(1/2:ℝ)^m)*(catalan m:ℝ))/N := by
    unfold comparisonBound
    rw [comparisonPolynomial_sq]
    simp only [mul_zero,sub_zero,norm_zero,expShift_zero,(model_endpoint (1:ℝ) m).1,
      (model_endpoint (1:ℝ) m).2,one_pow,mul_one,N]
    ring
  rw [hL,hR,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN] at hx
  rw [←initial_comparison_mass]
  have hh := (div_le_iff₀ hN).mp hx
  rw [sub_mul,div_mul_cancel₀ _ hN.ne',mul_comm (comparisonBound _ _ _ _ _)] at hh
  exact hh

end Springer
