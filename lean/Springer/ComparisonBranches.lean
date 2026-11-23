import Springer.ComparisonInduction
import Springer.RadialTransport

noncomputable section
open Set Finset Complex MeasureTheory PowerSeries
namespace Springer

/-- The endpoint contribution of a single real sign in the comparison. -/
def comparisonBranch (u t r a : ℝ) (n : ℕ) :=
  forcingPolynomial (n+1) ((r+u*a)^2) +
    ∫ v : ℝ in 0..u, (1-v)*comparisonPolynomial v t n ((r+(u-v)*a)^2)

theorem expShift_ofReal (r : ℝ) (F : ℕ → ℝ) (m : ℕ) :
    expShift (r:ℂ) (fun j => (F j:ℂ)) m=((expShift r F m : ℝ):ℂ) := by
  simp [expShift]

theorem comparisonBranch_complex (u t r a : ℝ) (n : ℕ) :
    expShift (r:ℂ) (reciprocalKernel (modelProfile 1 (t:ℂ)) (a:ℂ) u) (2*n+2) -
      reciprocalKernel (modelProfile (1/2) (t:ℂ)) 0 u (2*n+2) =
        (comparisonBranch u t r a n:ℂ) := by
  let U := modelProfile 1 (t:ℂ)
  let V := modelProfile (1/2) (t:ℂ)
  rw [shifted_reciprocalKernel,reciprocalKernel]
  simp only [mul_zero,zero_pow (by omega : 2*n+2≠0),zero_div,zero_add,convolution_zero]
  unfold comparisonBranch forcingPolynomial
  rw [Complex.ofReal_add,←intervalIntegral.integral_ofReal,add_sub_assoc,←intervalIntegral.integral_sub]
  · congr 1
    · push_cast
      rw [←pow_mul,show 2*(n+1)=2*n+2 by omega]
    · apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      rw [comparisonPolynomial_sq]
      push_cast
      change (1-(v:ℂ))*expShift ((r:ℂ)+((u:ℂ)-v)*a) (modelU (v:ℂ) (t:ℂ)) (2*n) -
        (1-(v:ℂ))*modelV (v:ℂ) (t:ℂ) (2*n)=_
      rw [show modelU (v:ℂ) (t:ℂ) = fun j => ((modelU v t j:ℝ):ℂ) from funext (modelU_ofReal v t),
        modelV_ofReal,show (r:ℂ)+((u:ℂ)-v)*a=↑(r+(u-v)*a) by push_cast; rfl,expShift_ofReal]
      push_cast
      ring
  all_goals
    apply Continuous.intervalIntegrable
    simp only [exponentialConvolution,functionalCoeff]
    fun_prop

theorem signAverage_branches (μ : Measure Circle) (P c : ℂ) (u t : ℝ) (n : ℕ) :
    let Z := c-(u:ℂ)*P
    let r := ‖Z‖
    let ω := chordDirection Z (∫ ξ : Circle, (ξ:ℂ) ∂μ)
    signAverage ω (comparisonBranch u t r (Real.sqrt t) n)
      (comparisonBranch u t r (-Real.sqrt t) n) = comparisonUpperSlope μ P c u t n := by
  intro Z r ω
  let E := fun (a v : ℝ) => (1-v)*comparisonPolynomial v t n ((r+(u-v)*a)^2)
  have hi (a : ℝ) : IntervalIntegrable (E a) volume 0 u := by
    apply Continuous.intervalIntegrable
    unfold E comparisonPolynomial modelU modelV functionalCoeff
    fun_prop
  let p := (1+ω)/2
  let q := (1-ω)/2
  have hsum : p*(∫ v : ℝ in 0..u, E (Real.sqrt t) v) + q*(∫ v : ℝ in 0..u, E (-Real.sqrt t) v) =
      ∫ v : ℝ in 0..u, (1-v)*chordAverage μ Z ((u-v)*Real.sqrt t) (comparisonPolynomial v t n) := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul,
      ←intervalIntegral.integral_add ((hi _).const_mul _) ((hi _).const_mul _)]
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp [E,chordAverage,signAverage,p,q,ω,r]
    simp only [mul_neg,←sub_eq_add_neg]
    ring
  unfold comparisonBranch signAverage comparisonUpperSlope
  dsimp only
  simp only [mul_add]
  change p*_+p*(∫ v : ℝ in 0..u, E (Real.sqrt t) v)+
    (q*_+q*(∫ v : ℝ in 0..u, E (-Real.sqrt t) v))=_
  rw [add_add_add_comm,hsum]
  simp only [chordAverage,signAverage,r,p,q,ω,Z,mul_neg,←sub_eq_add_neg]

end Springer
