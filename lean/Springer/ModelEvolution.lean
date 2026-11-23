import Springer.ReciprocalResidue
import Springer.ModelDerivative
import Springer.ShiftResidue

noncomputable section
open PowerSeries Finset
namespace Springer

/-- Degree m of the coefficientwise expression on the right of Lemma 4.3. -/
def reciprocalKernel (H : PowerSeries ℂ) (a : ℂ) (u : ℝ) : ℕ → ℂ
  | 0 => 1
  | 1 => (u:ℂ)*a
  | m+2 => ((u:ℂ)*a)^(m+2)/(m+2).factorial +
      ∫ v : ℝ in 0..u, (1-(v:ℂ))*exponentialConvolution H (((u:ℂ)-v)*a) v m

theorem kernel_eq_variation (H : PowerSeries ℂ) (a : ℂ) (u : ℝ) (m : ℕ) :
    reciprocalKernel H a u m=firstVariation H (reciprocalDirection H a) u m := by
  cases m with
  | zero => exact (reciprocal_degree_zero H a u).symm
  | succ n =>
    cases n with
    | zero => exact (reciprocal_degree_one H a u).symm
    | succ k => exact (reciprocal_integral H a u k).symm

theorem modelV_hasDeriv (u : ℝ) (τ : ℂ) (m : ℕ) :
    HasDerivAt (fun s => modelV (u:ℂ) s m) (reciprocalKernel (modelProfile (1/2) τ) 0 u m) τ := by
  have h := modelDenom_slope (1/2) τ
  rw [kernel_eq_variation]
  apply functional_deriv
  convert h using 2 <;> norm_num [reciprocalDirection,reciprocalDenom]

theorem convolution_zero (H : PowerSeries ℂ) (v : ℂ) (m : ℕ) :
    exponentialConvolution H 0 v m = functionalCoeff H v m := by
  unfold exponentialConvolution
  rw [sum_eq_single 0]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem modelV_deriv_zero (u : ℝ) (τ : ℂ) :
    HasDerivAt (fun s => modelV (u:ℂ) s 0) 1 τ := modelV_hasDeriv u τ 0

theorem modelV_deriv_one (u : ℝ) (τ : ℂ) :
    HasDerivAt (fun s => modelV (u:ℂ) s 1) 0 τ := by
  simpa [reciprocalKernel] using modelV_hasDeriv u τ 1

theorem modelV_deriv_integral (u : ℝ) (τ : ℂ) (m : ℕ) :
    HasDerivAt (fun s => modelV (u:ℂ) s (m+2))
      (∫ v : ℝ in 0..u, (1-(v:ℂ))*modelV (v:ℂ) τ m) τ := by
  simpa [reciprocalKernel,convolution_zero,modelV] using modelV_hasDeriv u τ (m+2)

private def quadraticDenom (P : PowerSeries ℂ) : PowerSeries ℂ := 1-2*X^2*P

private theorem model_w_derivative (τ : ℂ) :
    shiftDirection (modelProfile 1 τ)= -X*modelProfile 1 τ*(quadraticDenom (modelProfile 1 τ))⁻¹ := by
  let P := modelProfile 1 τ
  let M := quadraticDenom P
  have q : P = C τ+X^2*P^2 := by simpa [P] using modelProfile_quadratic 1 τ
  have eq := congrArg derivative q
  have d : derivative P=2*X*P^2+X^2*(2*P*derivative P) := by
    simp [derivative_pow,Derivation.leibniz,smul_eq_mul] at eq
    linear_combination eq
  have e : (P+X*derivative P)*M=P := by
    change (P+X*derivative P)*(1-2*X^2*P)=P
    linear_combination X*d
  have inv : M*M⁻¹=1 := PowerSeries.mul_inv_cancel M (by simp [M,quadraticDenom])
  change -X*(P+X*derivative P) = -X*P*M⁻¹
  calc
    _ = -X*((P+X*derivative P)*M)*M⁻¹ := by rw [mul_assoc (-X),mul_assoc _ M,inv,mul_one]
    _ = _ := by rw [e]

private theorem sign_direction (a : ℂ) (ha : a≠0) :
    let P := modelProfile 1 (a^2)
    reciprocalDirection P a = (quadraticDenom P)⁻¹-C a⁻¹*shiftDirection P := by
  dsimp only
  let P := modelProfile 1 (a^2)
  let M := quadraticDenom P
  let J := reciprocalDenom P a
  have q : P = C (a^2)+X^2*P^2 := by simpa only [P,map_one,one_mul] using modelProfile_quadratic 1 (a^2)
  have ca : (C a⁻¹ : PowerSeries ℂ)*C a=1 := by rw [←map_mul,inv_mul_cancel₀ ha,map_one]
  have ca2 : (C a⁻¹ : PowerSeries ℂ)*C (a^2)=C a := by rw [map_pow,sq,←mul_assoc,ca,one_mul]
  have eq : J*(1+C a⁻¹*X*P)=M := by
    change (1-C a*X-X^2*P)*(1+C a⁻¹*X*P)=1-2*X^2*P
    linear_combination C a⁻¹*X*q + X*ca2 - X^2*P*ca
  have hi : J⁻¹*J=1 := PowerSeries.inv_mul_cancel J (by simp [J,reciprocalDenom])
  have mi : M*M⁻¹=1 := PowerSeries.mul_inv_cancel M (by simp [M,quadraticDenom])
  have e : J⁻¹=(1+C a⁻¹*X*P)*M⁻¹ := by calc
    J⁻¹ = J⁻¹*(M*M⁻¹) := by rw [mi,mul_one]
    _ = _ := by rw [←eq,←mul_assoc,←mul_assoc,hi,one_mul]
  rw [model_w_derivative]
  change J⁻¹=M⁻¹-C a⁻¹*(-X*P*M⁻¹)
  rw [e]; ring

private theorem variation_sub_const (P L S : PowerSeries ℂ) (c u : ℂ) (m : ℕ) :
    firstVariation P (L-C c*S) u m=firstVariation P L u m-c*firstVariation P S u m := by
  simp only [firstVariation_extract,mul_sub]
  rw [show residueBase P u^m*(C c*S)=C c*(residueBase P u^m*S) by ring,map_sub,coeff_C_mul]
  ring

/-- Multiplication of an exponentially normalized series by the ordinary variable x. -/
def timesX (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | m+1 => f m

private theorem variation_shift (P : PowerSeries ℂ) (u : ℂ) (m : ℕ) :
    firstVariation P (shiftDirection P) u m = -u*timesX (functionalCoeff P u) m := by
  cases m with
  | zero => simp [timesX,shift_zero]
  | succ m => exact shift_succ P u m

private theorem sign_kernel (a : ℂ) (ha : a≠0) (u : ℝ) (m : ℕ) :
    let P := modelProfile 1 (a^2)
    reciprocalKernel P a u m = firstVariation P (quadraticDenom P)⁻¹ u m +
      ((u:ℂ)/a)*timesX (modelU (u:ℂ) (a^2)) m := by
  dsimp only
  rw [kernel_eq_variation,sign_direction a ha,variation_sub_const,variation_shift]
  change _ = _ + _*timesX (functionalCoeff (modelProfile 1 (a^2)) u) m
  ring

/-- The expectation over a random sign of mean ω, at degree m, with the
transport term moved to the left to display the genuine real derivative. -/
theorem modelU_sign_deriv (t : ℝ) (ht : 0<t) (u ω : ℝ) (m : ℕ) :
    HasDerivAt (fun s : ℝ => modelU (u:ℂ) (s:ℂ) m)
      (((1+(ω:ℂ))/2)*reciprocalKernel (modelProfile 1 (t:ℂ)) (Real.sqrt t) u m +
       ((1-(ω:ℂ))/2)*reciprocalKernel (modelProfile 1 (t:ℂ)) (-(Real.sqrt t:ℂ)) u m -
       ((ω:ℂ)*u/(Real.sqrt t:ℂ))*timesX (modelU (u:ℂ) (t:ℂ)) m) t := by
  let a : ℂ := Real.sqrt t
  have ha : a≠0 := by dsimp [a]; exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have sq : a^2=(t:ℂ) := by dsimp [a]; exact_mod_cast Real.sq_sqrt ht.le
  have hpos := sign_kernel a ha u m
  have hneg := sign_kernel (-a) (neg_ne_zero.mpr ha) u m
  simp only [neg_sq,sq] at hpos hneg
  rw [show (Real.sqrt t:ℂ)=a by rfl,hpos,hneg]
  have d := (functional_deriv (modelDenom_slope 1 (t:ℂ)) (u:ℂ) m).comp_ofReal
  change HasDerivAt (fun s : ℝ => functionalCoeff (modelProfile 1 (s:ℂ)) u m) _ t
  convert d using 1
  simp only [mul_one,map_ofNat,quadraticDenom]
  ring

end Springer
