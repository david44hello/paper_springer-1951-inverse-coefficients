import Springer.FunctionalDerivative

noncomputable section
open PowerSeries Finset
namespace Springer

/-- The polynomial in the reciprocal coordinate obtained by multiplying
u*w+(1-u)*H(w) by 1/w. -/
def residueBase (H : PowerSeries ℂ) (u : ℂ) : PowerSeries ℂ :=
  C u + C (1-u)*X^2*H

/-- Binomial expansion followed by coefficient extraction; both summands may
carry powers of the reciprocal variable. -/
private theorem weighted_binomial (P Q L : PowerSeries ℂ) (b c : ℂ) (p q m d : ℕ) :
    ((C b*X^p*P+C c*X^q*Q)^m*L).coeff d / m.factorial =
      ∑ j∈range (m+1), b^j*c^(m-j)/(j.factorial*((m-j).factorial:ℂ))*
        (if p*j+q*(m-j)≤d then (P^j*Q^(m-j)*L).coeff (d-(p*j+q*(m-j))) else 0) := by
  rw [add_pow,sum_mul,map_sum,Finset.sum_div]
  apply sum_congr rfl
  intro j hj
  let k := m-j
  have e : (C b*X^p*P)^j*(C c*X^q*Q)^k*(m.choose j:PowerSeries ℂ)*L =
      (m.choose j:PowerSeries ℂ) * (C (b^j*c^k) *
        (X^(p*j+q*k)*(P^j*Q^k*L))) := by
    simp only [mul_pow,map_mul,map_pow,pow_add,pow_mul]
    ring
  change ((C b*X^p*P)^j*(C c*X^q*Q)^k*(m.choose j:PowerSeries ℂ)*L).coeff d / _ = _
  rw [e,coeff_natCast_mul,coeff_C_mul,coeff_X_pow_mul']
  have he := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ (mem_range.mp hj))
  have hc : (m.choose j:ℂ)*(j.factorial:ℂ)*(k.factorial:ℂ) = (m.factorial:ℂ) := by exact_mod_cast he
  have hj0 : (j.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hk0 : (k.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hm0 : (m.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  change _ = b^j*c^k/((j.factorial:ℂ)*(k.factorial:ℂ))*(if p*j+q*k≤d then _ else 0)
  field_simp [hj0,hk0,hm0]
  linear_combination (b^j*c^k*(if p*j+q*k≤d then (P^j*Q^k*L).coeff (d-(p*j+q*k)) else 0))*hc

theorem firstVariation_extract (H L : PowerSeries ℂ) (u : ℂ) (m : ℕ) :
    firstVariation H L u m = (residueBase H u^m*L).coeff m / m.factorial := by
  have h := weighted_binomial 1 H L u (1-u) 0 2 m m
  simp only [pow_zero,mul_one,zero_mul,zero_add,one_pow,one_mul] at h
  rw [firstVariation,residueBase,h]
  apply sum_congr rfl
  intro j hj
  have hjm := Nat.le_of_lt_succ (mem_range.mp hj)
  have e : (2*(m-j) ≤ m) ↔ m-j≤j := by omega
  simp only [e,show m-2*(m-j)=j-(m-j) by omega]

theorem expResidue_extract (H : PowerSeries ℂ) (u : ℂ) (m : ℕ) :
    expResidue H u m = (residueBase H u^m).coeff (m+1) / m.factorial := by
  have h := weighted_binomial 1 H 1 u (1-u) 0 2 m (m+1)
  simp only [pow_zero,mul_one,zero_mul,zero_add,one_pow,one_mul] at h
  rw [expResidue,residueBase,h]
  apply sum_congr rfl
  intro j hj
  have hjm := Nat.le_of_lt_succ (mem_range.mp hj)
  have e : (2*(m-j) ≤ m+1) ↔ m-j≤j+1 := by omega
  simp only [e,show m+1-2*(m-j)=j+1-(m-j) by omega]

def reciprocalDenom (H : PowerSeries ℂ) (a : ℂ) : PowerSeries ℂ := 1-C a*X-X^2*H

def reciprocalDirection (H : PowerSeries ℂ) (a : ℂ) := (reciprocalDenom H a)⁻¹

theorem reciprocal_cancel (H : PowerSeries ℂ) (a : ℂ) :
    reciprocalDenom H a * reciprocalDirection H a=1 := by
  apply PowerSeries.mul_inv_cancel
  simp [reciprocalDenom]

/-- Interpolates the exponent while fixing the endpoint u. Its velocity is the
denominator of the reciprocal direction, exactly as in the integral identity. -/
private def exponentLine (H : PowerSeries ℂ) (a u v : ℂ) : PowerSeries ℂ :=
  X^2*H + C (u*a)*X + C v * reciprocalDenom H a

private theorem exponentLine_split (H : PowerSeries ℂ) (a u v : ℂ) :
    exponentLine H a u v=C ((u-v)*a)*X+residueBase H v := by
  simp only [exponentLine,reciprocalDenom,residueBase,map_mul,map_sub,map_one]; ring

private theorem exponentLine_deriv (H : PowerSeries ℂ) (a u v : ℂ) :
    CoeffDerivAt (exponentLine H a u) (reciprocalDenom H a) v := by
  intro j
  simp only [exponentLine,map_add,coeff_C_mul]
  simpa only [id_eq,one_mul,coeff_C_mul] using
    (((hasDerivAt_id v).mul_const ((reciprocalDenom H a).coeff j)).const_add
      ((X^2*H).coeff j+(u*a)*(X:PowerSeries ℂ).coeff j))

private theorem reciprocal_integrand (H : PowerSeries ℂ) (a u v : ℂ) (n : ℕ) :
    HasDerivAt (fun s => (exponentLine H a u s^(n+1)*reciprocalDirection H a).coeff (n+1) /
      (n+1).factorial) ((exponentLine H a u v^n).coeff (n+1)/n.factorial) v := by
  let L := reciprocalDirection H a
  have hc : CoeffDerivAt (fun _ : ℂ => L) 0 v := fun j => by simpa using
    (hasDerivAt_const v (L.coeff j))
  have h := (coeffDeriv_mul (coeffDeriv_pow (exponentLine_deriv H a u v) (n+1)) hc (n+1)).div_const
    ((n+1).factorial:ℂ)
  have E : (↑(n+1):PowerSeries ℂ)*exponentLine H a u v^(n+1-1)*reciprocalDenom H a*L+
      exponentLine H a u v^(n+1)*0=(↑(n+1):PowerSeries ℂ)*exponentLine H a u v^n := by
    rw [Nat.add_sub_cancel,mul_zero,add_zero,mul_assoc _ (reciprocalDenom H a) L,
      reciprocal_cancel,mul_one]
  rw [E,coeff_natCast_mul,Nat.factorial_succ,Nat.cast_mul] at h
  rw [Nat.factorial_succ,Nat.cast_mul]
  convert h using 1
  field_simp [show ((n+1:ℕ):ℂ)≠0 by exact_mod_cast Nat.succ_ne_zero n]

private theorem initial_residue (H : PowerSeries ℂ) (a u : ℂ) (m : ℕ) :
    (exponentLine H a u 0^m*reciprocalDirection H a).coeff m=(u*a)^m := by
  have h : exponentLine H a u 0 = X*(X*H+C (u*a)) := by simp [exponentLine]; ring
  rw [h,mul_pow,mul_assoc,coeff_X_pow_mul']
  simp [coeff_zero_eq_constantCoeff_apply,reciprocalDirection,reciprocalDenom,constantCoeff_inv]

theorem reciprocal_integral_raw (H : PowerSeries ℂ) (a : ℂ) (u : ℝ) (n : ℕ) :
    firstVariation H (reciprocalDirection H a) u (n+1) = ((u:ℂ)*a)^(n+1)/(n+1).factorial +
      ∫ v : ℝ in 0..u, (exponentLine H a u v^n).coeff (n+1)/n.factorial := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := u) (fun v _ => (reciprocal_integrand H a u v n).comp_ofReal)
  have cont : Continuous (fun v : ℝ => (exponentLine H a u v^n).coeff (n+1)/(n.factorial:ℂ)) :=
    continuous_iff_continuousAt.mpr fun v =>
      (((coeffDeriv_pow (exponentLine_deriv H a u v) n (n+1)).comp_ofReal).div_const _).continuousAt
  specialize h (cont.intervalIntegrable _ _)
  rw [h,Complex.ofReal_zero,initial_residue,exponentLine_split,sub_self,zero_mul,map_zero,zero_mul,
    zero_add,firstVariation_extract]
  ring

/-- Coefficient of the product of exp(c*x) with the formal exponential residue. -/
private theorem line_residue (H : PowerSeries ℂ) (a u v : ℂ) (n : ℕ) :
    (exponentLine H a u v^n).coeff (n+1)/n.factorial =
      ∑ j∈range (n+1), (((u-v)*a)^j/j.factorial)*expResidue H v (n-j) := by
  have h := weighted_binomial 1 (residueBase H v) 1 ((u-v)*a) 1 1 0 n (n+1)
  simp only [pow_zero,pow_one,one_mul,mul_one,map_one,zero_mul,add_zero,one_pow] at h
  rw [exponentLine_split,h]
  apply sum_congr rfl
  intro j hj
  have hjn := Nat.le_of_lt_succ (mem_range.mp hj)
  simp only [show j≤n+1 by omega,ite_true,show n+1-j=n-j+1 by omega,expResidue_extract]
  ring

/-- Coefficient of x^m in exp(c*x) times K_v(H). -/
def exponentialConvolution (H : PowerSeries ℂ) (c v : ℂ) (m : ℕ) :=
  ∑ j∈range (m+1), (c^j/j.factorial)*functionalCoeff H v (m-j)

theorem reciprocal_degree_zero (H : PowerSeries ℂ) (a u : ℂ) :
    firstVariation H (reciprocalDirection H a) u 0=1 := by
  simp [firstVariation_extract,coeff_zero_eq_constantCoeff_apply,reciprocalDirection,reciprocalDenom,
    constantCoeff_inv]

theorem reciprocal_degree_one (H : PowerSeries ℂ) (a : ℂ) (u : ℝ) :
    firstVariation H (reciprocalDirection H a) u 1=(u:ℂ)*a := by
  rw [reciprocal_integral_raw H a u 0]
  simp [coeff_one]

theorem reciprocal_integral (H : PowerSeries ℂ) (a : ℂ) (u : ℝ) (m : ℕ) :
    firstVariation H (reciprocalDirection H a) u (m+2)=((u:ℂ)*a)^(m+2)/(m+2).factorial +
      ∫ v : ℝ in 0..u, (1-(v:ℂ))*exponentialConvolution H (((u:ℂ)-v)*a) v m := by
  rw [reciprocal_integral_raw H a u (m+1)]
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [line_residue H a (u:ℂ) (v:ℂ) (m+1),sum_range_succ,exponentialConvolution,mul_sum]
  simp only [Nat.sub_self,expResidue_zero,mul_zero,add_zero]
  apply sum_congr rfl
  intro j hj
  have hjm := Nat.le_of_lt_succ (mem_range.mp hj)
  rw [show m+1-j=m-j+1 by omega,expResidue_succ]
  ring

end Springer
