import Springer.Trinomial
import Springer.Residue
import Springer.PolynomialCoeff

noncomputable section
open Set Filter Function Complex Finset Polynomial
open scoped Topology NNReal Polynomial
namespace Springer

private def castNN : ℝ≥0 →+* ℂ := Complex.ofRealHom.comp Nonneg.coeRingHom

private theorem binom_term (a b : ℝ≥0[X]) (n k d : ℕ) (hk : k≤n) :
    (a^k*b^(n-k)*(n.choose k:ℝ≥0[X])).coeff d ≤ ((a+b)^n).coeff d := by
  rw [add_pow,finsetSum_coeff]
  exact single_le_sum (f:=fun i => (a^i*b^(n-i)*(n.choose i:ℝ≥0[X])).coeff d) (fun _ _ => by positivity) (show k∈range (n+1) from Finset.mem_range.mpr (by omega))

private theorem positive_coefficient (m : ℕ) (hm : 3 ≤ m) (b c : ℝ≥0) :
    b^(m-1)*((2*m-1).choose (m-1):ℝ≥0)*c*(2*m:ℕ) ≤
      ((1+monomial 2 b+monomial 3 c : ℝ≥0[X])^(2*m)).coeff (2*m+1) := by
  let P := (1+monomial 2 b : ℝ≥0[X])
  have h := binom_term (monomial 3 c) P (2*m) 1 (2*m+1) (by omega)
  rw [add_comm (monomial 3 c) P] at h
  have hh := binom_term (monomial 2 b) (1:ℝ≥0[X]) (2*m-1) (m-1) (2*(m-1)) (by omega)
  rw [add_comm (monomial 2 b) 1] at hh
  change _ ≤ (P^(2*m-1)).coeff _ at hh
  simp only [one_pow,mul_one,←C_eq_natCast,coeff_mul_C,monomial_pow,coeff_monomial,ite_true] at hh
  simp only [pow_one,Nat.choose_one_right,←C_eq_natCast,coeff_mul_C] at h
  rw [show 2*m+1=2*(m-1)+3 by omega,coeff_monomial_mul] at h
  rw [show 2*(m-1)+3=2*m+1 by omega] at h
  calc
    _ = c*(b^(m-1)*((2*m-1).choose (m-1):ℝ≥0))*(2*m:ℕ) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh ((bot_le : 0 ≤ c))) ((by positivity))).trans h

private theorem half_central {m : ℕ} (hm : 0< m) : 2*((2*m-1).choose (m-1))=Nat.centralBinom m := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [Nat.centralBinom,show 2*(j+1)=(2*j+1)+1 by omega,Nat.choose_succ_succ']
  simp only [Nat.add_sub_cancel,Nat.succ_sub_one]
  rw [←Nat.choose_symm (show j≤2*j+1 by omega),show 2*j+1-j=j+1 by omega]
  ring

/-- Positivity of the forward polynomial lets one retain exactly the terms
with one cubic and m−1 quadratic selections. -/
theorem even_coefficient_lower {m : ℕ} (hm : 3 ≤ m) :
    (Nat.centralBinom m:ℝ)/(4*m)*(beta m)^(m-1) ≤ ‖inverseCoeff (trinomialMap m) (2*m)‖ := by
  have hm₁ : (1:ℝ)< m := by exact_mod_cast (by omega : 1< m)
  have hb : 0≤beta m := by unfold beta; linarith [one_div_lt_one_div_of_lt zero_lt_one hm₁]
  have hc : 0≤gamma m := by unfold gamma; positivity
  let b : ℝ≥0 := ⟨_,hb⟩
  let c : ℝ≥0 := ⟨_,hc⟩
  let P := (1+monomial 2 b+monomial 3 c : ℝ≥0[X])^(2*m)
  let k := P.coeff (2*m+1)
  have evalP (t : ℂ) : (P.map castNN).eval t = profile (trinomialMap m) t^(2*m) := by
    rw [trinomial_profile]
    simp only [P,←Polynomial.C_mul_X_pow_eq_monomial,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,Polynomial.map_one,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_X]
    rfl
  have H := inverse_residue (trinomial_sigma hm) (show 2*m≠0 by omega)
  rw [←funext evalP,taylorCoeff_polynomial,coeff_map] at H
  change (2*m:ℕ)*inverseCoeff (trinomialMap m) (2*m) = -((k:ℝ):ℂ) at H
  have hnorm := congrArg norm H
  simp only [norm_mul,Complex.norm_natCast,norm_neg,Complex.norm_of_nonneg k.2] at hnorm
  change ((2*m:ℕ):ℝ)*‖inverseCoeff (trinomialMap m) (2*m)‖=‖((k:ℝ):ℂ)‖ at hnorm
  have hh : ((2*m:ℕ):ℝ)*‖inverseCoeff (trinomialMap m) (2*m)‖=(k:ℝ) := hnorm.trans (Complex.norm_of_nonneg k.2)
  have hlow := positive_coefficient m hm b c
  have hlow' : beta m^(m-1)*((2*m-1).choose (m-1):ℝ)*gamma m*(2*m:ℕ)≤(k:ℝ) := by exact_mod_cast hlow
  have hc' : gamma m*((2*m:ℕ):ℝ)=1 := by unfold gamma; push_cast; field_simp
  have hhalf : (2:ℝ)*((2*m-1).choose (m-1):ℝ)=Nat.centralBinom m := by exact_mod_cast half_central (by omega : 0< m)
  rw [mul_assoc _ (gamma m),hc',mul_one,←hh] at hlow'
  push_cast at hlow'
  rw [←hhalf]
  have hpos : 0<(4:ℝ)*m := by positivity
  rw [div_mul_eq_mul_div,div_le_iff₀ hpos]
  linarith only [mul_le_mul_of_nonneg_left hlow' (by norm_num : (0:ℝ)≤2)]

end Springer
