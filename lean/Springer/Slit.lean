import Springer.Residue
import Springer.PolynomialCoeff

noncomputable section
open Set Function Filter Finset Polynomial
open scoped Topology Polynomial
namespace Springer

def slitMap (b z : ℂ) := z+b/z

theorem slit_profile (b t : ℂ) : profile (slitMap b) t=1+b*t^2 := by
  by_cases h : t=0
  · simp [h]
  · simp [profile,h,slitMap,div_eq_mul_inv,mul_add,mul_inv_cancel₀ h]; ring

theorem slit_sigma {b : ℂ} (hb : ‖b‖≤1) : Sigma (slitMap b) := by
  have ne {z : ℂ} (hz : z∈exterior) : z≠0 := norm_pos_iff.mp (zero_lt_one.trans hz)
  refine ⟨fun z hz => ?_,?_,?_,?_⟩
  · unfold slitMap; fun_prop (disch := exact ne hz)
  · intro z hz v hv e
    by_contra h
    unfold slitMap at e
    field_simp [ne hz,ne hv] at e
    have eq : (z-v)*(z*v-b)=0 := by linear_combination e
    have H := congrArg norm (sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left (sub_ne_zero.mpr h)))
    rw [norm_mul] at H
    have gt := one_lt_mul_of_lt_of_le (show 1<‖z‖ from hz) (show 1≤‖v‖ from hv.le)
    linarith
  · rw [funext (slit_profile b)]; intro t ht; fun_prop
  · rw [funext (slit_profile b)]
    have H := (((hasDerivAt_id (0:ℂ)).pow 2).const_mul b).const_add 1
    simpa [id_eq] using H.deriv

private theorem slit_coeff {b : ℂ} (n d : ℕ) :
    taylorCoeff (fun t => profile (slitMap b) t^n) d=
    ∑ j∈range (n+1), if 2*j=d then b^j*(n.choose j:ℂ) else 0 := by
  let P := ((monomial 2 b)+1 : ℂ[X])^n
  have E : (fun t => profile (slitMap b) t^n)=(fun t => P.eval t) := by
    funext t; simp [P,slit_profile,eval_monomial,add_comm]
  rw [E,taylorCoeff_polynomial]
  simp only [P,add_pow,finsetSum_coeff,one_pow,mul_one,←C_eq_natCast,coeff_mul_C,monomial_pow,coeff_monomial,ite_mul,zero_mul]

theorem slit_inverse_odd {b : ℂ} (hb : ‖b‖≤1) (m : ℕ) :
    inverseCoeff (slitMap b) (2*m+1)= -(catalan m:ℂ)*b^(m+1) := by
  have h := inverse_residue (slit_sigma hb) (show 2*m+1≠0 by omega)
  rw [slit_coeff] at h
  have eq (j : ℕ) : (2*j=2*m+1+1) ↔ j=m+1 := by omega
  simp only [eq,sum_ite_eq',Finset.mem_range,show m+1<2*m+1+1 by omega,ite_true] at h
  have hc : (2*m+1).choose (m+1)=(2*m+1)*catalan m := by
    have H := Nat.choose_mul_succ_eq (2*m) m
    have hsym := Nat.choose_symm (show m≤2*m+1 by omega)
    rw [show 2*m+1-m=m+1 by omega] at H hsym
    rw [←Nat.centralBinom,←succ_mul_catalan_eq_centralBinom,←hsym] at H
    nlinarith [H]
  rw [hc] at h
  apply mul_left_cancel₀ (show ((2*m+1:ℕ):ℂ)≠0 by exact_mod_cast (by omega : 2*m+1≠0))
  rw [h]; push_cast; ring

theorem slit_inverse_even {b : ℂ} (hb : ‖b‖≤1) {m : ℕ} (hm : m≠0) :
    inverseCoeff (slitMap b) (2*m)=0 := by
  have hn : 2*m≠0 := by omega
  have h := inverse_residue (slit_sigma hb) hn
  rw [slit_coeff] at h
  simp only [show ∀ j, ¬2*j=2*m+1 by intro j; omega,ite_false,sum_const_zero,neg_zero,mul_eq_zero,Nat.cast_eq_zero,hn,false_or] at h
  exact h

end Springer
