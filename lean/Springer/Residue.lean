import Springer.Coefficients

noncomputable section
open Set Filter Function Complex Finset
open scoped Topology
namespace Springer

private def jac (A : ℂ → ℂ) (t : ℂ) := 1-t*deriv A t/A t

private theorem jac_analytic {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) (hu : A 0≠0) : AnalyticAt ℂ (jac A) 0 :=
  analyticAt_const.sub ((analyticAt_id.mul hA.deriv).div hA hu)

private theorem jac_coeff {A : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) (hu : A 0≠0) {k : ℕ} (hk : k≠0) (n : ℕ) :
    taylorCoeff (fun t => A t^k*jac A t) n=(1-(n:ℂ)/k)*taylorCoeff (fun t => A t^k) n := by
  let f := fun t => A t^k
  have hf : AnalyticAt ℂ f 0 := hA.pow k
  have E : (fun t => A t^k*jac A t) =ᶠ[𝓝 0] fun t => f t-(1/(k:ℂ))*(t*deriv f t) := by
    filter_upwards [hA.eventually_analyticAt,hA.continuousAt.eventually_ne hu] with t ht hn
    have d : deriv f t=k*A t^(k-1)*deriv A t := (ht.differentiableAt.hasDerivAt.pow k).deriv
    rw [d,jac]
    dsimp only [f]
    have hpow : A t^(k-1)*A t=A t^k := by rw [←pow_succ]; congr 1; omega
    have hk' : (k:ℂ)≠0 := by exact_mod_cast hk
    field_simp
    linear_combination (t*deriv A t)*hpow
  erw [taylorCoeff_congr E,taylorCoeff_sub hf (analyticAt_const (v:=(1/(k:ℂ))).mul (analyticAt_id.mul hf.deriv)),
    taylorCoeff_const_mul,taylorCoeff_euler hf]
  dsimp only [f]; ring

private theorem transported_coeff {A J : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) (ha : A 0=1)
    (hJ : AnalyticAt ℂ J 0) (N : ℕ) :
    taylorCoeff (fun t => A t^N*J (t/A t)*jac A t) N=taylorCoeff J N := by
  let q := fun t => t/A t
  have hu : A 0≠0 := ha ▸ one_ne_zero
  have hq : AnalyticAt ℂ q 0 := analyticAt_id.div hA hu
  have q₀ : q 0=0 := by simp [q]
  have hD := jac_analytic hA hu
  obtain ⟨F,hF,expan⟩ := hJ.exists_eq_sum_add_pow_mul (N+1)
  let term := fun (j : ℕ) (t : ℂ) => taylorCoeff J j*(t^j*(A t^(N-j)*jac A t))
  let remn := fun t => (F (q t)*jac A t)/A t
  have hrem : AnalyticAt ℂ remn 0 := ((hF.comp_of_eq hq q₀).mul hD).div hA hu
  have ht (j : ℕ) : AnalyticAt ℂ (term j) 0 := analyticAt_const.mul ((analyticAt_id.pow j).mul ((hA.pow _).mul hD))
  have E : (fun t => A t^N*J (t/A t)*jac A t) =ᶠ[𝓝 0]
      fun t => (∑ j∈range (N+1), term j t)+t^(N+1)*remn t := by
    filter_upwards [hA.continuousAt.eventually_ne hu] with t hn
    rw [expan (t/A t),mul_add,add_mul]
    apply congrArg₂ (·+·)
    · rw [mul_sum,sum_mul]
      apply sum_congr rfl
      intro j hj
      have hj' : j≤N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have Hp : A t^N=A t^(N-j)*A t^j := by rw [←pow_add,Nat.sub_add_cancel hj']
      simp only [Hp,term,taylorCoeff,div_pow,smul_eq_mul]
      field_simp <;> ring
    · dsimp only [remn,q]; rw [smul_eq_mul,div_pow,pow_succ (A t) N]
      field_simp <;> ring
  erw [taylorCoeff_congr E,taylorCoeff_add (Finset.analyticAt_fun_sum (range (N+1)) (fun j _ => ht j)) ((analyticAt_id.pow (N+1)).mul hrem),
    taylorCoeff_sum _ (fun j _ => ht j),taylorCoeff_shift hrem]
  simp only [Nat.not_succ_le_self,if_false,add_zero]
  rw [sum_eq_single N]
  · dsimp only [term]; erw [taylorCoeff_const_mul,taylorCoeff_shift ((hA.pow (N-N)).mul hD),if_pos le_rfl,Nat.sub_self,taylorCoeff_zero]; simp [jac]
  · intro j hj hjN
    have hj' : j≤N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hpos : N-j≠0 := by omega
    erw [show term j=(fun t => taylorCoeff J j*(t^j*(A t^(N-j)*jac A t))) from rfl,
      taylorCoeff_const_mul,taylorCoeff_shift ((hA.pow (N-j)).mul hD),if_pos hj',jac_coeff hA hu hpos]
    simp [hpos]
  · simp
  -- the diagonal term has constant coefficient jac(A,0)=1

/-- The residue at infinity in n*g^{-1} is computed from the forward profile:
n B_n equals minus the coefficient of degree n+1 in A(t)^n. -/
theorem inverse_residue {g : ℂ → ℂ} (hg : Sigma g) {n : ℕ} (hn : n≠0) :
    (n:ℂ)*inverseCoeff g n = -taylorCoeff (fun t => profile g t^n) (n+1) := by
  let A := profile g
  have hA : AnalyticAt ℂ A 0 := hg.regular _ (by simp [disc])
  have ha : A 0=1 := profile_zero _
  have hu : A 0≠0 := by rw [ha]; norm_num
  obtain ⟨hJ,_,inv,_⟩ := inverse_germ hg
  have H := transported_coeff hA ha hJ (n+1)
  have E : (fun t => A t^(n+1)*inverseProfile g (t/A t)*jac A t)=ᶠ[𝓝 0] fun t => A t^n*jac A t := by
    filter_upwards [inv,hA.continuousAt.eventually_ne hu] with t ht hn'
    change inverseProfile g (t/A t)=(A t)⁻¹ at ht
    rw [ht,pow_succ,mul_assoc (A t^n),mul_inv_cancel₀ hn',mul_one]
  rw [taylorCoeff_congr E,jac_coeff hA hu hn] at H
  change (n:ℂ)*taylorCoeff (inverseProfile g) (n+1) = _
  rw [←H]; push_cast
  have hn' : (n:ℂ)≠0 := by exact_mod_cast hn
  field_simp <;> ring

end Springer
