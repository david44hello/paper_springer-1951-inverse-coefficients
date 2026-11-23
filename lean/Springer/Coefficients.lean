import Springer.Basic

noncomputable section
open Set Filter Function Complex Finset
open scoped Topology
namespace Springer

theorem taylorCoeff_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) (n : ℕ) : taylorCoeff f n=taylorCoeff g n :=
  congrArg (· / (n.factorial:ℂ)) (h.iteratedDeriv_eq n)

@[simp] theorem taylorCoeff_zero (f : ℂ → ℂ) : taylorCoeff f 0=f 0 := by simp [taylorCoeff]

theorem taylorCoeff_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i∈s, AnalyticAt ℂ (f i) 0) (n : ℕ) :
    taylorCoeff (fun x => ∑ i∈s, f i x) n=∑ i∈s, taylorCoeff (f i) n := by
  simp only [taylorCoeff,iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt),Finset.sum_div]

theorem taylorCoeff_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    taylorCoeff (fun t => f t+g t) n=taylorCoeff f n+taylorCoeff g n := by
  rw [taylorCoeff,iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt,add_div]; rfl

theorem taylorCoeff_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    taylorCoeff (fun t => f t-g t) n=taylorCoeff f n-taylorCoeff g n := by
  rw [taylorCoeff,iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt,sub_div]; rfl

theorem taylorCoeff_const_mul (c : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    taylorCoeff (fun t => c*f t) n=c*taylorCoeff f n := by
  unfold taylorCoeff
  change iteratedDeriv n (fun x => c • f x) 0 / _=_
  rw [iteratedDeriv_fun_const_smul_field,smul_eq_mul]; ring

theorem taylorCoeff_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    taylorCoeff (fun t => f t*g t) n=∑ i∈range (n+1), taylorCoeff f i*taylorCoeff g (n-i) := by
  simp only [taylorCoeff,iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt,Finset.sum_div]
  apply sum_congr rfl
  intro i hi
  have hk : i≤n := Nat.le_of_lt_succ (mem_range.mp hi)
  have h : ((n.choose i:ℕ):ℂ)*i.factorial*(n-i).factorial=n.factorial := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have nz (k : ℕ) : (k.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [nz]
  linear_combination (iteratedDeriv i f 0 * iteratedDeriv (n-i) g 0)*h

theorem taylorCoeff_pow (n k : ℕ) : taylorCoeff (fun t : ℂ => t^k) n=if n=k then 1 else 0 := by
  unfold taylorCoeff
  rw [iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · subst n; simp [Nat.factorial_ne_zero]
  · simp

theorem taylorCoeff_shift {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (k n : ℕ) :
    taylorCoeff (fun t => t^k*f t) n=if k≤n then taylorCoeff f (n-k) else 0 := by
  rw [taylorCoeff_mul (by fun_prop) hf]
  simp only [taylorCoeff_pow,ite_mul,one_mul,zero_mul,sum_ite_eq',Finset.mem_range,Nat.lt_succ_iff]

theorem taylorCoeff_deriv (f : ℂ → ℂ) (n : ℕ) :
    taylorCoeff (deriv f) n=(n+1)*taylorCoeff f (n+1) := by
  simp only [taylorCoeff,iteratedDeriv_succ',Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

theorem taylorCoeff_euler {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    taylorCoeff (fun t => t*deriv f t) n=n*taylorCoeff f n := by
  have H := taylorCoeff_shift hf.deriv 1 n
  simp only [pow_one] at H
  rw [H]
  cases n with
  | zero => simp
  | succ n => simp [taylorCoeff_deriv]

theorem inverse_series {g : ℂ → ℂ} (h : Sigma g) :
    ∀ᶠ t : ℂ in 𝓝[≠] 0, HasSum (fun j : ℕ => inverseCoeff g (j+1)*t^(j+1)) (invFunOn g exterior t⁻¹-t⁻¹) := by
  let f := inverseProfile g
  have H := (inverse_germ h).1.hasFPowerSeriesAt.eventually_hasSum_sub
  filter_upwards [H.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht (hn : t≠0)
  have hs : HasSum (fun j => taylorCoeff f j*t^j) (f t) := by
    simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,FormalMultilinearSeries.coeff_ofScalars,
      sub_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_comm,taylorCoeff,f] using ht
  have htail := (hasSum_nat_add_iff' 2).mpr hs
  have hfirst : taylorCoeff f 1=0 := by simp [taylorCoeff,f,(inverse_germ h).2.1]
  have hz : f 0=1 := profile_zero _
  simp only [sum_range_succ,sum_range_zero,zero_add,taylorCoeff_zero,hz,pow_zero,mul_one,hfirst,zero_mul,add_zero] at htail
  have hdiv := htail.div_const t
  convert hdiv using 1
  · funext j
    simp only [inverseCoeff,f,show j+2=(j+1)+1 by omega,pow_succ t (j+1)]
    field_simp
  · dsimp only [f,inverseProfile,profile]; rw [if_neg hn]; field_simp

end Springer
