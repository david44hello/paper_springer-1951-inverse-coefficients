import Springer.Trinomial

noncomputable section
open Set Finset Real
namespace Springer

private theorem binom_le_central {x : ℝ} {k : ℕ} (hk : (k:ℝ)≤x) (hx : x≤2*k) :
    realBinom x k ≤ Nat.centralBinom k := by
  have H : (∏ j∈range k, (x-j)) ≤ ∏ j∈range k, ((2*k:ℕ)-j:ℝ) := by
    apply prod_le_prod₀
    · intro j hj; have hj' : j ≤ k := (Finset.mem_range.mp hj).le
      exact sub_nonneg.mpr ((by exact_mod_cast hj' : (j:ℝ)≤k).trans hk)
    · intro j _; push_cast; linarith
  have hcast : (∏ j∈range k, ((2*k:ℕ)-j:ℝ)) = ((2*k).descFactorial k:ℝ) := by
    rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
    apply prod_congr rfl; intro j hj
    exact (Nat.cast_sub (by have := Finset.mem_range.mp hj; omega)).symm
  rw [hcast,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul] at H
  exact (div_le_iff₀ (by positivity : 0<(k.factorial:ℝ))).mpr (by simpa [Nat.centralBinom,mul_comm] using H)

private theorem beta_power_gt {m : ℕ} (hm : 3 ≤ m) : 1/3<(beta m)^(m-1) := by
  let k := m-1
  have hk : 0<k := by dsimp [k]; omega
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hm' : (m:ℝ)=k+1 := by exact_mod_cast (by dsimp [k]; omega : m=k+1)
  have h : 1+1/(k:ℝ) ≤ Real.exp (1/k) := by linarith [Real.add_one_le_exp (1/(k:ℝ))]
  have he := pow_le_pow_left₀ (by positivity) h k
  have E : Real.exp (1/(k:ℝ))^k = Real.exp 1 := by rw [←Real.exp_nat_mul]; field_simp
  rw [E] at he
  have b : beta m=(1+1/(k:ℝ))⁻¹ := by rw [beta,hm']; field_simp; ring
  rw [b,inv_pow]
  simpa only [one_div] using (one_div_lt_one_div_of_lt (by positivity) (he.trans_lt Real.exp_one_lt_three))

private theorem central_triple {j : ℕ} (hj : 1≤j) : 3*j.centralBinom≤(j+1).centralBinom := by
  have H := Nat.succ_mul_centralBinom_succ j
  have H' : (j+1)*(3*j.centralBinom)≤(j+1)*(j+1).centralBinom := by
    rw [H]
    nlinarith only [Nat.mul_le_mul_right j.centralBinom hj]
  exact (Nat.le_of_mul_le_mul_left H' (by omega))

private theorem minfac_data {m : ℕ} (hm : 3 ≤ m) :
    let q := (2*m+1).minFac
    let k := (2*m+1)/q
    3≤q ∧ 1≤k ∧ k*q=2*m+1 ∧ (m≠4 → k+2≤ m) := by
  let q := (2*m+1).minFac
  let k := (2*m+1)/q
  have hq := Nat.minFac_prime (show 2*m+1≠1 by omega)
  have h₂ : 2≤q := hq.two_le
  have he : k*q=2*m+1 := Nat.div_mul_cancel (Nat.minFac_dvd _)
  have h₃ : 3≤q := by
    by_contra! h
    have eq : q=2 := by omega
    rw [eq] at he; omega
  have hk : 1≤k := by
    by_cases eq : k=0
    · rw [eq,zero_mul] at he; omega
    · exact Nat.pos_of_ne_zero eq
  refine ⟨h₃,hk,he,fun hm4 => ?_⟩
  change k+2≤ m
  by_cases h : m=3
  · subst m; norm_num [k,q]
  · have H := Nat.mul_le_mul_left k h₃
    rw [he] at H; omega

theorem even_lower_exceeds_springer {m : ℕ} (hm : 3 ≤ m) :
    sigmaBound (2*m)<(Nat.centralBinom m:ℝ)/(4*m)*(beta m)^(m-1) := by
  by_cases hm4 : m=4
  · subst m
    norm_num [sigmaBound,realBinom,beta,Nat.centralBinom,Finset.prod_range_succ,Nat.choose]
  let q := (2*m+1).minFac
  let k := (2*m+1)/q
  obtain ⟨hq,hk,he,hgap⟩ := minfac_data hm
  change 3≤q at hq
  change 1≤k at hk
  change k*q=2*m+1 at he
  have hdiff : k+2≤ m := hgap hm4
  have h₁ := central_triple hk
  have h₂ := central_triple (show 1≤k+1 by omega)
  have h₃ := Nat.centralBinom_strictMono.monotone hdiff
  change 3*(k+1).centralBinom≤(k+2).centralBinom at h₂
  have hc : 9*k.centralBinom≤ m.centralBinom := by omega
  have hqr : (3:ℝ)≤q := by exact_mod_cast hq
  have hr : (k:ℝ)*q=2*m+1 := by exact_mod_cast he
  have hp : (0:ℝ)<q := by linarith
  have hmr : (0:ℝ)< m := by exact_mod_cast (by omega : 0< m)
  have hm₃ : (3:ℝ)≤ m := by exact_mod_cast hm
  have H := binom_le_central (k:=k) (x:=4*m/q) ((le_div_iff₀ hp).mpr (by nlinarith)) ((div_le_iff₀ hp).mpr (by nlinarith))
  have hB := beta_power_gt hm
  have hcm : (0:ℝ)< m.centralBinom := by exact_mod_cast Nat.centralBinom_pos m
  have hck : (0:ℝ)<k.centralBinom := by exact_mod_cast Nat.centralBinom_pos k
  have hc' : 9*(k.centralBinom:ℝ)≤ m.centralBinom := by exact_mod_cast hc
  have hlt := mul_lt_mul_of_pos_left hB hcm
  change realBinom (2*((2*m:ℕ):ℝ)/q) k / ((2*m:ℕ):ℝ) < _
  push_cast
  rw [show (2:ℝ)*(2*m)=4*m by ring,div_mul_eq_mul_div,div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_lt_mul_of_pos_right (show 2*realBinom (4*m/q) k<(m.centralBinom:ℝ)*beta m^(m-1) by linarith) hmr]

end Springer
