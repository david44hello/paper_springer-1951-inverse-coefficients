import Springer.FunctionalDerivative
noncomputable section
open PowerSeries Finset
namespace Springer

/-- Stored series for the w-derivative of the Laurent series t*H(t), t=1/w. -/
def shiftDirection (H : PowerSeries ℂ) := -X*(H+X*derivative H)

private theorem coeff_euler (P : PowerSeries ℂ) (n : ℕ) :
    (X*derivative P).coeff n=(n:ℂ)*P.coeff n := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul,coeff_derivative,Nat.cast_succ,mul_comm]

private theorem coeff_shift (H : PowerSeries ℂ) (l s : ℕ) :
    ((l:ℂ)+1)*(H^l*shiftDirection H).coeff (s+1) =
      -((l:ℂ)+1+s)*(H^(l+1)).coeff s := by
  have e : (↑(l+1):PowerSeries ℂ)*(H^l*shiftDirection H) =
      -(X*((↑(l+1):PowerSeries ℂ)*H^(l+1)+X*derivative (H^(l+1)))) := by
    rw [derivative_pow]
    simp only [shiftDirection,Nat.add_sub_cancel,pow_succ]
    ring
  have he := congrArg (coeff (s+1)) e
  simp only [coeff_natCast_mul,map_neg,coeff_succ_X_mul,map_add,coeff_euler] at he
  push_cast at he
  rw [he]; ring

theorem shift_zero (H : PowerSeries ℂ) (u : ℂ) :
    firstVariation H (shiftDirection H) u 0=0 := by
  simp [firstVariation,shiftDirection,coeff_zero_eq_constantCoeff_apply]

theorem shift_succ (H : PowerSeries ℂ) (u : ℂ) (m : ℕ) :
    firstVariation H (shiftDirection H) u (m+1) = -u*functionalCoeff H u m := by
  rw [firstVariation,sum_range_succ',functionalCoeff,mul_sum]
  simp only [Nat.sub_zero,show ¬m+1≤0 by omega,ite_false,mul_zero,add_zero]
  apply sum_congr rfl
  intro j hj
  let l := m-j
  have he : m+1-(j+1)=l := by dsimp [l]; omega
  rw [he,shiftedResidue]
  by_cases hl : l≤j
  · have hl' : l≤j+1 := by omega
    have eq : j+1-l=(j-l)+1 := by omega
    change _ = -u*(_*(if l≤j then (H^(l+1)).coeff (j-l) else 0))
    simp only [if_pos hl',if_pos hl,eq]
    have hh := coeff_shift H l (j-l)
    have cast : (l:ℂ)+1+((j-l:ℕ):ℂ)=(j:ℂ)+1 := by rw [Nat.cast_sub hl]; ring
    rw [cast] at hh
    change u^(j+1)*(1-u)^l/(((j+1).factorial:ℂ)*(l.factorial:ℂ))*_ =
      -u*(u^j*(1-u)^l/((j.factorial:ℂ)*((l+1).factorial:ℂ))*_)
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,pow_succ u]
    have hj0 : (j.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hl0 : (l.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero l
    have hj1 : (j:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero j
    have hl1 : (l:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero l
    field_simp [hj0,hl0,hj1,hl1]
    linear_combination u^(j+1)*(1-u)^l*hh
  · change _ = -u*(_*(if l≤j then _ else 0))
    simp only [if_neg hl,mul_zero]
    split_ifs with h
    · have eq : l=j+1 := by omega
      simp [eq,shiftDirection,coeff_zero_eq_constantCoeff_apply]
    · simp

end Springer
