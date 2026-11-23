import Springer.ResidueFunctional

noncomputable section
open Finset PowerSeries Filter
open scoped Topology
namespace Springer

/-- Derivative of a formal path means the ordinary scalar derivative of every coefficient. -/
def CoeffDerivAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (H : 𝕜 → PowerSeries ℂ) (L : PowerSeries ℂ) (t : 𝕜) : Prop :=
  ∀ n, HasDerivAt (fun s => (H s).coeff n) (L.coeff n) t

theorem coeffDeriv_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {F G : 𝕜 → PowerSeries ℂ} {D E : PowerSeries ℂ} {t : 𝕜}
    (hF : CoeffDerivAt F D t) (hG : CoeffDerivAt G E t) :
    CoeffDerivAt (fun s => F s*G s) (D*G t+F t*E) t := by
  intro j
  simp only [map_add,PowerSeries.coeff_mul,←Finset.sum_add_distrib]
  apply HasDerivAt.fun_sum
  intro a _
  exact (hF a.1).mul (hG a.2)

theorem coeffDeriv_pow {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {H : 𝕜 → PowerSeries ℂ} {L : PowerSeries ℂ} {t : 𝕜} (hd : CoeffDerivAt H L t) (p : ℕ) :
    CoeffDerivAt (fun s => H s^p) ((p:PowerSeries ℂ)*H t^(p-1)*L) t := by
  induction p with
  | zero => intro j; simp; exact hasDerivAt_const _ _
  | succ p ih =>
    have h := coeffDeriv_mul ih hd
    suffices eq : (p:PowerSeries ℂ)*H t^(p-1)*L*H t+H t^p*L=(p+1)*H t^p*L by
      simpa only [pow_succ (H _) p,Nat.cast_succ,Nat.succ_sub_one,eq] using h
    cases p with
    | zero => simp
    | succ p => simp only [Nat.cast_succ,Nat.succ_sub_one,pow_succ]; ring

/-- Coefficient of the bilinear Laurent residue in the direction L. -/
def firstVariation (H L : PowerSeries ℂ) (u : ℂ) (m : ℕ) :=
  ∑ j∈range (m+1), u^j*(1-u)^(m-j)/(j.factorial*((m-j).factorial:ℂ))*
    (if m-j≤j then (H^(m-j)*L).coeff (j-(m-j)) else 0)

theorem functional_deriv {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {H : 𝕜 → PowerSeries ℂ} {L : PowerSeries ℂ} {t : 𝕜} (hd : CoeffDerivAt H L t) (u : ℂ) (m : ℕ) :
    HasDerivAt (fun s => functionalCoeff (H s) u m) (firstVariation (H t) L u m) t := by
  unfold functionalCoeff firstVariation
  apply HasDerivAt.fun_sum
  intro j hj
  unfold shiftedResidue
  by_cases h : m-j≤j
  · simp only [if_pos h]
    let k := m-j
    have d := (coeffDeriv_pow hd (k+1) (j-k)).const_mul (u^j*(1-u)^k/(j.factorial*((k+1).factorial:ℂ)))
    have c : ((↑(k+1):PowerSeries ℂ)*H t^(k+1-1)*L).coeff (j-k) =
        ((k:ℂ)+1)*(H t^k*L).coeff (j-k) := by
      rw [Nat.add_sub_cancel,mul_assoc,coeff_natCast_mul,Nat.cast_succ]
    rw [c] at d
    convert d using 1
    change u^j*(1-u)^k/((j.factorial:ℂ)*(k.factorial:ℂ))*_ = _
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
    have hz : (k:ℂ)+1≠0 := by exact_mod_cast (Nat.succ_ne_zero k)
    field_simp <;> ring
  · simp only [if_neg h,mul_zero]
    exact hasDerivAt_const _ _

end Springer
