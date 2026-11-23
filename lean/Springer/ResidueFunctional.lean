import Springer.Basic

noncomputable section
open Finset PowerSeries
namespace Springer

/-- The stored power series h(t) represents H(w)=t h(t) in t=1/w.
The Laurent residue of w^j H^(l+1) uses degree j-l. -/
def shiftedResidue {R : Type*} [CommSemiring R] (H : PowerSeries R) (j l : ℕ) : R :=
  if l≤j then (H^(l+1)).coeff (j-l) else 0

/-- Coefficient of x^m in the manuscript's exponential residue. -/
def functionalCoeff {R : Type*} [Field R] (H : PowerSeries R) (u : R) (m : ℕ) :=
  ∑ j ∈ range (m+1), u^j*(1-u)^(m-j)/(j.factorial*((m-j+1).factorial:R))*shiftedResidue H j (m-j)

theorem functional_one {R : Type*} [Field R] [CharZero R] (H : PowerSeries R) (m : ℕ) :
    functionalCoeff H 1 m=H.coeff m/m.factorial := by
  unfold functionalCoeff
  rw [sum_eq_single m]
  · simp [shiftedResidue,div_eq_mul_inv,mul_comm]
  · intro j hj hne
    have hn : m-j≠0 := by have := mem_range.mp hj; omega
    simp [hn]
  · simp

theorem functional_zero {R : Type*} [Field R] [CharZero R] (H : PowerSeries R) (m : ℕ) :
    functionalCoeff H 0 m=if m=0 then H.coeff 0 else 0 := by
  unfold functionalCoeff
  rw [sum_eq_single 0]
  · cases m <;> simp [shiftedResidue]
  · intro j _ hn; simp [hn]
  · simp

theorem functional_degree_zero {R : Type*} [Field R] [CharZero R] (H : PowerSeries R) (u : R) :
    functionalCoeff H u 0=H.coeff 0 := by simp [functionalCoeff,shiftedResidue]

private theorem pow_coeff_mono {H G : PowerSeries ℝ}
    (hG : ∀ j, 0≤G.coeff j) (hHG : ∀ j, G.coeff j≤H.coeff j) (p : ℕ) :
    ∀ j, 0≤(G^p).coeff j ∧ (G^p).coeff j≤(H^p).coeff j := by
  induction p with
  | zero => intro j; simp [PowerSeries.coeff_one]; split_ifs <;> simp
  | succ p ih =>
    intro j
    simp only [pow_succ,PowerSeries.coeff_mul]
    exact ⟨sum_nonneg fun a _ => mul_nonneg (ih a.1).1 (hG _),
      sum_le_sum fun a _ => mul_le_mul (ih a.1).2 (hHG _) (hG _) ((ih _).1.trans (ih _).2)⟩

theorem functional_mono {H G : PowerSeries ℝ} {u : ℝ} (hu : u∈Set.Icc 0 1)
    (hG : ∀ j, 0≤G.coeff j) (hHG : ∀ j, G.coeff j≤H.coeff j) (m : ℕ) :
    0≤functionalCoeff G u m ∧ functionalCoeff G u m≤functionalCoeff H u m := by
  have sh (j l : ℕ) : 0≤ shiftedResidue G j l ∧ shiftedResidue G j l≤ shiftedResidue H j l := by
    unfold shiftedResidue
    split_ifs
    · exact pow_coeff_mono hG hHG _ _
    · simp
  have h₀ := hu.1
  have h₁ := sub_nonneg.mpr hu.2
  exact ⟨sum_nonneg fun j _ => mul_nonneg (by positivity) (sh j _).1,
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (sh j _).2 (by positivity)⟩

/-- An odd Laurent series has zero even Laurent coefficients, so its normalized
profile h(t)=H(1/t)/t has zero odd Taylor coefficients. -/
theorem functional_odd_input {R : Type*} [Field R] (H : PowerSeries R) (h : ∀ j, Odd j → H.coeff j=0)
    (u : R) {m : ℕ} (hm : Odd m) : functionalCoeff H u m=0 := by
  have Hpow (p : ℕ) : ∀ j, Odd j → (H^p).coeff j=0 := by
    induction p with
    | zero => intro j hj; simp [PowerSeries.coeff_one,show j≠0 by obtain ⟨k,hk⟩ := hj; omega]
    | succ p ih =>
      intro j hj
      rw [pow_succ,PowerSeries.coeff_mul]
      apply sum_eq_zero; intro a ha
      have he := HasAntidiagonal.mem_antidiagonal.mp ha
      by_cases h₁ : Odd a.1
      · rw [ih _ h₁,zero_mul]
      · have h₂ : Odd a.2 := by grind [Nat.odd_iff]
        rw [h _ h₂,mul_zero]
  apply sum_eq_zero
  intro j hj
  unfold shiftedResidue
  split_ifs with hle
  · have jle := Nat.le_of_lt_succ (mem_range.mp hj)
    have hh : Odd (j-(m-j)) := by rw [Nat.odd_iff] at hm ⊢; omega
    rw [Hpow _ _ hh,mul_zero]
  · rw [mul_zero]

/-- Coefficient of x^m in res exp(x*(u*w+(1-u)*H(w))).
The index j counts w-factors. In t=1/w the remaining m-j factors each
contribute t times the stored power series. -/
def expResidue {R : Type*} [Field R] (H : PowerSeries R) (u : R) (m : ℕ) :=
  ∑ j∈range (m+1), u^j*(1-u)^(m-j)/(j.factorial*((m-j).factorial:R))*
    (if m-j≤j+1 then (H^(m-j)).coeff (j+1-(m-j)) else 0)

theorem expResidue_zero {R : Type*} [Field R] [CharZero R] (H : PowerSeries R) (u : R) :
    expResidue H u 0=0 := by simp [expResidue,PowerSeries.coeff_one]

theorem expResidue_succ {R : Type*} [Field R] (H : PowerSeries R) (u : R) (m : ℕ) :
    expResidue H u (m+1)=(1-u)*functionalCoeff H u m := by
  rw [expResidue,Finset.sum_range_succ,functionalCoeff,Finset.mul_sum]
  simp only [Nat.sub_self,pow_zero,PowerSeries.coeff_one,show m+1+1≠0 by omega,
    ite_false,ite_self,Nat.sub_zero,mul_zero,add_zero]
  apply sum_congr rfl
  intro j hj
  have he : j≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hsub : m+1-j=(m-j)+1 := by omega
  simp only [hsub,Nat.add_le_add_iff_right,Nat.add_sub_add_right,shiftedResidue,pow_succ (1-u)]
  ring

end Springer
