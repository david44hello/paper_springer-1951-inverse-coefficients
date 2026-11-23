import Springer.ResidueFunctional
noncomputable section
open Finset PowerSeries
namespace Springer

/-- Every coefficient is an actual multivariate polynomial in u and the first
m+1 Laurent coefficients. The variable none represents u. -/
private def genericProfile (m : ℕ) : PowerSeries (MvPolynomial (Option (Fin (m+1))) ℂ) :=
  PowerSeries.mk fun j => if h : j < m+1 then MvPolynomial.X (some ⟨j,h⟩) else 0

def residuePolynomial (m : ℕ) : MvPolynomial (Option (Fin (m+1))) ℂ :=
  let U := MvPolynomial.X (R:=ℂ) (none : Option (Fin (m+1)))
  ∑ j∈range (m+1), U^j*(1-U)^(m-j) *
    MvPolynomial.C ((j.factorial*((m-j+1).factorial:ℂ))⁻¹)*shiftedResidue (genericProfile m) j (m-j)

theorem residuePolynomial_eval (H : PowerSeries ℂ) (u : ℂ) (m : ℕ) :
    MvPolynomial.eval (fun i : Option (Fin (m+1)) => i.elim u (fun k => H.coeff k))
      (residuePolynomial m)=functionalCoeff H u m := by
  let f := MvPolynomial.eval (fun i : Option (Fin (m+1)) => i.elim u (fun k => H.coeff k))
  have base (j : ℕ) (hj : j ≤ m) : f ((genericProfile m).coeff j) = H.coeff j := by
    simp [genericProfile,f,hj]
  have power (n : ℕ) : ∀ j ≤ m, f (((genericProfile m)^n).coeff j)=(H^n).coeff j := by
    induction n with
    | zero =>
      intro j hj
      simp only [pow_zero,coeff_one]
      split_ifs <;> simp
    | succ n ih =>
      intro j hj
      simp only [pow_succ,coeff_mul,map_sum,map_mul]
      apply sum_congr rfl
      intro k hk
      have h := mem_antidiagonal.mp hk
      rw [ih _ (by omega),base _ (by omega)]
  unfold residuePolynomial functionalCoeff
  simp only [map_sum,map_mul,map_pow,map_sub,map_one,MvPolynomial.eval_X,MvPolynomial.eval_C,
    Option.elim_none,div_eq_mul_inv]
  apply sum_congr rfl
  intro j hj
  congr 1
  change f (shiftedResidue (genericProfile m) j (m-j))=shiftedResidue H j (m-j)
  unfold shiftedResidue
  split_ifs
  · exact power _ _ (by have := mem_range.mp hj; omega)
  · exact map_zero _
end Springer
