import Springer.Coefficients

noncomputable section
open Function Polynomial
open scoped Polynomial
namespace Springer

theorem taylorCoeff_polynomial (p : ℂ[X]) (n : ℕ) : taylorCoeff (fun x => p.eval x) n=p.coeff n := by
  have D (k : ℕ) (P : ℂ[X]) : iteratedDeriv k (fun x => P.eval x) = fun x => (derivative^[k] P).eval x := by
    induction k generalizing P with
    | zero => ext x; simp
    | succ k ih =>
      rw [iteratedDeriv_succ',show deriv (fun x => P.eval x)=(fun x => P.derivative.eval x) from funext (fun _ => P.deriv),
        ih,Function.iterate_succ_apply]
  rw [taylorCoeff,D]
  change (derivative^[n] p).eval 0 / _ = _
  rw [←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self,nsmul_eq_mul,Nat.factorial_ne_zero]

end Springer
