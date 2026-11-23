import Springer.ShiftedKernel
import Springer.FunctionalRegularity

noncomputable section
open Complex Finset
open scoped ComplexConjugate
namespace Springer

/-- Differentiating exp(a(t)x) times a varying coefficient sequence. -/
theorem expShift_deriv {a : ℝ → ℂ} {d : ℂ} {t : ℝ} (ha : HasDerivAt a d t)
    {A : ℝ → ℕ → ℂ} {D : ℕ → ℂ} (hA : ∀ k, HasDerivAt (fun x => A x k) (D k) t) (m : ℕ) :
    HasDerivAt (fun x => expShift (a x) (A x) m)
      (d*expShift (a t) (timesX (A t)) m + expShift (a t) D m) t := by
  let T := fun j : ℕ => (j:ℂ)*a t^(j-1)*d/(j.factorial:ℂ)*A t (m-j)
  have hterm (j : ℕ) : HasDerivAt (fun x => a x^j/(j.factorial:ℂ)*A x (m-j))
      (T j + a t^j/(j.factorial:ℂ)*D (m-j)) t := by
    exact ((ha.pow j).div_const _).mul (hA _)
  apply (HasDerivAt.fun_sum (u:=range (m+1)) (fun i _ => hterm i)).congr_deriv
  rw [sum_add_distrib]
  congr 1
  dsimp only [T]
  cases m with
  | zero => simp [timesX,expShift]
  | succ m =>
    rw [sum_range_succ' (n:=m+1), expShift, sum_range_succ (n:=m+1)]
    simp only [Nat.cast_zero,zero_mul,zero_div,add_zero,Nat.sub_self,timesX,mul_zero]
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
    have hz : (j:ℂ)+1≠0 := by exact_mod_cast (Nat.succ_ne_zero j)
    rw [show m+1-j=(m-j)+1 by omega]
    simp [Nat.factorial_succ,Nat.cast_succ,timesX,hz]
    <;> field_simp <;> ring

/-- Squared distance has a derivative even when the moving center is zero. -/
theorem radius_sq_hasDeriv {Z : ℝ → ℂ} {t : ℝ} {v : ℂ} {b : ℝ}
    (hZ : HasDerivAt Z ((b:ℂ)*v) t) :
    HasDerivAt (fun s => ‖Z s‖^2) (2*‖Z t‖*(b*chordDirection (Z t) v)) t := by
  apply hZ.norm_sq.congr_deriv
  rw [Complex.inner, mul_assoc, mul_comm v (conj (Z t))]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  by_cases hz : Z t=0
  · simp [hz,chordDirection]
  · unfold chordDirection
    simp only [Complex.mul_re]
    field_simp [norm_ne_zero_iff.mpr hz]

/-- The real polynomial in time and squared radius can be differentiated along a
linear radius with the same squared-radius tangent. -/
theorem comparison_tangent_transfer {Z : ℝ → ℂ} {t d u : ℝ} (n : ℕ)
    (hq : HasDerivAt (fun x => ‖Z x‖^2) (2*‖Z t‖*d) t)
    (hU : ∀ m, DifferentiableAt ℝ (fun x => modelU u x m) t)
    (hV : DifferentiableAt ℝ (fun x => modelV u x (2*n)) t)
    {L : ℝ} (hline : HasDerivAt (fun x => comparisonPolynomial u x n ((‖Z t‖+d*(x-t))^2)) L t) :
    HasDerivAt (fun x => comparisonPolynomial u x n (‖Z x‖^2)) L t := by
  let Q := fun p : ℝ × ℝ => comparisonPolynomial u p.1 n p.2
  have hQ : DifferentiableAt ℝ Q (t,‖Z t‖^2) := by
    have hfst : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1) (t,‖Z t‖^2) := differentiableAt_fst
    have hterm (k : ℕ) := (hU k).comp (t,‖Z t‖^2) (f:=Prod.fst) hfst
    unfold Q comparisonPolynomial
    apply DifferentiableAt.sub
    · apply DifferentiableAt.fun_sum; intro k hk
      apply DifferentiableAt.mul
      · simp only [div_eq_mul_inv]
        exact (hterm (2*(n-k))).mul (differentiableAt_const _)
      · exact differentiableAt_snd.pow _
    · exact hV.comp (t,‖Z t‖^2) (f:=Prod.fst) hfst
  have hp : HasDerivAt (fun x : ℝ => ‖Z t‖+d*(x-t)) d t := by
    simpa using (((hasDerivAt_id t).sub_const t).const_mul d).const_add ‖Z t‖
  have pq : HasDerivAt (fun x => (‖Z t‖+d*(x-t))^2) (2*‖Z t‖*d) t := by
    simpa [Pi.pow_def] using hp.pow 2
  have pair := (hasDerivAt_id t).prodMk hq
  have lin := (hasDerivAt_id t).prodMk pq
  have h₁ := hQ.hasFDerivAt.comp_hasDerivAt t pair
  have h₂ := hQ.hasFDerivAt.comp_hasDerivAt_of_eq t lin (by simp)
  apply h₁.congr_deriv
  exact h₂.unique hline

end Springer
