import Springer.ArcMap
import Springer.Residue
import Springer.PolynomialCoeff

noncomputable section
open Set Filter Function Complex Finset
open scoped Topology
namespace Springer

private def arcTaylor : Polynomial ℂ := Polynomial.C 3*Polynomial.X^5+Polynomial.C (21/8)*Polynomial.X^4+
    Polynomial.C (-3/2)*Polynomial.X^3+Polynomial.C (-3)*Polynomial.X^2+1

private theorem arcTaylor_five : arcTaylor.coeff 5=3 := by
  norm_num [arcTaylor,Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_one]

private def arcRemainder (t : ℂ) := -3*(16*t^3-141*t^2+192*t-56)/(4-2*t)^4

private theorem arcRemainder_analytic : AnalyticAt ℂ arcRemainder 0 := by
  unfold arcRemainder; fun_prop (disch := norm_num)

private theorem arcTaylor_identity {t : ℂ} (hn : ‖t‖<1) :
    profile arcMap t^4 = arcTaylor.eval t+t^6*arcRemainder t := by
  have hden : 4-2*t≠0 := by
    intro he; have hh : t=2 := by linear_combination -he/2
    rw [hh] at hn; norm_num at hn
  rw [arc_profile t hn]; unfold arcTaylor arcProfile arcRemainder
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one]
  generalize e : (4:ℂ)-2*t=d at hden ⊢
  field_simp [hden]; rw [←e]; ring

/-- Direct extraction from the fourth power of the forward profile. -/
theorem arc_fourth_residue : taylorCoeff (fun t => profile arcMap t^4) 5=3 := by
  let P := fun t => arcTaylor.eval t
  have hP : AnalyticAt ℂ P 0 := by dsimp [P,arcTaylor]; simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one]; fun_prop
  have E : (fun t => profile arcMap t^4)=ᶠ[𝓝 (0:ℂ)] fun t => P t+t^6*arcRemainder t := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) zero_lt_one] with t ht using arcTaylor_identity (by simpa using ht)
  have hs : taylorCoeff (fun t : ℂ => t^6*arcRemainder t) 5=0 := by
    simpa only [if_neg (by decide : ¬6≤5)] using taylorCoeff_shift arcRemainder_analytic 6 5
  have hsum := taylorCoeff_add (f:=P) (g:=fun t : ℂ => t^6*arcRemainder t) hP ((analyticAt_id.pow 6).mul arcRemainder_analytic) 5
  exact (taylorCoeff_congr E 5).trans (hsum.trans (by rw [hs,add_zero]; exact (taylorCoeff_polynomial arcTaylor 5).trans arcTaylor_five))

/-- Theorem 1.4(a) with the actual inverse coefficient and both arc endpoints. -/
theorem even_four :
    Sigma arcMap ∧ arcMap '' exterior=circularArcᶜ ∧
      ‖inverseCoeff arcMap 4‖=3/4 ∧ sigmaBound 4=2/5 ∧ sigmaBound 4<‖inverseCoeff arcMap 4‖ := by
  have H := inverse_residue arcMap_sigma (by decide : 4≠0)
  rw [arc_fourth_residue] at H
  norm_num only [Nat.cast_ofNat] at H
  have hv : inverseCoeff arcMap 4= -3/4 := by linear_combination H/4
  have hn : ‖inverseCoeff arcMap 4‖=3/4 := by rw [hv]; norm_num [norm_div]
  have hs : sigmaBound 4=2/5 := by norm_num [sigmaBound,realBinom,Finset.prod_range_succ]
  exact ⟨arcMap_sigma,arcMap_image,hn,hs,by rw [hn,hs]; norm_num⟩

end Springer
