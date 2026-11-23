import Springer.ContourFlow
import Springer.Coefficients

noncomputable section
open Set MeasureTheory Complex Metric Filter
open scoped Real Topology
namespace Springer

def contourWeight (R : ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  (2*π*I:ℂ)⁻¹ * deriv (circleMap 0 R) θ / (circleMap 0 R θ)^(n+1)

def angleMeasure : Measure ℝ := volume.restrict (Icc 0 (2*π))

noncomputable instance : IsFiniteMeasure angleMeasure := by
  unfold angleMeasure
  exact isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne

/-- The exact Taylor normalization as a bounded linear functional of the values
on any positive-radius circle inside the disk of analyticity. -/
theorem taylorCoeff_contour {R : ℝ} (hR : 0<R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R)) (n : ℕ) :
    taylorCoeff f n=∫ θ, contourWeight R n θ * f (circleMap 0 R θ) ∂angleMeasure := by
  have hc := hf.circleIntegral_one_div_sub_center_pow_smul hR n
  rw [circleIntegral_def_Icc] at hc
  simp only [sub_zero,smul_eq_mul] at hc
  have hn : ((n.factorial:ℕ):ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  calc
    _ = (2*π*I:ℂ)⁻¹*((2*π*I/(n.factorial:ℂ))*iteratedDeriv n f 0) := by
      unfold taylorCoeff
      field_simp [two_pi_I_ne_zero,hn]
    _ = _ := by
      rw [←hc,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with θ
      dsimp [contourWeight]
      ring

/-- A time primitive on each contour point gives the true Taylor coefficient
increment. The initial value and each later slice have the same contour radius. -/
theorem taylorCoeff_increment {R s t : ℝ} (hR : 0<R) (hst : s≤t)
    (f V : ℝ → ℂ → ℂ) (hs : DiffContOnCl ℂ (f s) (ball 0 R))
    (ht : DiffContOnCl ℂ (f t) (ball 0 R)) (n : ℕ)
    (hsI : Integrable (fun θ => contourWeight R n θ*f s (circleMap 0 R θ)) angleMeasure)
    (htI : Integrable (fun θ => contourWeight R n θ*f t (circleMap 0 R θ)) angleMeasure)
    (hprod : Integrable (fun p : ℝ × ℝ => contourWeight R n p.1*V p.2 (circleMap 0 R p.1))
      (angleMeasure.prod (volume.restrict (Ioc s t))))
    (hinc : ∀ θ, f t (circleMap 0 R θ)-f s (circleMap 0 R θ)=
      ∫ v : ℝ in s..t, V v (circleMap 0 R θ)) :
    taylorCoeff (f t) n-taylorCoeff (f s) n =
      ∫ v : ℝ in s..t, ∫ θ, contourWeight R n θ*V v (circleMap 0 R θ) ∂angleMeasure := by
  rw [taylorCoeff_contour hR ht,taylorCoeff_contour hR hs]
  exact contour_increment angleMeasure hst (contourWeight R n)
    (fun x θ => f x (circleMap 0 R θ)) (fun x θ => V x (circleMap 0 R θ)) hsI htI hprod hinc

end Springer
