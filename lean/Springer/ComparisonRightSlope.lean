import Springer.ComparisonBranches

noncomputable section
open Complex Finset MeasureTheory
namespace Springer

private theorem expShift_linear_three (r p q d : ℂ) (A B T : ℕ → ℂ) (m : ℕ) :
    expShift r (fun j => p*A j+q*B j-d*T j) m =
      p*expShift r A m+q*expShift r B m-d*expShift r T m := by
  unfold expShift
  simp only [mul_sum,←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intros; ring

/-- The derivative of the upper bound for the true squared radius, including zeros of c-uP. -/
theorem comparisonBound_hasDeriv {P : ℝ → ℂ} (μ : Measure Circle) {t : ℝ} (ht : 0<t)
    (u : ℝ) (c : ℂ) (n : ℕ)
    (hP : HasDerivAt P (-(∫ ξ : Circle, (ξ:ℂ) ∂μ)/(Real.sqrt t:ℂ)) t) :
    HasDerivAt (fun x => comparisonBound (P x) u x c (n+1))
      (comparisonUpperSlope μ (P t) c u t n) t := by
  let Z := fun x => c-(u:ℂ)*P x
  let b := Real.sqrt t
  let mean := ∫ ξ : Circle, (ξ:ℂ) ∂μ
  let r := ‖Z t‖
  let ω := chordDirection (Z t) mean
  let d := ω*u/b
  let l := fun x : ℝ => r+d*(x-t)
  let p : ℂ := (1+(ω:ℂ))/2
  let q : ℂ := (1-(ω:ℂ))/2
  let U := fun x : ℝ => modelU (u:ℂ) (x:ℂ)
  let V := fun j => reciprocalKernel (modelProfile (1/2) (t:ℂ)) 0 u j
  let K := fun a : ℝ => reciprocalKernel (modelProfile 1 (t:ℂ)) (a:ℂ) u
  let m := 2*(n+1)
  have hl : HasDerivAt l d t := by
    simpa [l] using (((hasDerivAt_id t).sub_const t).const_mul d).const_add r
  have hl0 : l t = r := by simp [l]
  have hsum : p+q=1 := by dsimp [p,q]; ring
  have hz' : HasDerivAt Z (((u/b:ℝ):ℂ)*mean) t := by
    apply ((hP.const_mul (u:ℂ)).const_sub c).congr_deriv
    dsimp [mean,b]; push_cast; ring
  have hsq : HasDerivAt (fun x => ‖Z x‖^2) (2*‖Z t‖*d) t := by
    apply (radius_sq_hasDeriv hz').congr_deriv
    dsimp [d,ω]; ring
  have hu (j : ℕ) : HasDerivAt (fun x => U x j)
      (p*K b j+q*K (-b) j-(d:ℂ)*timesX (U t) j) t := by
    simpa [U,K,b,p,q,d,Complex.ofReal_neg] using modelU_sign_deriv t ht u ω j
  have hv (j : ℕ) : HasDerivAt (fun x : ℝ => modelV (u:ℂ) (x:ℂ) j) (V j) t :=
    (modelV_hasDeriv u (t:ℂ) j).comp_ofReal
  have du (j : ℕ) : DifferentiableAt ℝ (fun x => modelU u x j) t := by
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hu j)
    simpa [Function.comp_def,U,modelU_ofReal] using hh.differentiableAt
  have dv : DifferentiableAt ℝ (fun x => modelV u x m) t := by
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hv m)
    simpa [Function.comp_def,modelV_ofReal] using hh.differentiableAt
  apply comparison_tangent_transfer (n+1) hsq du dv
  have h := (expShift_deriv hl.ofReal_comp hu m).sub (hv m)
  have hh : HasDerivAt (fun x => expShift (l x:ℂ) (U x) m - modelV (u:ℂ) (x:ℂ) m)
      ((comparisonUpperSlope μ (P t) c u t n):ℂ) t := by
    apply h.congr_deriv
    rw [hl0,expShift_linear_three]
    calc
      _ = p*(expShift (r:ℂ) (K b) m-V m)+q*(expShift (r:ℂ) (K (-b)) m-V m) := by
        linear_combination V m * hsum
      _ = p*(comparisonBranch u t r b n:ℂ)+q*(comparisonBranch u t r (-b) n:ℂ) := by
        dsimp only [m,K,V]
        rw [show 2*(n+1)=2*n+2 by omega,comparisonBranch_complex,comparisonBranch_complex]
      _ = _ := by
        have hsign := congrArg Complex.ofReal (signAverage_branches μ (P t) c u t n)
        simpa [signAverage,p,q,r,ω,b,Z,mean] using hsign
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hh
  have eU (x : ℝ) : U x = fun j => ((modelU u x j:ℝ):ℂ) := funext (modelU_ofReal u x)
  change HasDerivAt (fun x => (expShift (l x:ℂ) (U x) m - modelV (u:ℂ) (x:ℂ) m).re)
    (comparisonUpperSlope μ (P t) c u t n) t at hre
  simp only [eU,expShift_ofReal,modelV_ofReal,Complex.sub_re,Complex.ofReal_re] at hre
  simpa only [comparisonPolynomial_sq,l,r,m] using hre

end Springer
