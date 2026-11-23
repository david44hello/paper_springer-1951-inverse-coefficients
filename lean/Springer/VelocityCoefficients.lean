import Springer.ReciprocalResidue
import Springer.Coefficients

noncomputable section
open Finset PowerSeries Set Filter Complex
open scoped Topology
namespace Springer

/-- In the reciprocal variable y, the exterior remainder is R(y)=P−yH(y). -/
def storedRemainder (R : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => -taylorCoeff R (k+1))

private def seriesAtZero (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (taylorCoeff f)

private theorem seriesAtZero_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    seriesAtZero (fun y => f y*g y)=seriesAtZero f*seriesAtZero g := by
  ext n
  simp only [seriesAtZero, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    coeff_mk,taylorCoeff_mul hf hg]

private theorem seriesAtZero_const (c : ℂ) :
    seriesAtZero (fun _ => c) = C c := by
  ext n
  cases n <;> simp [seriesAtZero,taylorCoeff,iteratedDeriv_const,coeff_C]

private theorem seriesAtZero_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    seriesAtZero (fun y => f y+g y)=seriesAtZero f+seriesAtZero g := by
  ext n; simp only [map_add,seriesAtZero,coeff_mk,taylorCoeff_add hf hg]

private theorem seriesAtZero_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    seriesAtZero (fun y => f y-g y)=seriesAtZero f-seriesAtZero g := by
  ext n; simp only [map_sub,seriesAtZero,coeff_mk,taylorCoeff_sub hf hg]

private theorem seriesAtZero_id : seriesAtZero (fun y : ℂ => y) = X := by
  ext n
  have h := taylorCoeff_pow n 1
  simpa only [seriesAtZero,coeff_mk,pow_one,coeff_X] using h

private theorem seriesAtZero_split (R : ℂ → ℂ) :
    seriesAtZero R = C (R 0) - X*storedRemainder R := by
  ext n
  cases n with
  | zero => simp [seriesAtZero]
  | succ k => simp [seriesAtZero,storedRemainder,coeff_C,coeff_succ_X_mul]

/-- The exact reciprocal denominator in the analytic coordinate has the formal
coefficients used by the evolution, including its sign and index shift. -/
theorem analytic_velocity_reciprocal {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0) (p : ℂ) (j : ℕ) :
    taylorCoeff (fun y => (1+y*(R y-p))⁻¹) j =
      (reciprocalDirection (storedRemainder R) (p-R 0)).coeff j := by
  let d := fun y : ℂ => 1+y*(R y-p)
  have hd : AnalyticAt ℂ d 0 := analyticAt_const.add (analyticAt_id.mul (hR.sub analyticAt_const))
  have h₀ : d 0≠0 := by simp [d]
  have hD : seriesAtZero d=reciprocalDenom (storedRemainder R) (p-R 0) := by
    unfold d
    rw [seriesAtZero_add (f:=fun _ => 1) (g:=fun y => y*(R y-p)) analyticAt_const (analyticAt_id.mul (hR.sub analyticAt_const)),
      seriesAtZero_const, seriesAtZero_mul (f:=fun y => y) (g:=fun y => R y-p) analyticAt_id (hR.sub analyticAt_const),
      seriesAtZero_id, seriesAtZero_sub (f:=R) (g:=fun _ => p) hR analyticAt_const, seriesAtZero_const,seriesAtZero_split]
    simp only [reciprocalDenom,map_one,map_sub]
    ring
  have hprod : seriesAtZero (fun y => (d y)⁻¹) * seriesAtZero d = 1 := by
    rw [←seriesAtZero_mul (f:=fun y => (d y)⁻¹) (g:=d) (hd.inv h₀) hd]
    have he : (fun y => (d y)⁻¹ * d y) =ᶠ[𝓝 0] fun _ => 1 :=
      (hd.continuousAt.eventually_ne h₀).mono (fun y hy => inv_mul_cancel₀ hy)
    have e : seriesAtZero (fun y => (d y)⁻¹*d y)=seriesAtZero (fun _ => 1) := by
      ext n; simpa only [seriesAtZero,coeff_mk] using taylorCoeff_congr he n
    rw [e,seriesAtZero_const,map_one]
  rw [hD] at hprod
  have eqn : seriesAtZero (fun y => (d y)⁻¹)=reciprocalDirection (storedRemainder R) (p-R 0) :=
    (PowerSeries.eq_inv_iff_mul_eq_one (by simp [reciprocalDenom])).mpr hprod
  simpa only [seriesAtZero,coeff_mk,d] using congrArg (PowerSeries.coeff j) eqn

/-- The real-time velocity is negative; H is minus the negative-order part of
the inverse-map remainder. These signs cancel in Lemma 3.1(iii). -/
def reciprocalVelocity (R : ℂ → ℂ) (a : ℂ) (ξ : Circle) (y : ℂ) :=
  -(ξ:ℂ)/a - (ξ:ℂ)^2*(y*(1+y*(R y-a*ξ))⁻¹)

theorem reciprocalVelocity_coeff {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0) (a : ℂ) (ξ : Circle) (j : ℕ) :
    taylorCoeff (reciprocalVelocity R a ξ) (j+1) =
      -(ξ:ℂ)^2*(reciprocalDirection (storedRemainder R) (a*ξ-R 0)).coeff j := by
  let d := fun y : ℂ => 1+y*(R y-a*ξ)
  have hd : AnalyticAt ℂ d 0 := analyticAt_const.add (analyticAt_id.mul (hR.sub analyticAt_const))
  have hi : AnalyticAt ℂ (fun y => (d y)⁻¹) 0 := hd.inv (by simp [d])
  have h := taylorCoeff_shift hi 1 (j+1)
  simp only [pow_one,show 1≤j+1 by omega,ite_true,Nat.add_sub_cancel] at h
  unfold reciprocalVelocity
  rw [taylorCoeff_sub (f:=fun _ => -(ξ:ℂ)/a) (g:=fun y => (ξ:ℂ)^2*(y*(d y)⁻¹))
    analyticAt_const (analyticAt_const.mul (analyticAt_id.mul hi)),
    taylorCoeff_const_mul]
  change taylorCoeff (fun _ : ℂ => -(ξ:ℂ)/a) (j+1) - (ξ:ℂ)^2*
    taylorCoeff (fun y => y*(d y)⁻¹) (j+1) = _
  rw [h, show taylorCoeff (fun _ : ℂ => -(ξ:ℂ)/a) (j+1)=0 by simp [taylorCoeff,iteratedDeriv_const]]
  rw [show taylorCoeff (fun y => (d y)⁻¹) j=_ from analytic_velocity_reciprocal hR (a*ξ) j]
  ring

end Springer
