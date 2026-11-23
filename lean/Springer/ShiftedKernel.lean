import Springer.Comparison
import Springer.ModelEvolution

noncomputable section
open Set Finset PowerSeries MeasureTheory
namespace Springer

private def expSeries (c : ℂ) := rescale c (PowerSeries.exp ℂ)

private theorem expSeries_coeff (c : ℂ) (m : ℕ) :
    (expSeries c).coeff m = c^m/m.factorial := by
  simp [expSeries, coeff_rescale, coeff_exp, div_eq_mul_inv]

theorem expShift_as_coeff (c : ℂ) (F : ℕ → ℂ) (m : ℕ) :
    expShift c F m=(expSeries c * PowerSeries.mk F).coeff m := by
  simp only [expShift, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    expSeries_coeff,coeff_mk]

private theorem shift_series (c : ℂ) (F : ℕ → ℂ) :
    PowerSeries.mk (expShift c F)=expSeries c*PowerSeries.mk F := by
  ext m
  rw [coeff_mk,expShift_as_coeff]

theorem expShift_add_arg (c b : ℂ) (F : ℕ → ℂ) (m : ℕ) :
    expShift c (expShift b F) m=expShift (c+b) F m := by
  rw [expShift_as_coeff, shift_series, ←mul_assoc, expShift_as_coeff (c+b)]
  rw [show expSeries c*expSeries b=expSeries (c+b) from exp_mul_exp_eq_exp_add c b]

private def kernelIntegral (H : PowerSeries ℂ) (a : ℂ) (u : ℝ) (m : ℕ) :=
  ∫ v : ℝ in 0..u, (1-(v:ℂ))*exponentialConvolution H (((u:ℂ)-v)*a) v m

private theorem kernel_series (H : PowerSeries ℂ) (a : ℂ) (u : ℝ) :
    PowerSeries.mk (reciprocalKernel H a u)=expSeries ((u:ℂ)*a) +
      PowerSeries.mk (kernelIntegral H a u)*X^2 := by
  ext m
  rw [coeff_mk,map_add,expSeries_coeff]
  cases m with
  | zero => simp [reciprocalKernel,coeff_mul_X_pow']
  | succ k =>
    cases k with
    | zero => simp [reciprocalKernel,coeff_mul_X_pow']
    | succ n => rw [coeff_mul_X_pow _ 2 n, coeff_mk]; rfl

theorem shifted_reciprocalKernel (H : PowerSeries ℂ) (a c : ℂ) (u : ℝ) (n : ℕ) :
    expShift c (reciprocalKernel H a u) (n+2)=
      (c+(u:ℂ)*a)^(n+2)/(n+2).factorial +
      ∫ v : ℝ in 0..u, (1-(v:ℂ))*exponentialConvolution H (c+((u:ℂ)-v)*a) v n := by
  rw [expShift_as_coeff,kernel_series,mul_add,←mul_assoc (expSeries c) _ (X^2),map_add,
    show expSeries c * expSeries ((u:ℂ)*a) = expSeries (c+(u:ℂ)*a) from exp_mul_exp_eq_exp_add _ _,
    expSeries_coeff, coeff_mul_X_pow,←expShift_as_coeff]
  congr 1
  unfold expShift kernelIntegral
  simp only [←intervalIntegral.integral_const_mul]
  rw [←intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro v hv
    change (∑ k ∈ range (n+1), c^k/(k.factorial:ℂ)*((1-(v:ℂ))*
      expShift (((u:ℂ)-v)*a) (functionalCoeff H (v:ℂ)) (n-k))) =
        (1-(v:ℂ))*expShift (c+((u:ℂ)-v)*a) (functionalCoeff H (v:ℂ)) n
    rw [←expShift_add_arg,expShift,mul_sum]
    apply sum_congr rfl
    intro k hk
    ring
  · intro k hk
    apply Continuous.intervalIntegrable
    unfold exponentialConvolution functionalCoeff
    fun_prop

theorem expShift_circle_integral (μ : Measure Circle) [IsProbabilityMeasure μ]
    (c : ℂ) (F : ℕ → Circle → ℂ) (m : ℕ) (hF : ∀ j ≤ m, Integrable (F j) μ) :
    expShift c (fun j => ∫ ξ, F j ξ ∂μ) m =
      ∫ ξ, expShift c (fun j => F j ξ) m ∂μ := by
  unfold expShift
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro k hk
    exact (hF _ (Nat.sub_le _ _)).const_mul _

end Springer
