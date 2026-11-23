import Springer.ModelSeries
import Springer.FunctionalDerivative
noncomputable section
open PowerSeries
namespace Springer

private def parameterSlope (b τ : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun j => deriv (fun s => (modelProfile b s).coeff j) τ)

private theorem profile_slope (b τ : ℂ) : CoeffDerivAt (modelProfile b) (parameterSlope b τ) τ := by
  intro j
  rw [parameterSlope,coeff_mk]
  apply DifferentiableAt.hasDerivAt
  rcases Nat.even_or_odd j with ⟨k,rfl⟩|ho
  · simp_rw [←two_mul,modelProfile_even]
    fun_prop
  · simp only [modelProfile_odd _ _ ho]
    fun_prop

theorem modelDenom_slope (b τ : ℂ) :
    CoeffDerivAt (modelProfile b) ((1-C (2*b)*X^2*modelProfile b τ)⁻¹) τ := by
  let P := modelProfile b τ
  let D := parameterSlope b τ
  let M : PowerSeries ℂ := C b*X^2
  let J := 1-C (2*b)*X^2*P
  have hd := profile_slope b τ
  have hm : CoeffDerivAt (fun _ : ℂ => M) 0 τ := fun j => by simpa using hasDerivAt_const τ (M.coeff j)
  have hC : CoeffDerivAt (fun s : ℂ => C s) 1 τ := by
    intro j
    by_cases h : j=0
    · subst j; simpa [coeff_C,coeff_one,id_eq] using hasDerivAt_id' τ
    · simpa [coeff_C,coeff_one,h] using hasDerivAt_const τ (0:ℂ)
  have eq : D=1+M*(D*P+P*D) := by
    ext j
    have g := (hC j).add (coeffDeriv_mul hm (coeffDeriv_mul hd hd) j)
    simp only [zero_mul,zero_add] at g
    have f : (fun s : ℂ => (modelProfile b s).coeff j) =
        (fun s : ℂ => (C s).coeff j+(M*(modelProfile b s*modelProfile b s)).coeff j) := by
      funext s
      exact (congrArg (coeff j) (modelProfile_quadratic b s)).trans (by simp [M,sq])
    have d := hd j
    rw [f] at d
    exact d.unique g
  have e : J*D=1 := by
    change (1-C (2*b)*X^2*P)*D=1
    simp only [map_mul,map_ofNat]
    change D=1+C b*X^2*(D*P+P*D) at eq
    linear_combination eq
  have h0 : J.constantCoeff≠0 := by simp [J]
  have inv := PowerSeries.inv_mul_cancel J h0
  have ed : D=J⁻¹ := by calc
    D = (J⁻¹*J)*D := by rw [inv,one_mul]
    _ = J⁻¹ := by rw [mul_assoc,e,mul_one]
  exact ed ▸ hd

end Springer
