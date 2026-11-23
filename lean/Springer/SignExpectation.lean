import Springer.ModelEvolution
noncomputable section
open MeasureTheory
namespace Springer

/-- The random-sign identity with an arbitrary probability space and any measurable sign. -/
theorem modelU_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (hmeas : AEStronglyMeasurable D μ) (hs : ∀ᵐ x ∂μ, D x=1 ∨ D x= -1)
    {ω : ℝ} (hmean : ∫ x, D x ∂μ=ω) {t : ℝ} (ht : 0<t) (u : ℝ) (m : ℕ) :
    HasDerivAt (fun s : ℝ => modelU (u:ℂ) (s:ℂ) m)
      ((∫ x, reciprocalKernel (modelProfile 1 (t:ℂ)) ((Real.sqrt t:ℂ)*(D x:ℂ)) u m ∂μ) -
       ((ω:ℂ)*u/(Real.sqrt t:ℂ))*timesX (modelU (u:ℂ) (t:ℂ)) m) t := by
  let A := reciprocalKernel (modelProfile 1 (t:ℂ)) (Real.sqrt t) u m
  let B := reciprocalKernel (modelProfile 1 (t:ℂ)) (-(Real.sqrt t:ℂ)) u m
  have hd : Integrable D μ := by
    apply (integrable_const (μ:=μ) (1:ℝ)).mono' hmeas
    filter_upwards [hs] with x hx
    rcases hx with h|h <;> simp [h]
  have e : (∫ x, reciprocalKernel (modelProfile 1 (t:ℂ)) ((Real.sqrt t:ℂ)*(D x:ℂ)) u m ∂μ) =
      ((1+(ω:ℂ))/2)*A+((1-(ω:ℂ))/2)*B := by
    calc
      _ = ∫ x, ((A+B)/2)+(D x:ℂ)*((A-B)/2) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hs] with x hx
        rcases hx with h|h
        · rw [h,Complex.ofReal_one,mul_one,one_mul]; change A=_; ring
        · rw [h,Complex.ofReal_neg,Complex.ofReal_one,mul_neg_one,neg_one_mul]; change B=_; ring
      _ = _ := by rw [integral_add (integrable_const _) (hd.ofReal.mul_const _),
          integral_const,integral_mul_const,integral_complex_ofReal,hmean]; simp; ring
  rw [e]
  exact modelU_sign_deriv t ht u ω m

end Springer
