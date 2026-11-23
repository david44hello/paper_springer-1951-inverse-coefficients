import Springer.ModelEvolution

noncomputable section
open PowerSeries Finset MeasureTheory
namespace Springer

/-- Continuity of each coefficient of the reciprocal in the pole parameter. -/
theorem reciprocal_coeff_continuous (H : PowerSeries ℂ) (n : ℕ) :
    Continuous (fun a => (reciprocalDirection H a).coeff n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    simp only [reciprocalDirection,coeff_inv n,reciprocalDenom,map_sub,map_one,map_mul,
      map_pow,constantCoeff_C,constantCoeff_X,zero_pow (by decide : 2≠0),
      mul_zero,zero_mul,sub_zero,inv_one]
    by_cases hz : n=0
    · simp [hz]; exact continuous_const
    · simp only [if_neg hz]
      apply Continuous.mul continuous_const
      apply continuous_finsetSum
      intro k _
      split_ifs with hk
      · apply Continuous.mul
        · simp only [map_sub,coeff_C_mul]; fun_prop
        · exact ih k.2 hk
      · exact continuous_const

/-- Normalized stored derivative in the circle-measure evolution. -/
def averagedDirection (H : PowerSeries ℂ) (a : Circle → ℂ) (μ : Measure Circle) : PowerSeries ℂ :=
  PowerSeries.mk fun j => ∫ ξ, (ξ:ℂ)^2*(reciprocalDirection H (a ξ)).coeff j ∂μ

theorem averagedDirection_zero (H : PowerSeries ℂ) (a : Circle → ℂ) (μ : Measure Circle) :
    (averagedDirection H a μ).coeff 0=∫ ξ, (ξ:ℂ)^2 ∂μ := by
  simp [averagedDirection,reciprocalDirection,reciprocalDenom,coeff_zero_eq_constantCoeff_apply,
    constantCoeff_inv]

/-- The chain rule applied to the coefficientwise equation in Lemma 3.1(iii). -/
theorem functional_evolution {H : ℝ → PowerSeries ℂ} {t : ℝ} (μ : Measure Circle) [IsFiniteMeasure μ]
    {a : Circle → ℂ} (ha : Continuous a) (hd : CoeffDerivAt H (averagedDirection (H t) a μ) t)
    (u : ℝ) (m : ℕ) :
    HasDerivAt (fun s => functionalCoeff (H s) (u:ℂ) m)
      (∫ ξ, (ξ:ℂ)^2*reciprocalKernel (H t) (a ξ) u m ∂μ) t := by
  have d := functional_deriv hd (u:ℂ) m
  convert d using 1
  simp_rw [kernel_eq_variation,firstVariation_extract,coeff_mul,averagedDirection,coeff_mk]
  let A := (residueBase (H t) u)^m
  let R := fun (ξ : Circle) => reciprocalDirection (H t) (a ξ)
  let f := fun (k : ℕ × ℕ) (ξ : Circle) => A.coeff k.1*((ξ:ℂ)^2*(R ξ).coeff k.2)
  have hf (k : ℕ × ℕ) : Integrable (f k) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul ((by fun_prop : Continuous (fun ξ : Circle => (ξ:ℂ)^2)).mul
      ((reciprocal_coeff_continuous (H t) k.2).comp ha))
  calc
    _ = ∫ ξ, (∑ k∈antidiagonal m, f k ξ)*(m.factorial:ℂ)⁻¹ ∂μ := by
      apply integral_congr_ae
      filter_upwards with ξ
      dsimp [f,A,R]
      rw [div_eq_mul_inv,←mul_assoc,mul_sum]
      congr 1
      apply sum_congr rfl; intros; ring
    _ = _ := by
      rw [integral_mul_const,integral_finsetSum _ (fun k _ => hf k),div_eq_mul_inv]
      congr 1
      apply sum_congr rfl
      intro k _
      exact integral_const_mul _ _

/-- Time evolution of V_u(h₁(t)) from the first coefficient of the flow. -/
theorem modelV_evolution {h : ℝ → ℂ} {t : ℝ} (μ : Measure Circle) (u : ℝ) (m : ℕ)
    (hd : HasDerivAt h (∫ ξ, (ξ:ℂ)^2 ∂μ) t) :
    HasDerivAt (fun s => modelV (u:ℂ) (h s) m)
      (∫ ξ, (ξ:ℂ)^2*reciprocalKernel (modelProfile (1/2) (h t)) 0 u m ∂μ) t := by
  rw [integral_mul_const]
  exact (modelV_hasDeriv u (h t) m).scomp t hd

end Springer
