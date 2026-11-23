import Springer.ComparisonInduction
import Springer.ShiftedKernel
import Springer.FunctionalEvolution

noncomputable section
open MeasureTheory Set Finset Complex PowerSeries
namespace Springer

private theorem circle_interval_integrable (μ : Measure Circle) [IsFiniteMeasure μ]
    (f : Circle → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) (u : ℝ) :
    Integrable (Function.uncurry f) (μ.prod (volume.restrict (Set.Ioc 0 u))) := by
  have hi : IntegrableOn (Function.uncurry f) (Set.univ ×ˢ Set.Icc 0 u) (μ.prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_univ.prod isCompact_Icc)
  have he : μ.prod (volume.restrict (Set.Ioc 0 u)) =
      (μ.prod volume).restrict (Set.univ ×ˢ Set.Ioc 0 u) := by
    simpa only [Measure.restrict_univ] using (Measure.prod_restrict (μ:=μ) (ν:=volume) Set.univ (Set.Ioc 0 u))
  rw [he]
  exact hi.mono_set (Set.prod_mono_right Set.Ioc_subset_Icc_self)

private theorem kernel_cont (H : PowerSeries ℂ) (u : ℝ) (m : ℕ) :
    Continuous (fun a => reciprocalKernel H a u m) := by
  simp only [kernel_eq_variation,firstVariation_extract,coeff_mul]
  apply Continuous.div_const
  apply continuous_finsetSum
  intro k hk
  exact continuous_const.mul (reciprocal_coeff_continuous H k.2)

private theorem integrable_circle (μ : Measure Circle) [IsFiniteMeasure μ] {f : Circle → ℂ}
    (h : Continuous f) : Integrable f μ :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Insert the shift exp(cx) and subtract the model with parameter h₁(t) in the
coefficient ODE. Fubini exchanges the compact contour and the real v-integral. -/
theorem comparisonValue_hasDeriv {H : ℝ → PowerSeries ℂ} {t : ℝ} (P c : ℂ)
    (μ : Measure Circle) [IsProbabilityMeasure μ] {u : ℝ} (hu : 0≤u) (n : ℕ)
    (hd : CoeffDerivAt H (averagedDirection (H t) (fun ξ : Circle => (Real.sqrt t:ℂ)*ξ-P) μ) t) :
    HasDerivAt (fun x => comparisonValue (H x) u c (n+1)) (comparisonSlope μ (H t) P c u t n) t := by
  let a := fun ξ : Circle => (Real.sqrt t:ℂ)*ξ-P
  let m := 2*n
  let F := H t
  let M := modelProfile (1/2) (F.coeff 0)
  let K := fun j (ξ : Circle) => (ξ:ℂ)^2*reciprocalKernel F (a ξ) u j
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hK (j : ℕ) : Integrable (K j) μ :=
    integrable_circle μ ((by fun_prop : Continuous (fun ξ : Circle => (ξ:ℂ)^2)).mul ((kernel_cont F u j).comp ha))
  have hk (j : ℕ) := functional_evolution μ ha hd u j
  have hshift (j : ℕ) : HasDerivAt (fun x => expShift c (functionalCoeff (H x) (u:ℂ)) j)
      (expShift c (fun d => ∫ ξ, K d ξ ∂μ) j) t := by
    unfold expShift
    apply HasDerivAt.fun_sum
    intro k hk'
    exact (hk (j-k)).const_mul _
  have hd0 : HasDerivAt (fun x => (H x).coeff 0) (∫ ξ : Circle, (ξ:ℂ)^2 ∂μ) t := by
    simpa only [averagedDirection_zero] using hd 0
  have hv := modelV_evolution μ u (m+2) hd0
  have he := (hshift (m+2)).sub hv
  have hm : 2*(n+1)=m+2 := by dsimp [m]; omega
  change HasDerivAt (fun x => expShift c (functionalCoeff (H x) (u:ℂ)) (2*(n+1)) -
    modelV (u:ℂ) ((H x).coeff 0) (2*(n+1))) _ t
  rw [hm]
  apply he.congr_deriv
  let force := fun ξ : Circle => (ξ:ℂ)^2*((c+(u:ℂ)*a ξ)^(m+2)/((m+2).factorial:ℂ))
  let inner := fun (ξ : Circle) (v : ℝ) => (ξ:ℂ)^2*((1-(v:ℂ))*
    comparisonValue F v (c+((u:ℂ)-v)*a ξ) n)
  have hcont : Continuous (Function.uncurry inner) := by
    unfold Function.uncurry inner comparisonValue expShift modelV functionalCoeff
    dsimp only [a]
    fun_prop
  have hprod := circle_interval_integrable μ inner hcont u
  have hforce : Integrable force μ := integrable_circle μ (by dsimp [force,a]; fun_prop)
  have hinner : Integrable (fun ξ => ∫ v : ℝ in 0..u, inner ξ v) μ := by
    simp only [intervalIntegral.integral_of_le hu]
    exact hprod.integral_prod_left
  rw [expShift_circle_integral μ c K _ (fun j _ => hK j)]
  have hL : Integrable (fun ξ => expShift c (fun j => K j ξ) (m+2)) μ := by
    unfold expShift; apply integrable_finsetSum; intro j _; exact (hK _).const_mul _
  have hV : Integrable (fun ξ : Circle => (ξ:ℂ)^2*reciprocalKernel M 0 u (m+2)) μ :=
    integrable_circle μ (by fun_prop)
  rw [←integral_sub hL hV]
  calc
    _ = ∫ ξ, (force ξ + ∫ v : ℝ in 0..u, inner ξ v) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ξ
      have hfactor : expShift c (fun j => K j ξ) (m+2) =
          (ξ:ℂ)^2*expShift c (reciprocalKernel F (a ξ) u) (m+2) := by
        unfold expShift K
        rw [mul_sum]
        apply sum_congr rfl; intros; ring
      dsimp only
      rw [hfactor, shifted_reciprocalKernel, reciprocalKernel]
      simp only [mul_zero, zero_pow (by omega : m+2≠0),zero_div,zero_add,convolution_zero]
      have hi (v : ℝ) : functionalCoeff M (v:ℂ) m = modelV (v:ℂ) (F.coeff 0) m := rfl
      simp_rw [hi]
      simp only [mul_add, ←intervalIntegral.integral_const_mul]
      rw [add_sub_assoc, ←intervalIntegral.integral_sub]
      · congr 1
        apply intervalIntegral.integral_congr; intro v hv'
        dsimp only [inner,comparisonValue,m,exponentialConvolution,expShift]
        ring
      all_goals
        apply Continuous.intervalIntegrable
        simp only [exponentialConvolution, modelV, functionalCoeff]
        fun_prop
    _ = (∫ ξ, force ξ ∂μ) + ∫ v : ℝ in 0..u, ∫ ξ, inner ξ v ∂μ := by
      rw [integral_add hforce hinner]
      simp only [intervalIntegral.integral_of_le hu]
      rw [integral_integral_swap hprod]
    _ = _ := by
      unfold comparisonSlope
      dsimp only
      rw [hm]
      congr 1
      apply intervalIntegral.integral_congr
      intro v hv'
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      dsimp [inner]
      ring

end Springer
