import Springer.ComparisonStep
import Springer.DiskConsequences

noncomputable section
open Set MeasureTheory Complex Finset
namespace Springer

def comparisonSlope (μ : Measure Circle) (H : PowerSeries ℂ) (P c : ℂ) (u t : ℝ) (n : ℕ) : ℂ :=
  let a := fun ξ : Circle => (Real.sqrt t:ℂ)*ξ-P
  (∫ ξ : Circle, (ξ:ℂ)^2*((c+(u:ℂ)*a ξ)^(2*(n+1))/((2*(n+1)).factorial:ℂ)) ∂μ) +
    ∫ v : ℝ in 0..u, (1-(v:ℂ))*∫ ξ : Circle, (ξ:ℂ)^2*comparisonValue H v (c+((u:ℂ)-v)*a ξ) n ∂μ

def comparisonUpperSlope (μ : Measure Circle) (P c : ℂ) (u t : ℝ) (n : ℕ) : ℝ :=
  let Z := c-(u:ℂ)*P
  chordAverage μ Z (u*Real.sqrt t) (forcingPolynomial (n+1)) +
    ∫ v : ℝ in 0..u, (1-v)*chordAverage μ Z ((u-v)*Real.sqrt t) (comparisonPolynomial v t n)

private theorem chord_intervalIntegrable (μ : Measure Circle) (Z : ℂ) (u t : ℝ) (n : ℕ) :
    IntervalIntegrable (fun v : ℝ => (1-v)*
      chordAverage μ Z ((u-v)*Real.sqrt t) (comparisonPolynomial v t n)) volume 0 u := by
  apply Continuous.intervalIntegrable
  unfold chordAverage signAverage
  unfold comparisonPolynomial modelU modelV functionalCoeff
  fun_prop

private theorem comparisonValue_init (c : ℂ) (u : ℝ) (n : ℕ) : comparisonValue 0 u c n=0 := by
  simp [comparisonValue,expShift,modelV,modelProfile,functionalCoeff,shiftedResidue,
    zero_pow (Nat.succ_ne_zero _)]

/-- The degree induction in Proposition 6.1, taking as input the two coefficientwise
evolution identities. The induction hypothesis remains uniform in time, u, and c. -/
theorem comparison_of_evolution_slopes_retained {s : ℝ} (hs : 0 ≤ s) {H : ℝ → PowerSeries ℂ}
    (hinit : H s=0) (P : ℝ → ℂ) (μ : ℝ → Measure Circle) [∀ x, IsProbabilityMeasure (μ x)]
    (hac : ∀ (n : ℕ) (u : ℝ), u∈Set.Icc 0 1 → ∀ c : ℂ,
      AbsolutelyContinuousOnInterval (fun t => comparisonValue (H t) u c n) s 1 ∧
      AbsolutelyContinuousOnInterval (fun t => comparisonBound (P t) u t c n) s 1)
    (hder : ∀ (n : ℕ) (u : ℝ), u∈Set.Icc 0 1 → ∀ c : ℂ, ∀ᵐ t ∂volume.restrict (Set.Icc s 1),
      HasDerivAt (fun x => comparisonValue (H x) u c (n+1)) (comparisonSlope (μ t) (H t) (P t) c u t n) t ∧
      HasDerivAt (fun x => comparisonBound (P x) u x c (n+1)) (comparisonUpperSlope (μ t) (P t) c u t n) t) :
    ∀ n t, t∈Set.Icc s 1 → ∀ u, u∈Set.Icc 0 1 → ∀ c : ℂ,
      ‖comparisonValue (H t) u c n‖ ≤ comparisonBound (P t) u t c n - comparisonBound (P s) u s c n := by
  intro n
  induction n with
  | zero =>
    intro t ht u hu c
    have hzero (P c : ℂ) (u t : ℝ) : comparisonBound P u t c 0=0 := by
      simp [comparisonBound,comparisonPolynomial,(model_degree_zero u t).1,(model_degree_zero u t).2]
    simpa only [hzero,sub_zero] using comparison_zero (H t) (P t) c u t
  | succ n ih =>
    intro t ht u hu c
    have hsub : Set.Icc s t ⊆ Set.Icc s 1 := Set.Icc_subset_Icc_right ht.2
    have husub : uIcc s t ⊆ uIcc s 1 := by
      simpa [uIcc_of_le ht.1,uIcc_of_le (ht.1.trans ht.2)] using hsub
    obtain ⟨hAC₁,hAC₂⟩ := hac (n+1) u hu c
    have hdiff := comparison_integrate ht.1 (hAC₁.mono husub) (hAC₂.mono husub)
      (v:=fun x => comparisonSlope (μ x) (H x) (P x) c u x n) (by
        have hloc := (hder n u hu c).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
        filter_upwards [hloc,ae_restrict_mem measurableSet_Icc] with x hd hx
        have hx' := hsub hx
        refine ⟨hd.1, ?_⟩
        rw [hd.2.deriv]
        exact comparison_step_bound (μ x) (H x) (P x) c hu (hs.trans hx'.1) n (fun v hv b =>
          (ih x hx' v hv b).trans (sub_le_self _ (comparison_initial hv hs _ _ _)))
          (chord_intervalIntegrable (μ x) _ u x n))
    rw [hinit,comparisonValue_init,sub_zero] at hdiff
    exact hdiff

theorem comparison_of_evolution_slopes {s : ℝ} (hs : 0 ≤ s) {H : ℝ → PowerSeries ℂ}
    (hinit : H s=0) (P : ℝ → ℂ) (μ : ℝ → Measure Circle) [∀ x, IsProbabilityMeasure (μ x)]
    (hac : ∀ (n : ℕ) (u : ℝ), u∈Set.Icc 0 1 → ∀ c : ℂ,
      AbsolutelyContinuousOnInterval (fun t => comparisonValue (H t) u c n) s 1 ∧
      AbsolutelyContinuousOnInterval (fun t => comparisonBound (P t) u t c n) s 1)
    (hder : ∀ (n : ℕ) (u : ℝ), u∈Set.Icc 0 1 → ∀ c : ℂ, ∀ᵐ t ∂volume.restrict (Set.Icc s 1),
      HasDerivAt (fun x => comparisonValue (H x) u c (n+1)) (comparisonSlope (μ t) (H t) (P t) c u t n) t ∧
      HasDerivAt (fun x => comparisonBound (P x) u x c (n+1)) (comparisonUpperSlope (μ t) (P t) c u t n) t) :
    ∀ n t, t∈Set.Icc s 1 → ∀ u, u∈Set.Icc 0 1 → ∀ c : ℂ,
      ‖comparisonValue (H t) u c n‖ ≤ comparisonBound (P t) u t c n := by
  intro n t ht u hu c
  exact (comparison_of_evolution_slopes_retained hs hinit P μ hac hder n t ht u hu c).trans
    (sub_le_self _ (comparison_initial hu hs _ _ _))

/-- Specializing the actual comparison at t=u=1, c=0 removes the factorial and
produces the signed center of the printed disk. -/
theorem diskBound_of_comparison_endpoint {g : ℂ → ℂ} {H : PowerSeries ℂ} {m : ℕ}
    (hB : ∀ k, H.coeff k = -inverseCoeff g (k+1)) (hb : H.coeff 0=forwardCoeff g 1)
    (h : ‖comparisonValue H 1 0 m‖ ≤ comparisonBound 0 1 1 0 m) : DiskBound g m := by
  let N := ((2*m).factorial:ℝ)
  have hN : 0<N := by dsimp [N]; positivity
  have hL : comparisonValue H 1 0 m =
      -(inverseCoeff g (2*m+1)+(diskWeight m:ℂ)*(forwardCoeff g 1)^(m+1))/(N:ℂ) := by
    simp only [comparisonValue, Complex.ofReal_one,expShift_zero,functional_one,hb,
      (model_endpoint (forwardCoeff g 1) m).2,hB]
    unfold diskWeight N
    push_cast
    ring
  have hR : comparisonBound 0 1 1 0 m = ((1-(1/2:ℝ)^m)*(catalan m:ℝ))/N := by
    unfold comparisonBound
    rw [comparisonPolynomial_sq]
    simp only [mul_zero,sub_zero,norm_zero,expShift_zero,(model_endpoint (1:ℝ) m).1,
      (model_endpoint (1:ℝ) m).2,one_pow,mul_one,N]
    ring
  rw [hL,hR,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN] at h
  exact (div_le_div_iff_of_pos_right hN).mp h

end Springer
