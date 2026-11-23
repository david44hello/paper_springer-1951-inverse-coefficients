import Springer.Comparison

noncomputable section
open MeasureTheory Set Finset Complex
open scoped ComplexConjugate
namespace Springer

/-- The two-point average with the direction determined by the same measure at all scales. -/
def signAverage (ω plus minus : ℝ) := (1+ω)/2*plus + (1-ω)/2*minus

def chordAverage (μ : Measure Circle) (Z : ℂ) (β : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  signAverage (chordDirection Z (∫ ξ : Circle, (ξ:ℂ) ∂μ))
    (Φ ((‖Z‖+β)^2)) (Φ ((‖Z‖-β)^2))

/-- Integrands of the complex evolution carry an extra factor ξ² of unit modulus. -/
theorem norm_circle_integral_le_chord (μ : Measure Circle) [IsProbabilityMeasure μ]
    {Φ : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) Φ) (Z : ℂ) {β : ℝ} (hb : 0≤β)
    (f : Circle → ℂ) (h : ∀ ξ, ‖f ξ‖ ≤ Φ (‖Z+(β:ℂ)*ξ‖^2)) :
    ‖∫ ξ : Circle, (ξ:ℂ)^2*f ξ ∂μ‖ ≤ chordAverage μ Z β Φ := by
  have hi := convex_comp_integrable_of_bounded μ hf
    (Y:=fun ξ : Circle => ‖Z+(β:ℂ)*ξ‖^2) (by fun_prop)
    (M:=(‖Z‖+β)^2) (sq_nonneg _) (fun ξ => by
      refine ⟨sq_nonneg _,pow_le_pow_left₀ (norm_nonneg _) ?_ 2⟩
      simpa [norm_mul, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
        using norm_add_le Z ((β:ℂ)*(ξ:ℂ)))
  apply (norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall (fun ξ => ?_))).trans
    (chord_integral μ hf Z hb)
  simpa only [norm_mul,norm_pow,Circle.norm_coe,one_pow,one_mul] using h ξ

def forcingPolynomial (n : ℕ) (q : ℝ) : ℝ := q^n / (2*n).factorial

private theorem forcing_convex (n : ℕ) : ConvexOn ℝ (Ici 0) (forcingPolynomial n) := by
  change ConvexOn ℝ (Ici 0) (fun q : ℝ => q^n / ((2*n).factorial:ℝ))
  simpa [smul_eq_mul, div_eq_inv_mul] using
    (convexOn_pow (𝕜:=ℝ) n).smul (show 0 ≤ (((2*n).factorial:ℝ))⁻¹ by positivity)

def comparisonValue (H : PowerSeries ℂ) (u : ℝ) (c : ℂ) (n : ℕ) :=
  expShift c (functionalCoeff H (u:ℂ)) (2*n) - modelV (u:ℂ) (H.coeff 0) (2*n)

def comparisonBound (P : ℂ) (u t : ℝ) (c : ℂ) (n : ℕ) :=
  comparisonPolynomial u t n (‖c-(u:ℂ)*P‖^2)

theorem comparison_zero (H : PowerSeries ℂ) (P c : ℂ) (u t : ℝ) :
    ‖comparisonValue H u c 0‖ ≤ comparisonBound P u t c 0 := by
  simp [comparisonValue, comparisonBound, comparisonPolynomial,expShift,
    functional_degree_zero, (model_degree_zero (u:ℂ) (PowerSeries.constantCoeff H)).2,
    (model_degree_zero u t).1,(model_degree_zero u t).2]

theorem comparison_initial {u t : ℝ} (hu : u∈Set.Icc 0 1) (ht : 0≤t) (P c : ℂ) (n : ℕ) :
    0 ≤ comparisonBound P u t c n := by
  let term := fun k : ℕ => (modelU u t (2*(n-k)) / ((2*k).factorial:ℝ))* (‖c-(u:ℂ)*P‖^2)^k
  have hnon (k : ℕ) : 0≤term k := by
    have h := model_nonneg hu ht (2*(n-k))
    exact mul_nonneg (div_nonneg (h.1.trans h.2) (Nat.cast_nonneg _)) (by positivity)
  have hle := Finset.single_le_sum (f:=term) (fun k _ => hnon k) (mem_range.mpr (Nat.zero_lt_succ n))
  apply sub_nonneg.mpr
  exact (model_nonneg hu ht (2*n)).2.trans (by simpa [term] using hle)

/-- The forcing term and the lower-degree term are dominated at the same measure
and center. The complex derivative here is in its Fubini-reordered form. -/
theorem comparison_step_bound (μ : Measure Circle) [IsProbabilityMeasure μ]
    (H : PowerSeries ℂ) (P c : ℂ) {u t : ℝ} (hu : u∈Set.Icc 0 1) (ht : 0≤t) (n : ℕ)
    (ih : ∀ v ∈ Set.Icc 0 1, ∀ b : ℂ, ‖comparisonValue H v b n‖ ≤ comparisonBound P v t b n)
    (hI : IntervalIntegrable (fun v : ℝ => (1-v)*
      chordAverage μ (c-(u:ℂ)*P) ((u-v)*Real.sqrt t) (comparisonPolynomial v t n)) volume 0 u) :
    let Z := c-(u:ℂ)*P
    let a := fun ξ : Circle => (Real.sqrt t:ℂ)*ξ-P
    ‖(∫ ξ : Circle, (ξ:ℂ)^2*((c+(u:ℂ)*a ξ)^(2*(n+1))/((2*(n+1)).factorial:ℂ)) ∂μ) +
      (∫ v : ℝ in 0..u, (1-(v:ℂ))*
        ∫ ξ : Circle, (ξ:ℂ)^2*comparisonValue H v (c+((u:ℂ)-v)*a ξ) n ∂μ)‖ ≤
      chordAverage μ Z (u*Real.sqrt t) (forcingPolynomial (n+1)) +
      ∫ v : ℝ in 0..u, (1-v)*chordAverage μ Z ((u-v)*Real.sqrt t) (comparisonPolynomial v t n) := by
  intro Z a
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply norm_circle_integral_le_chord μ (forcing_convex (n+1)) Z (mul_nonneg hu.1 (Real.sqrt_nonneg t))
    intro ξ
    have he : c+(u:ℂ)*a ξ = Z+((u*Real.sqrt t:ℝ):ℂ)*ξ := by
      dsimp [Z,a]; push_cast; ring
    rw [he,norm_div,norm_pow]
    simp [forcingPolynomial, ←pow_mul]
  · apply intervalIntegral.norm_integral_le_of_norm_le hu.1 _ hI
    apply Filter.Eventually.of_forall
    intro v hv
    have hv' : v ∈ Set.Icc 0 1 := ⟨hv.1.le,hv.2.trans hu.2⟩
    have hq : 0≤(u-v)*Real.sqrt t := mul_nonneg (sub_nonneg.mpr hv.2) (Real.sqrt_nonneg t)
    have hc := norm_circle_integral_le_chord μ (comparisonPolynomial_convex hv' ht n) Z hq
      (fun ξ => comparisonValue H v (c+((u:ℂ)-v)*a ξ) n) (fun ξ => by
        have he : c+((u:ℂ)-v)*a ξ-(v:ℂ)*P = Z+(((u-v)*Real.sqrt t:ℝ):ℂ)*ξ := by
          dsimp [Z,a]; push_cast; ring
        simpa only [comparisonBound,he] using ih v hv' (c+((u:ℂ)-v)*a ξ))
    rw [norm_mul]
    have hw : ‖1-(v:ℂ)‖=1-v := by
      rw [← Complex.ofReal_one, ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hv'.2)]
    rw [hw]
    exact mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hv'.2)

end Springer
