import Springer.ModelSeries
import Springer.Chord

noncomputable section
open MeasureTheory Set Finset Complex
namespace Springer

/-- Multiplication of an ordinary coefficient sequence by exp(cx). -/
def expShift {R : Type*} [Field R] (c : R) (F : ℕ → R) (m : ℕ) : R :=
  ∑ k ∈ range (m+1), c^k / k.factorial * F (m-k)

@[simp] theorem expShift_zero {R : Type*} [Field R] [CharZero R] (F : ℕ → R) (m : ℕ) :
    expShift 0 F m = F m := by
  unfold expShift
  rw [sum_eq_single 0]
  · simp
  · intro k hk hn; simp [zero_pow hn]
  · simp

private theorem sum_by_parity (F : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (2*n+1), F k =
      (∑ k ∈ range (n+1), F (2*k)) + ∑ k ∈ range n, F (2*k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1=((2*n+1)+1)+1 by omega, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun k => F (2*k)) (n+1), sum_range_succ (fun k => F (2*k+1)) n]
    rw [show 2*(n+1)=2*n+1+1 by omega]
    ring

/-- The upper comparison coefficient expressed as a polynomial in the squared radius. -/
def comparisonPolynomial (u t : ℝ) (n : ℕ) (q : ℝ) :=
  (∑ k ∈ range (n+1), (modelU u t (2*(n-k)) / (2*k).factorial) * q^k) -
    modelV u t (2*n)

theorem comparisonPolynomial_sq (u t r : ℝ) (n : ℕ) :
    comparisonPolynomial u t n (r^2) =
      expShift r (modelU u t) (2*n) - modelV u t (2*n) := by
  unfold comparisonPolynomial expShift
  rw [sum_by_parity]
  have ho : (∑ k ∈ range n, r^(2*k+1)/(2*k+1).factorial*modelU u t (2*n-(2*k+1)))=0 := by
    apply sum_eq_zero
    intro k hk
    have hk' := mem_range.mp hk
    have hodd : Odd (2*n-(2*k+1)) := by rw [Nat.odd_iff]; omega
    rw [(model_odd u t hodd).1, mul_zero]
  rw [ho,add_zero]
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [←pow_mul,show 2*(n-k)=2*n-2*k by omega]
  ring

theorem comparisonPolynomial_convex {u t : ℝ} (hu : u∈Set.Icc 0 1) (ht : 0≤t) (n : ℕ) :
    ConvexOn ℝ (Ici 0) (comparisonPolynomial u t n) := by
  let a := fun k : ℕ => modelU u t (2*(n-k)) / ((2*k).factorial:ℝ)
  have ha (k : ℕ) : 0 ≤ a k := by
    have h := model_nonneg hu ht (2*(n-k))
    exact div_nonneg (h.1.trans h.2) (Nat.cast_nonneg _)
  have H (s : Finset ℕ) : ConvexOn ℝ (Ici 0) (fun q : ℝ => ∑ k ∈ s, a k*q^k) := by
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (0:ℝ) (convex_Ici (0:ℝ))
    | insert k s hks ih =>
      have hk := (convexOn_pow (𝕜:=ℝ) k).smul (ha k)
      simpa [sum_insert hks,smul_eq_mul,Pi.add_def] using hk.add ih
  change ConvexOn ℝ (Set.Ici 0) (fun q : ℝ => (∑ k ∈ range (n+1), a k*q^k) - modelV u t (2*n))
  simpa [sub_eq_add_neg,Pi.add_def] using
    (H (range (n+1))).add_const (-modelV u t (2*n))

theorem comparison_chord (μ : Measure Circle) [IsProbabilityMeasure μ] {u t : ℝ}
    (hu : u∈Set.Icc 0 1) (ht : 0≤t) (n : ℕ) (Z : ℂ) {β : ℝ} (hb : 0≤β) :
    (∫ ξ : Circle, comparisonPolynomial u t n (‖Z+(β:ℂ)*ξ‖^2) ∂μ) ≤
      (1+chordDirection Z (∫ ξ : Circle, (ξ:ℂ) ∂μ))/2 *
        comparisonPolynomial u t n ((‖Z‖+β)^2) +
      (1-chordDirection Z (∫ ξ : Circle, (ξ:ℂ) ∂μ))/2 *
        comparisonPolynomial u t n ((‖Z‖-β)^2) :=
  chord_integral μ (comparisonPolynomial_convex hu ht n) Z hb

/-- Integrate a complex derivative bound by applying the real FTC to a norming
functional for the endpoint difference. The functional also exists for a zero difference. -/
theorem comparison_integrate {s t : ℝ} (hst : s≤t) {f : ℝ → ℂ} {v : ℝ → ℂ} {F : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f s t) (hF : AbsolutelyContinuousOnInterval F s t)
    (hd : ∀ᵐ x ∂volume.restrict (Set.Icc s t), HasDerivAt f (v x) x ∧ ‖v x‖≤deriv F x) :
    ‖f t - f s‖ ≤ F t - F s := by
  obtain ⟨L, hL, he⟩ := exists_dual_vector'' ℝ (f t-f s)
  have hcomp := L.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have hle : deriv (L ∘ f) ≤ᵐ[volume.restrict (Set.Icc s t)] deriv F := by
    filter_upwards [hd] with x hx
    rw [(L.hasFDerivAt.comp_hasDerivAt x hx.1).deriv]
    calc
      L (v x) ≤ ‖L (v x)‖ := le_abs_self _
      _ ≤ ‖L‖*‖v x‖ := L.le_opNorm _
      _ ≤ 1*‖v x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ ≤ deriv F x := by simpa using hx.2
  have H := intervalIntegral.integral_mono_ae_restrict hst hcomp.intervalIntegrable_deriv
    hF.intervalIntegrable_deriv hle
  rw [hcomp.integral_deriv_eq_sub,hF.integral_deriv_eq_sub] at H
  simpa [Function.comp_apply,←map_sub,he] using H

end Springer
