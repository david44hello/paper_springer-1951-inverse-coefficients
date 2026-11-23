import Mathlib

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology NNReal
namespace Springer

/-- After multiplication by a fixed Cauchy weight, take the contour integral of the
pointwise fundamental theorem of calculus. Joint integrability permits Fubini. -/
theorem contour_increment {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s x : ℝ} (hx : s≤x) (W : α → ℂ) (Y V : ℝ → α → ℂ)
    (hsY : Integrable (fun z => W z*Y s z) μ) (hxY : Integrable (fun z => W z*Y x z) μ)
    (hprod : Integrable (fun p : α × ℝ => W p.1*V p.2 p.1) (μ.prod (volume.restrict (Ioc s x))))
    (hinc : ∀ z, Y x z-Y s z=∫ v : ℝ in s..x, V v z) :
    (∫ z, W z*Y x z ∂μ)-(∫ z, W z*Y s z ∂μ) =
      ∫ v : ℝ in s..x, ∫ z, W z*V v z ∂μ := by
  rw [←integral_sub hxY hsY]
  calc
    _ = ∫ z, (∫ v : ℝ in s..x, W z*V v z) ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [←mul_sub,hinc,intervalIntegral.integral_const_mul]
    _ = _ := by
      simp only [intervalIntegral.integral_of_le hx]
      exact integral_integral_swap hprod

/-- Countably many time-dependent coefficients share a single exceptional null set.
Intervals are closed in the hypotheses, but the derivative uses an interior germ. -/
theorem simultaneous_coefficient_deriv {s b : ℝ} (hsb : s≤b) (A D : ℕ → ℝ → ℂ)
    (hi : ∀ n, IntervalIntegrable (D n) volume s b)
    (hinc : ∀ n x, x∈Icc s b → A n x-A n s=∫ v : ℝ in s..x, D n v) :
    ∀ᵐ x ∂volume.restrict (Icc s b), ∀ n, HasDerivAt (A n) (D n x) x := by
  rw [←Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ:=volume) (a:=s) (b:=b)),ae_all_iff]
  intro n
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [(hi n).ae_hasDerivAt_integral] with x hx hxi
  have hs' : s∈uIcc s b := left_mem_uIcc
  have hx' : x∈uIcc s b := by rw [uIcc_of_le hsb]; exact Ioo_subset_Icc_self hxi
  have h := (hx hx' s hs').const_add (A n s)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
  have he := hinc n y (Ioo_subset_Icc_self hy)
  linear_combination he

/-- A uniform bound on the contour derivative gives absolute continuity of
each coefficient without choosing new exceptional sets on subintervals. -/
theorem coefficient_ac_of_increment {s b : ℝ} (hsb : s≤b) {C : ℝ≥0} (A D : ℝ → ℂ)
    (hd : ∀ x∈Icc s b, ‖D x‖ ≤ C)
    (hi : ∀ x∈Icc s b, IntervalIntegrable D volume s x)
    (hinc : ∀ x∈Icc s b, A x-A s=∫ v : ℝ in s..x, D v) :
    AbsolutelyContinuousOnInterval A s b := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K:=C)
  rw [lipschitzOnWith_iff_dist_le_mul,uIcc_of_le hsb]
  intro x hx y hy
  have e : A x - A y = ∫ v : ℝ in y..x, D v := by
    rw [←intervalIntegral.integral_interval_sub_left (hi x hx) (hi y hy),←hinc x hx,←hinc y hy]
    abel
  rw [dist_eq_norm,Real.dist_eq,e]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro v hv
  apply hd
  exact ⟨(le_min hy.1 hx.1).trans hv.1.le, hv.2.trans (max_le hy.2 hx.2)⟩

end Springer
