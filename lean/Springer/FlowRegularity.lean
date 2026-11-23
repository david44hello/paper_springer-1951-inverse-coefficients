import Springer.Comparison
import Springer.TimeChange

noncomputable section
open MeasureTheory Set Complex Filter
open scoped NNReal Topology
namespace Springer

theorem complex_increment_of_ac {f v : ℝ → ℂ} {s t : ℝ} (hst : s≤t)
    (hf : AbsolutelyContinuousOnInterval f s t) (hv : IntervalIntegrable v volume s t)
    (hd : ∀ᵐ x ∂volume.restrict (Icc s t), HasDerivAt f (v x) x) :
    f t-f s=∫ x : ℝ in s..t, v x := by
  have proj (L : ℂ →L[ℝ] ℝ) : L (f t-f s)=L (∫ x : ℝ in s..t, v x) := by
    have hAC := L.lipschitzWith.comp_absolutelyContinuousOnInterval hf
    rw [map_sub, ←L.intervalIntegral_comp_comm hv]
    calc
      _ = ∫ x : ℝ in s..t, deriv (L ∘ f) x := hAC.integral_deriv_eq_sub.symm
      _ = _ := by
        apply intervalIntegral.integral_congr_ae
        rw [ae_restrict_iff' measurableSet_Icc] at hd
        filter_upwards [hd] with x hx hxi
        apply (L.hasFDerivAt.comp_hasDerivAt x (hx _)).deriv
        exact uIoc_subset_uIcc hxi |> (fun h => by simpa [uIcc_of_le hst] using h)
  exact Complex.ext (proj Complex.reCLM) (proj Complex.imCLM)

/-- Bounded velocity of an absolutely continuous complex path controls its
Lipschitz constant on the entire closed interval. -/
theorem lipschitz_of_ac_velocity {f v : ℝ → ℂ} {s b : ℝ} (hsb : s≤b) (C : ℝ≥0)
    (hf : AbsolutelyContinuousOnInterval f s b)
    (hd : ∀ᵐ x ∂volume.restrict (Icc s b), HasDerivAt f (v x) x ∧ ‖v x‖ ≤ C) :
    LipschitzOnWith C f (Icc s b) := by
  have hlin : AbsolutelyContinuousOnInterval (fun x : ℝ => (C:ℝ)*x) s b :=
    (ContDiff.contDiffOn (by fun_prop : ContDiff ℝ 1 (fun x : ℝ => (C:ℝ)*x))).absolutelyContinuousOnInterval
  have inc (x y : ℝ) (hx : x∈Icc s b) (hy : y∈Icc s b) (hxy : x≤y) :
      ‖f y-f x‖ ≤ (C:ℝ)*(y-x) := by
    have hsub : Icc x y ⊆ Icc s b := Icc_subset_Icc hx.1 hy.2
    have hus : uIcc x y ⊆ uIcc s b := by simpa [uIcc_of_le hxy,uIcc_of_le hsb] using hsub
    have hD : ∀ᵐ z ∂volume.restrict (Icc x y), HasDerivAt f (v z) z ∧ ‖v z‖ ≤ deriv (fun x:ℝ => (C:ℝ)*x) z := by
      filter_upwards [hd.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))] with z hz
      simpa using hz
    simpa only [mul_sub] using comparison_integrate hxy (hf.mono hus) (hlin.mono hus) hD
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rcases le_total x y with h|h
  · rw [dist_comm,dist_eq_norm,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr h),neg_sub]
    exact inc x y hx hy h
  · rw [dist_eq_norm,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr h)]
    exact inc y x hy hx h

theorem elapsed_lipschitz {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ≥0, LipschitzOnWith C elapsed (Icc s 1) := by
  let C : ℝ≥0 := ⟨1/(2*s), by positivity⟩
  refine ⟨C,(convex_Icc s 1).lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_⟩
  · intro x hx; exact (elapsed_deriv (hs.trans_le hx.1)).differentiableAt
  · intro x hx
    have hpx := hs.trans_le hx.1
    change ‖deriv elapsed x‖ ≤ 1/(2*s)
    rw [(elapsed_deriv hpx).deriv,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [hx.1])

theorem inv_lipschitz_away {δ : ℝ} (hδ : 0<δ) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun z : ℂ => z⁻¹) {z | δ≤‖z‖} := by
  let C : ℝ≥0 := ⟨1/δ^2,by positivity⟩
  refine ⟨C,lipschitzOnWith_iff_dist_le_mul.mpr ?_⟩
  intro x hx y hy
  have hx' : δ≤‖x‖ := hx
  have hy' : δ≤‖y‖ := hy
  have hnx := norm_pos_iff.mp (hδ.trans_le hx')
  have hny := norm_pos_iff.mp (hδ.trans_le hy')
  have e : x⁻¹-y⁻¹=(y-x)/(x*y) := by field_simp
  rw [dist_eq_norm,e,norm_div,norm_mul,norm_sub_rev,dist_eq_norm]
  change ‖x-y‖/(‖x‖*‖y‖) ≤ 1/δ^2*‖x-y‖
  have hp : δ^2 ≤ ‖x‖*‖y‖ := by rw [pow_two]; exact mul_le_mul hx' hy' hδ.le (norm_nonneg _)
  rw [div_eq_mul_inv,one_div,mul_comm ‖x-y‖]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (sq_pos_of_pos hδ) hp) (norm_nonneg _)

end Springer
