import Springer.LoewnerInput
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Springer

private theorem vector_bound (μ : Measure Circle) [IsProbabilityMeasure μ] {r : ℝ} (hr : r<1)
    {z w : ℂ} (hz : ‖z‖≤r) (hw : ‖w‖≤r) :
    ‖-z*herglotzTransform μ z-(-w*herglotzTransform μ w)‖≤(1+2/(1-r)^2)*‖z-w‖ := by
  have hd (x : ℂ) (hx : ‖x‖≤r) (ξ : Circle) : 1-r≤‖1-(ξ:ℂ)*x‖ :=
    (sub_le_sub_left hx 1).trans (by simpa [norm_mul] using norm_sub_norm_le (1:ℂ) ((ξ:ℂ)*x))
  have hi (x : ℂ) (hx : ‖x‖≤r) : Integrable (fun ξ : Circle => -x*flowKernel x ξ) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul (circle_kernel_continuous (by simpa [disc] using hx.trans_lt hr))
  change ‖-z*(∫ ξ, flowKernel z ξ ∂μ)-(-w*(∫ ξ, flowKernel w ξ ∂μ))‖≤_
  rw [←integral_const_mul,←integral_const_mul,←integral_sub (hi z hz) (hi w hw)]
  apply le_trans (norm_integral_le_of_norm_le_const (C:=(1+2/(1-r)^2)*‖z-w‖) _) (by simp)
  filter_upwards with ξ
  have hzne := norm_pos_iff.mp ((sub_pos.mpr hr).trans_le (hd z hz ξ))
  have hwne := norm_pos_iff.mp ((sub_pos.mpr hr).trans_le (hd w hw ξ))
  have eq : -z*flowKernel z ξ-(-w*flowKernel w ξ) =
      (z-w)*(1-2/((1-(ξ:ℂ)*z)*(1-(ξ:ℂ)*w))) := by
    unfold flowKernel
    generalize ez : 1-(ξ:ℂ)*z = A at hzne ⊢
    generalize ew : 1-(ξ:ℂ)*w = B at hwne ⊢
    field_simp [hzne,hwne]
    rw [←ez,←ew]; ring
  rw [eq,norm_mul,mul_comm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one,norm_div,norm_mul,Complex.norm_ofNat]
  apply add_le_add_right
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (sub_pos.mpr hr))
    (by rw [sq]; exact mul_le_mul (hd z hz ξ) (hd w hw ξ) (sub_nonneg.mpr hr.le) (norm_nonneg _))

private theorem ac_zero_of_growth {T K : ℝ} (hT : 0≤T) {d d' : ℝ → ℂ}
    (hac : AbsolutelyContinuousOnInterval d 0 T) (hd0 : d 0=0)
    (hd : ∀ᵐ x ∂volume.restrict (Icc 0 T), HasDerivAt d (d' x) x ∧ ‖d' x‖≤K*‖d x‖) :
    ∀ x∈Icc 0 T, d x=0 := by
  let weight := fun x : ℝ => Real.exp (-2*K*x)
  let energy := fun x : ℝ => weight x*‖d x‖^2
  have hw : AbsolutelyContinuousOnInterval weight 0 T :=
    (ContDiff.contDiffOn (by dsimp [weight]; fun_prop : ContDiff ℝ 1 weight)).absolutelyContinuousOnInterval
  have hn := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hac
  have hE : AbsolutelyContinuousOnInterval energy 0 T := by
    simpa [energy,sq,Pi.mul_def,Function.comp_def] using hw.mul (hn.mul hn)
  have dec : deriv energy ≤ᵐ[volume.restrict (Icc 0 T)] (fun _ => 0) := by
    filter_upwards [hd] with x hx
    have hw' : HasDerivAt weight (weight x*(-2*K)) x := by
      simpa [weight,id_eq,mul_comm] using (((hasDerivAt_id' x).const_mul (-2*K)).exp)
    have e := (hw'.mul hx.1.norm_sq).deriv
    change deriv energy x ≤ 0
    rw [show deriv energy x=_ from e]
    have hi := (real_inner_le_norm (d x) (d' x)).trans (mul_le_mul_of_nonneg_left hx.2 (norm_nonneg _))
    have hwpos : 0 ≤ weight x := (Real.exp_pos _).le
    nlinarith [mul_nonneg hwpos (sub_nonneg.mpr hi)]
  intro x hx
  have hs : Icc (0:ℝ) x ⊆ Icc 0 T := Icc_subset_Icc le_rfl hx.2
  have ex := hE.mono (show uIcc (0:ℝ) x ⊆ uIcc 0 T by simpa [uIcc_of_le hx.1,uIcc_of_le hT] using hs)
  have di := dec.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))
  have le := intervalIntegral.integral_mono_ae_restrict hx.1 ex.intervalIntegrable_deriv
    (intervalIntegrable_const (c:=(0:ℝ))) di
  rw [ex.integral_deriv_eq_sub] at le
  simp [energy,hd0] at le
  have hwpos : 0<weight x := Real.exp_pos _
  by_contra hn
  exact (not_lt_of_ge le) (mul_pos hwpos (sq_pos_of_pos (norm_pos_iff.mpr hn)))

/-- Uniqueness among absolutely continuous solutions taking values in the open disk.
Only the original Herglotz field and scalar ODE are used. -/
theorem loewner_trajectory_unique {T : ℝ} (hT : 0≤T) {p : ℝ → ℂ → ℂ}
    (hp : ∀ᵐ t ∂volume.restrict (Icc 0 T), AnalyticOnNhd ℂ (p t) disc ∧ p t 0=1 ∧
      ∀ z∈disc, 0<(p t z).re)
    {f g : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 T) (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hfD : MapsTo f (Icc 0 T) disc) (hgD : MapsTo g (Icc 0 T) disc) (he : f 0=g 0)
    (df : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt f (-f t*p t (f t)) t)
    (dg : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt g (-g t*p t (g t)) t) : EqOn f g (Icc 0 T) := by
  have cont : ContinuousOn (fun t => max ‖f t‖ ‖g t‖) (Icc 0 T) := by
    simpa [uIcc_of_le hT] using hf.continuousOn.norm.sup hg.continuousOn.norm
  obtain ⟨s,hs,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) cont
  let r := max ‖f s‖ ‖g s‖
  have hr : r<1 := max_lt (by simpa [disc] using hfD hs) (by simpa [disc] using hgD hs)
  have h := ac_zero_of_growth (K:=1+2/(1-r)^2) (d:=fun t => f t-g t)
    (d':=fun t => -f t*p t (f t)-(-g t*p t (g t))) hT (hf.sub hg) (sub_eq_zero.mpr he) (by
      filter_upwards [hp,df,dg,ae_restrict_mem measurableSet_Icc] with t htp hdf hdg ht
      refine ⟨hdf.sub hdg,?_⟩
      obtain ⟨μ,hm⟩ := herglotz_representation (p t) htp.1 htp.2.1 htp.2.2
      rw [hm (hfD ht),hm (hgD ht)]
      exact vector_bound (μ : Measure Circle) hr ((le_max_left _ _).trans (hmax ht))
        ((le_max_right _ _).trans (hmax ht)))
  exact fun x hx => sub_eq_zero.mp (h x hx)


/-- The distinguished trajectory is the unique AC disk solution to the printed
initial value problem, for each initial point separately. -/
theorem NormalizedLoewnerData.solution_unique {ψ : ℂ → ℂ} {ρ : ℝ} {p φ : ℝ → ℂ → ℂ}
    (h : NormalizedLoewnerData ψ ρ p φ) (hρ : 0<ρ) (hρ1 : ρ≤1)
    {z : ℂ} (hz : z∈disc) {y : ℝ → ℂ} (hy0 : y 0=z)
    (hy : AbsolutelyContinuousOnInterval y 0 (Real.log (1/ρ)))
    (hym : MapsTo y (Icc 0 (Real.log (1/ρ))) disc)
    (hyd : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.log (1/ρ))), HasDerivAt y (-y t*p t (y t)) t) :
    EqOn y (fun t => φ t z) (Icc 0 (Real.log (1/ρ))) := by
  have hT := Real.log_nonneg ((le_div_iff₀ hρ).mpr (by simpa using hρ1))
  exact loewner_trajectory_unique hT h.p_good hy (h.path_ac z hz) hym
    (fun t ht => h.maps t ht hz) (hy0.trans (h.initial hz).symm) hyd (h.path_deriv z hz)

end Springer
