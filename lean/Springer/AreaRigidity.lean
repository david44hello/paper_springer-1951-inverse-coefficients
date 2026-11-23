import Springer.DiskConsequences

noncomputable section
open Set Filter Complex Finset
open scoped Topology
namespace Springer

/-- Exterior area estimate, indexed from zero by adding a zero summand. -/
def AreaBound (g : ℂ → ℂ) : Prop :=
  ∃ A : ℝ, A ≤ 1 ∧ HasSum (fun k : ℕ => (k:ℝ)*‖forwardCoeff g k‖^2) A

private theorem AreaBound.finite_sum {g : ℂ → ℂ} (h : AreaBound g) (s : Finset ℕ) :
    ∑ k ∈ s, (k:ℝ)*‖forwardCoeff g k‖^2 ≤ 1 := by
  obtain ⟨A, hA, hsum⟩ := h
  exact (sum_le_hasSum s (fun _ _ => by positivity) hsum).trans hA

theorem AreaBound.first_le_one {g : ℂ → ℂ} (h : AreaBound g) : ‖forwardCoeff g 1‖ ≤ 1 := by
  have H := h.finite_sum {1}
  simp only [sum_singleton, Nat.cast_one, one_mul] at H
  nlinarith [norm_nonneg (forwardCoeff g 1)]

theorem AreaBound.higher_vanish {g : ℂ → ℂ} (h : AreaBound g)
    (hb : ‖forwardCoeff g 1‖=1) {k : ℕ} (hk : 2≤k) : forwardCoeff g k=0 := by
  have h₁ : 1≠k := by omega
  have H := h.finite_sum {1,k}
  simp [h₁,hb] at H
  by_contra hn
  have ht : 0<(k:ℝ)*‖forwardCoeff g k‖^2 := mul_pos (by exact_mod_cast (show 0<k by omega))
    (pow_pos (norm_pos_iff.mpr hn) _)
  linarith

private theorem taylor_hasSum_near {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∀ᶠ t in 𝓝 (0:ℂ), HasSum (fun n : ℕ => taylorCoeff f n*t^n) (f t) := by
  filter_upwards [hf.hasFPowerSeriesAt.eventually_hasSum_sub] with t ht
  simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, FormalMultilinearSeries.coeff_ofScalars,
    sub_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_comm,taylorCoeff] using ht

theorem eqOn_slit_of_higher_vanish {g : ℂ → ℂ} (hg : Sigma g)
    (hv : ∀ k, 2≤k → forwardCoeff g k=0) :
    EqOn g (slitMap (forwardCoeff g 1)) exterior := by
  let b := forwardCoeff g 1
  let f := fun t : ℂ => 1+b*t^2
  have hf : AnalyticOnNhd ℂ f disc := by intro t ht; dsimp [f]; fun_prop
  have h0 : (0:ℂ) ∈ disc := by simp [disc]
  have hcoeff (n : ℕ) : taylorCoeff (profile g) n = taylorCoeff f n := by
    have hp : taylorCoeff f n = (if n=0 then 1 else 0) + b*(if n=2 then 1 else 0) := by
      dsimp only [f]
      rw [taylorCoeff_add (f:=fun _ : ℂ => 1) (g:=fun t : ℂ => b*t^2) (by fun_prop) (by fun_prop),
        taylorCoeff_const_mul, taylorCoeff_pow]
      by_cases hn : n=0
      · subst n; simp
      · simp [hn,taylorCoeff,iteratedDeriv_const]
    rw [hp]
    match n with
    | 0 => simp
    | 1 => simp [taylorCoeff, hg.centered]
    | 2 => simp [b,forwardCoeff]
    | n+3 =>
      have h := hv (n+2) (by omega)
      simpa [forwardCoeff] using h
  have he : profile g =ᶠ[𝓝 0] f := by
    filter_upwards [taylor_hasSum_near (hg.regular _ h0), taylor_hasSum_near (hf _ h0)] with t h₁ h₂
    simp only [hcoeff] at h₁
    exact h₁.unique h₂
  have heq := hg.regular.eqOn_of_preconnected_of_eventuallyEq hf
    (show IsPreconnected disc from (convex_ball (0:ℂ) 1).isPreconnected) h0 he
  intro z hz
  have hpos : 0<‖z‖ := zero_lt_one.trans hz
  have hn := norm_pos_iff.mp hpos
  have hz' : z⁻¹ ∈ disc := by
    change z⁻¹ ∈ Metric.ball (0:ℂ) 1
    rw [Metric.mem_ball,dist_zero_right,norm_inv]
    exact (inv_lt_one₀ hpos).mpr hz
  have H := heq hz'
  rw [profile,ite_eq_right (inv_ne_zero hn),inv_inv] at H
  change z⁻¹*g z=1+b*(z⁻¹)^2 at H
  change g z=z+b/z
  field_simp [hn] at H ⊢
  linear_combination H

theorem AreaBound.eqOn_rotated_slit {g : ℂ → ℂ} (h : AreaBound g) (hg : Sigma g)
    (hb : ‖forwardCoeff g 1‖=1) :
    ∃ θ : ℝ, EqOn g (slitMap (Complex.exp ((θ:ℂ)*I))) exterior := by
  refine ⟨(forwardCoeff g 1).arg, ?_⟩
  have hx := Complex.norm_mul_exp_arg_mul_I (forwardCoeff g 1)
  rw [hb,Complex.ofReal_one,one_mul] at hx
  rw [hx]
  exact eqOn_slit_of_higher_vanish hg (fun _ hk => h.higher_vanish hb hk)

theorem odd_equality_slit_of_area_and_disk {g : ℂ → ℂ} (hg : Sigma g) (ha : AreaBound g)
    {m : ℕ} (hd : DiskBound g m) (he : ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ)) :
    ∃ θ : ℝ, EqOn g (slitMap (Complex.exp ((θ:ℂ)*I))) exterior :=
  ha.eqOn_rotated_slit hg (hd.firstCoeff_of_equality ha.first_le_one he)

theorem inverseCoeff_eq_of_eqOn_exterior {g f : ℂ → ℂ} (hg : Sigma g) (hf : Sigma f)
    (he : EqOn g f exterior) (n : ℕ) : inverseCoeff g n=inverseCoeff f n := by
  apply taylorCoeff_congr
  filter_upwards [eventually_nhdsWithin_iff.mp (inverse_germ hg).2.2.2] with t ht
  by_cases hn : t=0
  · simp [hn,inverseProfile]
  obtain ⟨hz, hv⟩ := ht hn
  have hfv := (he hz).symm.trans hv
  have hinv := hf.univalent.leftInvOn_invFunOn hz
  rw [hfv] at hinv
  simp only [inverseProfile,profile,ite_eq_right hn,hinv]

theorem odd_equality_of_eqOn_rotated_slit {g : ℂ → ℂ} (hg : Sigma g) (θ : ℝ)
    (he : EqOn g (slitMap (Complex.exp ((θ:ℂ)*I))) exterior) (m : ℕ) :
    ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ) := by
  have hb := Complex.norm_exp_ofReal_mul_I θ
  rw [inverseCoeff_eq_of_eqOn_exterior hg (slit_sigma hb.le) he]
  exact slit_odd_attains hb m

end Springer
