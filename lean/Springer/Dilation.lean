import Springer.Coefficients

noncomputable section
open Set Filter Function Complex
open scoped Topology
namespace Springer

/-- Restrict the original exterior map to a smaller exterior domain and renormalize. -/
def dilateMap (g : ℂ → ℂ) (R : ℝ) (z : ℂ) := g ((R:ℂ)*z)/(R:ℂ)

private theorem scale_exterior {R : ℝ} (hR : 1 < R) {z : ℂ} (hz : z ∈ exterior) :
    (R:ℂ)*z ∈ exterior := by
  change 1 < ‖z‖ at hz
  change 1 < ‖(R:ℂ)*z‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0<R)]
  exact one_lt_mul_of_lt_of_le hR hz.le

theorem profile_dilateMap (g : ℂ → ℂ) {R : ℝ} (hR : 0 < R) (t : ℂ) :
    profile (dilateMap g R) t = profile g (t/(R:ℂ)) := by
  have hn : (R:ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  by_cases ht : t=0
  · simp [ht]
  simp only [profile, ite_eq_right ht, ite_eq_right (div_ne_zero ht hn), dilateMap, inv_div]
  rw [div_eq_mul_inv (R:ℂ) t]
  ring

theorem Sigma.dilateMap {g : ℂ → ℂ} (hg : Sigma g) {R : ℝ} (hR : 1 < R) :
    Sigma (dilateMap g R) := by
  have hr : 0<R := by linarith
  have hn : (R:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have pro : profile (Springer.dilateMap g R) = fun t => profile g (t/(R:ℂ)) :=
    funext (profile_dilateMap g hr)
  constructor
  · intro z hz
    exact ((hg.analytic _ (scale_exterior hR hz)).comp ((analyticAt_const.mul analyticAt_id))).div
      analyticAt_const hn
  · intro z hz w hw he
    apply mul_left_cancel₀ hn
    apply hg.univalent (scale_exterior hR hz) (scale_exterior hR hw)
    exact (div_left_inj' hn).mp he
  · rw [pro]
    intro t ht
    have htd : t/(R:ℂ) ∈ disc := by
      change t ∈ Metric.ball (0:ℂ) 1 at ht
      rw [Metric.mem_ball, dist_zero_right] at ht
      change t/(R:ℂ) ∈ Metric.ball (0:ℂ) 1
      rw [Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, div_lt_iff₀ hr]
      linarith
    have hq : AnalyticAt ℂ (fun z : ℂ => z/(R:ℂ)) t := by fun_prop (disch := exact hn)
    exact (hg.regular _ htd).comp (f := fun z : ℂ => z/(R:ℂ)) hq
  · rw [pro]
    have ha := (hg.regular 0 (by simp [disc])).differentiableAt.hasDerivAt
    rw [hg.centered] at ha
    have hs := (hasDerivAt_id (0:ℂ)).div_const (R:ℂ)
    simpa [Function.comp_def] using (ha.comp_of_eq 0 hs (by simp)).deriv

private theorem iteratedDeriv_scaled (f : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t => f (a*t)) = fun t => a^n * iteratedDeriv n f (a*t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext t
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left]
    simp only [iteratedDeriv_succ, smul_eq_mul, pow_succ]
    ring

theorem taylorCoeff_div_arg (f : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    taylorCoeff (fun t => f (t/a)) n = taylorCoeff f n / a^n := by
  have eqn : (fun t => f (t/a)) = fun t => f (a⁻¹*t) := by
    funext t; rw [div_eq_inv_mul]
  rw [eqn, taylorCoeff, iteratedDeriv_scaled]
  simp only [mul_zero, taylorCoeff, inv_pow, div_eq_mul_inv]
  ring

theorem forwardCoeff_dilateMap (g : ℂ → ℂ) {R : ℝ} (hR : 1 < R) (n : ℕ) :
    forwardCoeff (dilateMap g R) n = forwardCoeff g n / (R:ℂ)^(n+1) := by
  unfold forwardCoeff
  rw [funext (profile_dilateMap g (by linarith : 0<R)), taylorCoeff_div_arg]

theorem inverseProfile_dilateMap {g : ℂ → ℂ} (hg : Sigma g) {R : ℝ} (hR : 1<R) :
    inverseProfile (dilateMap g R) =ᶠ[𝓝 0] fun t => inverseProfile g (t/(R:ℂ)) := by
  have hn : (R:ℂ) ≠ 0 := by exact_mod_cast (show R≠0 by linarith)
  have H := (inverse_germ (hg.dilateMap hR)).2.2.2
  filter_upwards [eventually_nhdsWithin_iff.mp H] with t ht
  by_cases ht0 : t=0
  · simp [ht0,inverseProfile]
  obtain ⟨hz, he⟩ := ht ht0
  let z := invFunOn (dilateMap g R) exterior t⁻¹
  have hgval : g ((R:ℂ)*z) = (t/(R:ℂ))⁻¹ := by
    change g ((R:ℂ)*z)/(R:ℂ)=t⁻¹ at he
    rw [inv_div]
    calc
      _ = t⁻¹*(R:ℂ) := (div_eq_iff hn).mp he
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hinv := hg.univalent.leftInvOn_invFunOn (scale_exterior hR hz)
  change invFunOn g exterior (g ((R:ℂ)*z))=(R:ℂ)*z at hinv
  rw [hgval] at hinv
  simp only [inverseProfile, profile, ite_eq_right ht0, ite_eq_right (div_ne_zero ht0 hn), hinv]
  change t*z=t/(R:ℂ)*((R:ℂ)*z)
  field_simp

theorem inverseCoeff_dilateMap {g : ℂ → ℂ} (hg : Sigma g) {R : ℝ} (hR : 1<R) (n : ℕ) :
    inverseCoeff (dilateMap g R) n = inverseCoeff g n / (R:ℂ)^(n+1) := by
  unfold inverseCoeff
  rw [taylorCoeff_congr (inverseProfile_dilateMap hg hR), taylorCoeff_div_arg]

/-- The strict version of omitting the closed disk used in Section 3. -/
def OmitsDisk (g : ℂ → ℂ) : Prop :=
  ∃ w : ℂ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ z ∈ exterior, ρ < ‖g z - w‖

theorem dilateMap_omitsDisk {g : ℂ → ℂ} (hg : Sigma g) {R : ℝ} (hR : 1 < R) :
    OmitsDisk (dilateMap g R) := by
  have hr : 0<R := by linarith
  have hn : (R:ℂ)≠0 := by exact_mod_cast hr.ne'
  let F := fun z => g z/(R:ℂ)
  let S := {z : ℂ | 1<‖z‖ ∧ ‖z‖<R}
  let a : ℂ := (((1+R)/2:ℝ):ℂ)
  have ha : ‖a‖=(1+R)/2 := by
    exact (Complex.norm_real _).trans ((Real.norm_eq_abs _).trans (abs_of_pos (by linarith)))
  have has : a ∈ S := by change 1<‖a‖ ∧ ‖a‖<R; rw [ha]; constructor <;> linarith
  have hS : S ∈ 𝓝 a :=
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).mem_nhds has
  have inj : InjOn F exterior := fun x hx y hy e => hg.univalent hx hy ((div_left_inj' hn).mp e)
  have hF : AnalyticAt ℂ F a := (hg.analytic a has.1).div analyticAt_const hn
  have him : F '' S ∈ 𝓝 (F a) := by
    rcases hF.eventually_constant_or_nhds_le_map_nhds with h | h
    · have he : ∀ᶠ z in 𝓝[≠] a, z=a := by
        filter_upwards [h.filter_mono nhdsWithin_le_nhds, mem_nhdsWithin_of_mem_nhds hS]
          with z he hz
        exact inj hz.1 has.1 he
      obtain ⟨z, hza, hnz⟩ := (he.and (self_mem_nhdsWithin : {a}ᶜ ∈ 𝓝[≠] a)).exists
      exact False.elim (hnz hza)
    · exact h (image_mem_map hS)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp him
  let ρ := min (ε/2) (1/2)
  refine ⟨F a, ρ, lt_min (by linarith) (by norm_num), (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro z hz
  by_contra! hb
  have small : ‖dilateMap g R z-F a‖ < ε := lt_of_le_of_lt hb
    ((min_le_left _ _).trans_lt (by linarith))
  have hmem : dilateMap g R z ∈ Metric.ball (F a) ε := by simpa [Metric.mem_ball,dist_eq_norm] using small
  obtain ⟨v,hv,he⟩ := hball hmem
  have eqn : v=(R:ℂ)*z := inj hv.1 (scale_exterior hR hz) he
  have hz' : R<‖(R:ℂ)*z‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    simpa using mul_lt_mul_of_pos_left (show 1<‖z‖ from hz) hr
  exact (not_lt_of_ge hz'.le) (eqn ▸ hv.2)

/-- Extending any closed constraint on a forward/inverse coefficient pair from the
omitted-disk subclass to the full class. -/
theorem closed_coeff_constraint {C : Set (ℂ × ℂ)} (hC : IsClosed C) (i j : ℕ)
    (h : ∀ g : ℂ → ℂ, Sigma g → OmitsDisk g → (forwardCoeff g i, inverseCoeff g j) ∈ C)
    {g : ℂ → ℂ} (hg : Sigma g) : (forwardCoeff g i, inverseCoeff g j) ∈ C := by
  let pair := fun R : ℝ => (forwardCoeff g i / (R:ℂ)^(i+1), inverseCoeff g j / (R:ℂ)^(j+1))
  have ht : ContinuousAt pair 1 := by dsimp [pair]; fun_prop (disch := norm_num)
  have hm : ∀ᶠ R in 𝓝[>] (1:ℝ), pair R ∈ C := by
    filter_upwards [self_mem_nhdsWithin] with R (hR : 1<R)
    simpa only [pair, forwardCoeff_dilateMap g hR, inverseCoeff_dilateMap hg hR]
      using h (dilateMap g R) (hg.dilateMap hR) (dilateMap_omitsDisk hg hR)
  have h1 := hC.mem_of_tendsto (ht.tendsto.mono_left nhdsWithin_le_nhds) hm
  simpa [pair] using h1

end Springer
