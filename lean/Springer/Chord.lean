import Mathlib

noncomputable section
open Set Complex MeasureTheory
open scoped ComplexConjugate
namespace Springer

/-- Normalized projection onto Z; division by zero gives the stipulated value zero. -/
def chordDirection (Z z : ℂ) : ℝ := (conj Z * z).re / ‖Z‖

theorem chordDirection_abs_le (Z : ℂ) (ξ : Circle) : |chordDirection Z ξ| ≤ 1 := by
  by_cases hz : Z = 0
  · simp [hz, chordDirection]
  have hp : 0 < ‖Z‖ := norm_pos_iff.mpr hz
  rw [chordDirection, abs_div, abs_of_pos hp, div_le_one hp]
  simpa [norm_mul] using Complex.abs_re_le_norm (conj Z * (ξ : ℂ))

theorem chord_pointwise {Φ : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) Φ)
    (Z : ℂ) (β : ℝ) (ξ : Circle) :
    Φ (‖Z+(β:ℂ)*ξ‖^2) ≤
      (1+chordDirection Z ξ)/2*Φ ((‖Z‖+β)^2) +
      (1-chordDirection Z ξ)/2*Φ ((‖Z‖-β)^2) := by
  let d := chordDirection Z ξ
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp (chordDirection_abs_le Z ξ)
  have hmul : d*‖Z‖=(conj Z*(ξ:ℂ)).re := by
    by_cases hz : Z=0
    · simp [hz,d,chordDirection]
    · exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)
  have hn : ‖Z+(β:ℂ)*(ξ:ℂ)‖^2=‖Z‖^2+β^2+2*β*(conj Z*(ξ:ℂ)).re := by
    rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul, ← Complex.sq_norm Z,
      ← Complex.sq_norm (ξ:ℂ), Circle.norm_coe]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have eqn : ‖Z+(β:ℂ)*(ξ:ℂ)‖^2 =
      ((1+d)/2)*(‖Z‖+β)^2+((1-d)/2)*(‖Z‖-β)^2 := by
    rw [hn,←hmul]; ring
  have h := hf.2 (show (‖Z‖+β)^2∈Ici (0:ℝ) from Set.mem_Ici.mpr (sq_nonneg _))
    (show (‖Z‖-β)^2∈Ici (0:ℝ) from Set.mem_Ici.mpr (sq_nonneg _))
    (show 0≤(1+d)/2 by dsimp only [d]; linarith)
    (show 0≤(1-d)/2 by dsimp only [d]; linarith)
    (show (1+d)/2+(1-d)/2=1 by ring)
  simpa only [smul_eq_mul,←eqn,d] using h

/-- A finite convex function on the closed half-line can jump at its endpoint.
This integrability argument only needs continuity in its interior. -/
theorem convex_comp_integrable_of_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {Φ : ℝ → ℝ} {Y : α → ℝ}
    (hf : ConvexOn ℝ (Ici 0) Φ) (hY : Measurable Y)
    {M : ℝ} (hM : 0≤M) (hb : ∀ x, Y x∈Icc 0 M) : Integrable (fun x => Φ (Y x)) μ := by
  let A := max (Φ 0) (Φ (2*M))
  have upper (v : ℝ) (hv : v∈Icc 0 (2*M)) : Φ v≤A :=
    hf.le_max_of_mem_Icc (Set.mem_Ici.mpr (le_refl (0:ℝ))) (by change 0≤2*M; linarith) hv
  have cont : ContinuousOn Φ (Ioi (0:ℝ)) := by simpa using hf.continuousOn_interior
  have meas := cont.measurable_piecewise (continuousOn_const (c:=Φ 0)) measurableSet_Ioi
  have meq : (fun x => Φ (Y x)) = (Ioi (0:ℝ)).piecewise Φ (fun _ => Φ 0) ∘ Y := by
    funext x
    by_cases hx : 0<Y x
    · simp [Function.comp_apply,Set.piecewise, hx]
    · have h0 : Y x=0 := le_antisymm (le_of_not_gt hx) (hb x).1
      simp [Function.comp_apply,Set.piecewise,h0]
  have hm : Measurable (fun x => Φ (Y x)) := meq ▸ meas.comp hY
  apply (integrable_const (μ:=μ) (|A|+2*|Φ M|)).mono' hm.aestronglyMeasurable
  filter_upwards with x
  obtain ⟨hx,hy⟩ := hb x
  have h₁ := upper (Y x) ⟨hx,by linarith⟩
  have h₂ := upper (2*M-Y x) ⟨by linarith,by linarith⟩
  have h₃ := hf.2 (Set.mem_Ici.mpr hx) (show 2*M-Y x∈Ici (0:ℝ) by change 0≤2*M-Y x; linarith)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul,show 1/2*Y x+1/2*(2*M-Y x)=M by ring] at h₃
  rw [Real.norm_eq_abs,abs_le]
  have ha := le_abs_self A
  have hf₀ := neg_abs_le (Φ M)
  have hf₁ := abs_nonneg (Φ M)
  constructor <;> linarith

theorem chord_integral (μ : Measure Circle) [IsProbabilityMeasure μ]
    {Φ : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) Φ) (Z : ℂ) {β : ℝ} (hβ : 0≤β) :
    (∫ ξ : Circle, Φ (‖Z+(β:ℂ)*ξ‖^2) ∂μ) ≤
      (1+chordDirection Z (∫ ξ : Circle, (ξ:ℂ) ∂μ))/2*Φ ((‖Z‖+β)^2) +
      (1-chordDirection Z (∫ ξ : Circle, (ξ:ℂ) ∂μ))/2*Φ ((‖Z‖-β)^2) := by
  let X := fun ξ : Circle => ‖Z+(β:ℂ)*ξ‖^2
  have hI := convex_comp_integrable_of_bounded μ hf (Y:=X) (by dsimp [X]; fun_prop)
    (M:=(‖Z‖+β)^2) (sq_nonneg _) (fun ξ => by
      refine ⟨sq_nonneg _,pow_le_pow_left₀ (norm_nonneg _) ?_ 2⟩
      simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hβ] using norm_add_le Z ((β:ℂ)*(ξ:ℂ)))
  have hξ : Integrable (fun ξ : Circle => (ξ:ℂ)) μ := Continuous.integrable_of_hasCompactSupport
    (by fun_prop) (HasCompactSupport.of_compactSpace _)
  have hd : Integrable (fun ξ : Circle => chordDirection Z ξ) μ := by
    exact ((hξ.const_mul (conj Z)).re).div_const _
  have hmean : (∫ ξ : Circle, chordDirection Z ξ ∂μ)=chordDirection Z (∫ ξ : Circle, (ξ:ℂ) ∂μ) := by
    unfold chordDirection
    rw [integral_div]
    have hr : (∫ ξ : Circle, (conj Z*(ξ:ℂ)).re ∂μ) =
        (∫ ξ : Circle, conj Z*(ξ:ℂ) ∂μ).re := integral_re (hξ.const_mul (conj Z))
    rw [hr, integral_const_mul]
  have hc : Integrable (fun _ : Circle => (1:ℝ)) μ := integrable_const _
  have h1 : Integrable (fun ξ : Circle => (1+chordDirection Z ξ)/2*Φ ((‖Z‖+β)^2)) μ :=
    (((hc.add hd).div_const 2).mul_const _)
  have h2 : Integrable (fun ξ : Circle => (1-chordDirection Z ξ)/2*Φ ((‖Z‖-β)^2)) μ :=
    (((hc.sub hd).div_const 2).mul_const _)
  apply (integral_mono hI (h1.add h2) (chord_pointwise hf Z β)).trans_eq
  rw [integral_add' h1 h2]
  simp only [integral_mul_const, integral_div, integral_add hc hd, integral_sub hc hd,
    integral_const, probReal_univ, one_smul, hmean]

end Springer
