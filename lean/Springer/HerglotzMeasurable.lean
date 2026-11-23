import Springer.Basic
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology ComplexConjugate
namespace Springer

def circleMoment (μ : Measure Circle) (k : ℕ) : ℂ := ∫ ξ, (ξ:ℂ)^k ∂μ

private theorem int_moment_measurable {T : Type*} [MeasurableSpace T] (μ : T → Measure Circle)
    (h : ∀ k, Measurable (fun t => circleMoment (μ t) k)) (n : ℤ) :
    Measurable (fun t => ∫ ξ, (ξ:ℂ)^n ∂μ t) := by
  cases n with
  | ofNat n => simpa [circleMoment] using h n
  | negSucc n =>
    have e (t : T) : (∫ ξ, (ξ:ℂ)^(Int.negSucc n) ∂μ t)=conj (circleMoment (μ t) (n+1)) := by
      rw [circleMoment,←integral_conj]
      apply integral_congr_ae
      filter_upwards with ξ
      rw [zpow_negSucc,map_pow,←Circle.coe_inv_eq_conj]
      simp
    simp_rw [e]
    exact Complex.continuous_conj.measurable.comp (h _)

/-- Nonnegative Fourier moments determine weak measurability of a family of circle probabilities. -/
theorem measurable_integral_of_moments {T : Type*} [MeasurableSpace T] (μ : T → Measure Circle)
    [∀ t, IsProbabilityMeasure (μ t)] (h : ∀ k, Measurable (fun t => circleMoment (μ t) k))
    (f : C(Circle,ℂ)) : Measurable (fun t => ∫ ξ, f ξ ∂μ t) := by
  let e := AddCircle.homeomorphCircle (one_ne_zero : (1:ℝ)≠0)
  let I := fun (g : C(AddCircle (1:ℝ),ℂ)) (t : T) => ∫ ξ, g (e.symm ξ) ∂μ t
  have hi (g : C(AddCircle (1:ℝ),ℂ)) (t : T) : Integrable (fun ξ => g (e.symm ξ)) (μ t) :=
    (g.continuous.comp e.symm.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have mon (n : ℤ) : Measurable (I (fourier n)) := by
    have hf (ξ : Circle) : fourier n (e.symm ξ)=(ξ:ℂ)^n := by
      rw [fourier_apply,AddCircle.toCircle_zsmul,Circle.coe_zpow,←AddCircle.homeomorphCircle_apply one_ne_zero]
      simp [e]
    simpa only [I,hf] using int_moment_measurable μ h n
  let S := Submodule.span ℂ (Set.range (fourier (T:=(1:ℝ))))
  have hm (g : C(AddCircle (1:ℝ),ℂ)) (hg : g∈S) : Measurable (I g) := by
    induction hg using Submodule.span_induction with
    | mem x hx => obtain ⟨n,rfl⟩ := hx; exact mon n
    | zero => simpa [I] using (measurable_const : Measurable (fun _ : T => (0:ℂ)))
    | add g k _ _ hg hk =>
      have e' : I (g+k)=fun t => I g t+I k t := by funext t; exact integral_add (hi g t) (hi k t)
      rw [e']; exact hg.add hk
    | smul c g _ hg =>
      have e' : I (c • g)=fun t => c*I g t := by funext t; exact integral_const_mul _ _
      rw [e']; exact measurable_const.mul hg
  let F := f.comp (⟨e,e.continuous⟩ : C(AddCircle (1:ℝ),Circle))
  have hc : F ∈ closure (S : Set C(AddCircle (1:ℝ),ℂ)) := by
    rw [←Submodule.topologicalClosure_coe,show S.topologicalClosure=⊤ from span_fourier_closure_eq_top]
    trivial
  obtain ⟨g,hg,hlim⟩ := mem_closure_iff_seq_limit.mp hc
  have cont (t : T) : LipschitzWith 1 (fun g => I g t) := by
    apply LipschitzWith.mk_one
    intro g k
    rw [dist_eq_norm,dist_eq_norm]
    change ‖(∫ ξ, g (e.symm ξ) ∂μ t) - ∫ ξ, k (e.symm ξ) ∂μ t‖ ≤ ‖g-k‖
    rw [←integral_sub (hi g t) (hi k t)]
    simpa using norm_integral_le_of_norm_le_const (μ:=μ t) (C:=‖g-k‖)
      (Filter.Eventually.of_forall (fun ξ => (g-k).norm_coe_le_norm (e.symm ξ)))
  have mF := measurable_of_tendsto_metrizable (fun n => hm (g n) (hg n))
    (tendsto_pi_nhds.mpr fun t => (cont t).continuous.continuousAt.tendsto.comp hlim)
  simpa [I,F] using mF

end Springer
