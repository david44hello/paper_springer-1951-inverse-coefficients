import Springer.HerglotzTime
import Springer.FlowNormalization
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Springer

/-- The portion of the classical normalized disk Loewner representation used in
the proof. The time interval is [0, log(1/ρ)]. The field p is permitted to have
Lebesgue-measurable scalar slices. No conclusion about Laurent coefficients is a field. -/
structure NormalizedLoewnerData (ψ : ℂ → ℂ) (ρ : ℝ) (p φ : ℝ → ℂ → ℂ) : Prop where
  p_meas : ∀ z∈disc, AEMeasurable (fun l => p l z) (volume.restrict (Icc 0 (Real.log (1/ρ))))
  p_good : ∀ᵐ l ∂volume.restrict (Icc 0 (Real.log (1/ρ))),
    AnalyticOnNhd ℂ (p l) disc ∧ p l 0=1 ∧ ∀ z∈disc, 0<(p l z).re
  initial : EqOn (φ 0) id disc
  terminal : EqOn (φ (Real.log (1/ρ))) ψ disc
  maps : ∀ l∈Icc 0 (Real.log (1/ρ)), MapsTo (φ l) disc disc
  univalent : ∀ l∈Icc 0 (Real.log (1/ρ)), InjOn (φ l) disc
  analytic : ∀ l∈Icc 0 (Real.log (1/ρ)), AnalyticOnNhd ℂ (φ l) disc
  fixed_zero : ∀ l∈Icc 0 (Real.log (1/ρ)), φ l 0=0
  at_origin : ∀ l∈Icc 0 (Real.log (1/ρ)), HasDerivAt (φ l) (Real.exp (-l):ℂ) 0
  path_ac : ∀ z∈disc, AbsolutelyContinuousOnInterval (fun l => φ l z) 0 (Real.log (1/ρ))
  path_deriv : ∀ z∈disc, ∀ᵐ l ∂volume.restrict (Icc 0 (Real.log (1/ρ))),
    HasDerivAt (fun s => φ s z) (-φ l z*p l (φ l z)) l

/-- Classical existence premise. Theorem B and the normalized ODE in §2.2 of
Gumenyuk, arXiv:1603.04043. Source time is rescaled by ℓ/log(1/ρ). -/
def NormalizedLoewnerRepresentation : Prop :=
  ∀ (ψ : ℂ → ℂ) (ρ : ℝ), 0<ρ → ρ<1 → AnalyticOnNhd ℂ ψ disc → MapsTo ψ disc disc →
    InjOn ψ disc → ψ 0=0 → HasDerivAt ψ (ρ:ℂ) 0 → ∃ p φ, NormalizedLoewnerData ψ ρ p φ

theorem normalizedLoewner_of_omitted_disk (hL : NormalizedLoewnerRepresentation)
    {g : ℂ → ℂ} (hg : Sigma g) (w : ℂ) {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1)
    (hom : ∀ z∈exterior, ρ<‖g z-w‖) :
    ∃ p φ, NormalizedLoewnerData (flowDiskMap g w ρ) ρ p φ := by
  obtain ⟨ha,hm,hi,hd⟩ := flowDiskMap_properties hg hρ hom
  exact hL _ ρ hρ hρ1 ha hm hi (flowDiskMap_zero g w ρ) hd

/-- At the elapsed-time argument the same probability law works for all spatial
points in the kernel formula. The ODE itself may have an exceptional set for
each chosen trajectory, as in the classical initial-value theorem. -/
theorem NormalizedLoewnerData.circle_laws {ψ : ℂ → ℂ} {ρ : ℝ} {p φ : ℝ → ℂ → ℂ}
    (h : NormalizedLoewnerData ψ ρ p φ) (hρ : 0<ρ) :
    ∃ μ : ℝ → Measure Circle, (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ f : C(Circle,ℂ), Measurable (fun t => ∫ ξ, f ξ ∂μ t)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (ρ^2) 1), EqOn (p (elapsed t)) (herglotzTransform (μ t)) disc) ∧
      ∀ z∈disc, ∀ᵐ t ∂volume.restrict (Icc (ρ^2) 1),
        HasDerivAt (fun s => φ s z) (-φ (elapsed t) z *
          (∫ ξ, flowKernel (φ (elapsed t) z) ξ ∂μ t)) (elapsed t) := by
  let J := Icc (0:ℝ) (Real.log (1/ρ))
  obtain ⟨ν,N,hN,h0,hprob,_,hrep,hweak⟩ :=
    herglotz_measurable_probabilities (volume.restrict J) h.p_meas h.p_good
  refine ⟨fun t => ν (elapsed t),fun t => hprob _,?_,?_,?_⟩
  · intro f; exact (hweak f).comp (by unfold elapsed; fun_prop)
  · apply elapsed_ae hρ (p:=fun l => EqOn (p l) (herglotzTransform (ν l)) disc)
    have hn : ∀ᵐ l ∂volume.restrict J, l∉N := by simpa [ae_iff] using h0
    exact hn.mono (fun l hl => hrep l hl)
  · intro z hz
    apply elapsed_ae hρ (p:=fun l => HasDerivAt (fun s => φ s z) (-φ l z*(∫ ξ, flowKernel (φ l z) ξ ∂ν l)) l)
    have hn : ∀ᵐ l ∂volume.restrict J, l∉N := by simpa [ae_iff] using h0
    filter_upwards [h.path_deriv z hz,hn,ae_restrict_mem measurableSet_Icc] with l hd hln hlJ
    rw [hrep l hln (h.maps l hlJ hz)] at hd
    exact hd

end Springer
