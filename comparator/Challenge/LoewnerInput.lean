import Challenge.HerglotzExistence
import Challenge.TimeChange
import Challenge.FlowNormalization

/- Frozen input: Springer/LoewnerInput.lean -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Springer

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

def NormalizedLoewnerRepresentation : Prop :=
  ∀ (ψ : ℂ → ℂ) (ρ : ℝ), 0<ρ → ρ<1 → AnalyticOnNhd ℂ ψ disc → MapsTo ψ disc disc →
    InjOn ψ disc → ψ 0=0 → HasDerivAt ψ (ρ:ℂ) 0 → ∃ p φ, NormalizedLoewnerData ψ ρ p φ

end Springer
end
