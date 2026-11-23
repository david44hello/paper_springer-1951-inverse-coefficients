import Challenge.LoewnerInput

/- Frozen input: Springer/LoewnerUnique.lean -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Springer

theorem loewner_trajectory_unique {T : ℝ} (hT : 0≤T) {p : ℝ → ℂ → ℂ}
    (hp : ∀ᵐ t ∂volume.restrict (Icc 0 T), AnalyticOnNhd ℂ (p t) disc ∧ p t 0=1 ∧
      ∀ z∈disc, 0<(p t z).re)
    {f g : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 T) (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hfD : MapsTo f (Icc 0 T) disc) (hgD : MapsTo g (Icc 0 T) disc) (he : f 0=g 0)
    (df : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt f (-f t*p t (f t)) t)
    (dg : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt g (-g t*p t (g t)) t) : EqOn f g (Icc 0 T) := by sorry

end Springer
end
