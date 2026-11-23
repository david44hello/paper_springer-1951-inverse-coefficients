import Springer.HerglotzExistence
import Springer.TimeChange
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Springer

/-- Measurable selection for the Lebesgue-time formulation: each slice is only
assumed measurable up to a null set. A countable dense set gives common Borel
representatives, before taking derivatives or selecting circle measures. -/
theorem herglotz_measurable_probabilities {T : Type*} [MeasurableSpace T] (ν : Measure T) {p : T → ℂ → ℂ}
    (hm : ∀ z∈disc, AEMeasurable (fun t => p t z) ν)
    (ha : ∀ᵐ t ∂ν, AnalyticOnNhd ℂ (p t) disc ∧ p t 0=1 ∧ ∀ z∈disc, 0<(p t z).re) :
    ∃ (μ : T → Measure Circle) (N : Set T), MeasurableSet N ∧ ν N=0 ∧
      (∀ t, IsProbabilityMeasure (μ t)) ∧ (∀ t∈N, μ t=Measure.dirac 1) ∧
      (∀ t∉N, EqOn (p t) (herglotzTransform (μ t)) disc) ∧
      ∀ f : C(Circle,ℂ), Measurable (fun t => ∫ ξ, f ξ ∂μ t) := by
  classical
  obtain ⟨s,hcount,hsub,hdense⟩ := TopologicalSpace.exists_countable_dense_subset disc
  let F := fun z : s => (hm z (hsub z.property)).mk (fun t => p t z)
  have hall : ∀ᵐ t ∂ν, ∀ z∈s, ∀ h : z∈s, p t z=F ⟨z,h⟩ t := by
    apply (ae_ball_iff hcount).mpr
    intro z hz
    filter_upwards [(hm z (hsub hz)).ae_eq_mk] with t ht
    exact fun _ => ht
  obtain ⟨B,hBsub,hB,hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp (ha.and hall))
  have good (t : T) (ht : t∉B) : (AnalyticOnNhd ℂ (p t) disc ∧ p t 0=1 ∧ ∀ z∈disc, 0<(p t z).re) ∧
      ∀ z∈s, ∀ h : z∈s, p t z=F ⟨z,h⟩ t := by
    by_contra h
    exact ht (hBsub h)
  let q := fun (t : T) (z : ℂ) => if t∈B then 1 else p t z
  have qa (t : T) : AnalyticOnNhd ℂ (q t) disc := by
    by_cases ht : t∈B
    · simpa [q,ht] using (analyticOnNhd_const (v:=(1:ℂ)) (s:=disc) (𝕜:=ℂ))
    · simpa [q,ht] using (good t ht).1.1
  have qm (z : ℂ) (hz : z∈disc) : Measurable (fun t => q t z) := by
    obtain ⟨w,hw,hlim⟩ := mem_closure_iff_seq_limit.mp (hdense hz)
    have hwm (i : ℕ) : Measurable (fun t => q t (w i)) := by
      have e : (fun t => q t (w i))=fun t => if t∈B then 1 else F ⟨w i,hw i⟩ t := by
        funext t
        by_cases ht : t∈B
        · simp [q,ht]
        · simp [q,ht,(good t ht).2 _ (hw i) (hw i)]
      rw [e]
      exact Measurable.ite hB measurable_const (hm (w i) (hsub (hw i))).measurable_mk
    exact measurable_of_tendsto_metrizable hwm
      (tendsto_pi_nhds.mpr fun t => ((qa t z hz).continuousAt.tendsto.comp hlim))
  have qgood : ∀ᵐ t ∂ν, AnalyticOnNhd ℂ (q t) disc ∧ q t 0=1 ∧ ∀ z∈disc, 0<(q t z).re :=
    ae_of_all _ fun t => by
      by_cases ht : t∈B
      · simp [q,ht,analyticOnNhd_const]
      · simpa [q,ht] using (good t ht).1
  obtain ⟨μ,N,hN,hN0,hμ,hδ,hrep,hw⟩ := herglotz_family ν qm qgood herglotz_representation
  let laws := fun t => if t∈B then Measure.dirac (1:Circle) else μ t
  refine ⟨laws,B∪N,hB.union hN,measure_union_null hnull hN0,?_,?_,?_,?_⟩
  · intro t; dsimp [laws]; split <;> first | infer_instance | exact hμ t
  · intro t ht
    by_cases hb : t∈B
    · simp [laws,hb]
    · simp [laws,hb,hδ t (ht.resolve_left hb)]
  · intro t ht
    have hb : t∉B := fun h => ht (Or.inl h)
    have hn : t∉N := fun h => ht (Or.inr h)
    simpa [q,laws,hb] using hrep t hn
  · intro f
    have e : (fun t => ∫ ξ, f ξ ∂laws t) = fun t => if t∈B then f 1 else ∫ ξ, f ξ ∂μ t := by
      funext t; by_cases ht : t∈B <;> simp [laws,ht]
    rw [e]; exact Measurable.ite hB measurable_const (hw f)

end Springer
