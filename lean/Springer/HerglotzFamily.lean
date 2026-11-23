import Springer.HerglotzCoefficients
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Springer

theorem measurable_taylorCoeff {T : Type*} [MeasurableSpace T] {p : T → ℂ → ℂ}
    (hm : ∀ z∈disc, Measurable (fun t => p t z)) (ha : ∀ t, AnalyticOnNhd ℂ (p t) disc)
    (n : ℕ) : Measurable (fun t => taylorCoeff (p t) n) := by
  classical
  have hd (k : ℕ) : ∀ z∈disc, Measurable (fun t => iteratedDeriv k (p t) z) := by
    induction k with
    | zero => simpa using hm
    | succ k ih =>
      intro z hz
      simp only [iteratedDeriv_succ]
      let q := fun (y : ℂ) (t : T) => if y∈disc then slope (iteratedDeriv k (p t)) z y else 0
      apply measurable_of_tendsto_metrizable' (𝓝[≠] z) (f:=q)
      · intro y
        by_cases hy : y∈disc
        · simp only [q,if_pos hy,slope_def_field]
          exact ((ih y hy).sub (ih z hz)).div_const _
        · simp only [q,if_neg hy]; exact measurable_const
      · apply tendsto_pi_nhds.mpr
        intro t
        have d := (((ha t).iterated_deriv k z hz).differentiableAt.hasDerivAt).tendsto_slope
        rw [←iteratedDeriv_eq_iterate] at d
        apply d.congr'
        filter_upwards [mem_nhdsWithin_of_mem_nhds ((Metric.isOpen_ball).mem_nhds hz)] with y hy
        change y∈disc at hy
        simp [q,hy]
  exact (hd n 0 (by simp [disc])).div_const _

/-- The single-time classical representation input in the orientation used by the manuscript. -/
def HerglotzRepresentation : Prop :=
  ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f disc → f 0=1 → (∀ z∈disc, 0<(f z).re) →
    ∃ ν : ProbabilityMeasure Circle, EqOn f (herglotzTransform (ν : Measure Circle)) disc

/-- Extract the measurable family from a pointwise representation without assuming
measurability of the measure selection. On the common null set use point mass at 1. -/
theorem herglotz_family {T : Type*} [MeasurableSpace T] (timeMeasure : Measure T) {p : T → ℂ → ℂ}
    (hm : ∀ z∈disc, Measurable (fun t => p t z))
    (ha : ∀ᵐ t ∂timeMeasure, AnalyticOnNhd ℂ (p t) disc ∧ p t 0=1 ∧ ∀ z∈disc, 0<(p t z).re)
    (hrep : HerglotzRepresentation) :
    ∃ (μ : T → Measure Circle) (N : Set T), MeasurableSet N ∧ timeMeasure N=0 ∧
      (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t∈N, μ t=Measure.dirac 1) ∧
      (∀ t∉N, EqOn (p t) (herglotzTransform (μ t)) disc) ∧
      ∀ f : C(Circle,ℂ), Measurable (fun t => ∫ ξ, f ξ ∂μ t) := by
  classical
  obtain ⟨N,hsub,hN,hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp ha)
  have good (t : T) (ht : t∉N) :
      AnalyticOnNhd ℂ (p t) disc ∧ p t 0=1 ∧ ∀ z∈disc, 0<(p t z).re := by
    by_contra h
    exact ht (hsub h)
  have chooseRep (t : T) (ht : t∉N) := hrep (p t) (good t ht).1 (good t ht).2.1 (good t ht).2.2
  let μ := fun t => if ht : t∈N then Measure.dirac (1:Circle) else ((chooseRep t ht).choose : Measure Circle)
  have prob (t : T) : IsProbabilityMeasure (μ t) := by dsimp [μ]; split <;> infer_instance
  have repr (t : T) (ht : t∉N) : EqOn (p t) (herglotzTransform (μ t)) disc := by
    simpa [μ,ht] using (chooseRep t ht).choose_spec
  refine ⟨μ,N,hN,hnull,prob,fun t ht => by simp [μ,ht],repr,?_⟩
  let P := fun (t : T) (z : ℂ) => if t∈N then (1+z)/(1-z) else p t z
  have hpm (z : ℂ) (hz : z∈disc) : Measurable (fun t => P t z) := Measurable.ite hN measurable_const (hm z hz)
  have hpa (t : T) : AnalyticOnNhd ℂ (P t) disc := by
    by_cases ht : t∈N
    · intro z hz
      have hn : 1-z≠0 := by intro e; have := sub_eq_zero.mp e; subst z; simpa [disc] using hz
      simp only [P,if_pos ht]
      fun_prop (disch := exact hn)
    · simpa only [P,if_neg ht] using (good t ht).1
  have eq (t : T) : EqOn (P t) (herglotzTransform (μ t)) disc := by
    intro z hz
    by_cases ht : t∈N
    · simp [P,ht,μ,herglotzTransform]
    · simpa [P,ht] using repr t ht hz
  apply measurable_integral_of_moments μ
  intro k
  cases k with
  | zero => simpa [circleMoment] using (measurable_const : Measurable (fun _ : T => (1:ℂ)))
  | succ k =>
    have e (t : T) : circleMoment (μ t) (k+1)= taylorCoeff (P t) (k+1)/2 := by
      have he := Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds (0:ℂ) (show 0<(1:ℝ) by norm_num)) (eq t)
      rw [taylorCoeff_congr he,herglotz_taylor]; ring
    simp_rw [e]
    exact (measurable_taylorCoeff hpm hpa _).div_const _

end Springer
