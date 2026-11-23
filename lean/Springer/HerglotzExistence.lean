import Springer.HerglotzRadial
import Springer.HerglotzFamily
noncomputable section
open Set Metric Filter MeasureTheory Complex
open scoped Topology
namespace Springer

/-- Classical Herglotz representation on the open disk obtained by weak compactness
of the probability laws of its radial restrictions. -/
theorem herglotz_representation : HerglotzRepresentation := by
  intro f hf h0 hp
  let r := fun n : ℕ => (1:ℝ)-1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 ≤ r n ∧ r n < 1 := by
    dsimp [r]
    constructor
    · have h := (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (by linarith [Nat.cast_nonneg (α:=ℝ) n] : (1:ℝ)≤n+1))
      linarith
    · have : (0:ℝ)<1/((n:ℝ)+1) := by positivity
      linarith
  have hr1 : Tendsto r atTop (𝓝 1) := by
    simpa [r] using (tendsto_const_nhds (x:=(1:ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  let F := fun (n : ℕ) (z : ℂ) => f ((r n:ℂ)*z)
  have maps (n : ℕ) : MapsTo (fun z : ℂ => (r n:ℂ)*z) (closedBall 0 1) disc := by
    intro z hz
    rw [mem_closedBall,dist_zero_right] at hz
    change _ ∈ ball (0:ℂ) 1
    rw [mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hr n).1]
    exact (mul_le_of_le_one_right (hr n).1 hz).trans_lt (hr n).2
  have hF (n : ℕ) : DiffContOnCl ℂ (F n) disc := by
    have hd : DifferentiableOn ℂ (F n) (closedBall 0 1) :=
      hf.differentiableOn.comp (by fun_prop) (maps n)
    exact DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn
  have rep (n : ℕ) := herglotz_closed_disk (hF n) (by simp [F,h0]) (by
    intro ξ; exact (hp _ (maps n (by simp))).le)
  choose ν hν using rep
  obtain ⟨μ,φ,hmono,hlim⟩ := CompactSpace.tendsto_subseq ν
  refine ⟨μ,?_⟩
  intro z hz
  let k : BoundedContinuousFunction Circle ℂ := BoundedContinuousFunction.mkOfCompact
    ⟨fun ξ => (1+(ξ:ℂ)*z)/(1-(ξ:ℂ)*z),circle_kernel_continuous hz⟩
  have htest := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim k
  have hval : Tendsto (fun n => F (φ n) z) atTop (𝓝 (f z)) := by
    apply (hf z hz).continuousAt.tendsto.comp
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hr1.comp hmono.tendsto_atTop)).mul_const z
    simpa using hh
  have target : Tendsto (fun n => F (φ n) z) atTop (𝓝 (herglotzTransform (μ : Measure Circle) z)) := by
    apply htest.congr'
    exact Eventually.of_forall (fun n => (hν (φ n) hz).symm)
  exact tendsto_nhds_unique hval target

end Springer
