import Springer.Basic
noncomputable section
open Complex Real Set Metric MeasureTheory Filter
open scoped Topology
namespace Springer

/-- Schwarz's integral formula on the unit circle, in the normalization f(0)=1. -/
theorem schwarz_average {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f disc) (f0 : f 0=1) {z : ℂ} (hz : z∈disc) :
    Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • ((f ζ).re:ℂ)) 0 1=f z := by
  let K := fun z => Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • ((f ζ).re:ℂ)) 0 1
  have hsubset : sphere (0:ℂ) (1:ℝ) ⊆ closure disc := by
    rw [disc,closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)]
    exact sphere_subset_closedBall
  have hc := hf.continuousOn.mono hsubset
  have hR : CircleIntegrable (fun ζ => (f ζ).re) 0 1 := (continuous_re.comp_continuousOn hc).circleIntegrable (by norm_num)
  have hC : CircleIntegrable (fun ζ => ((f ζ).re:ℂ)) 0 1 :=
    (continuous_ofReal.comp_continuousOn (continuous_re.comp_continuousOn hc)).circleIntegrable (by norm_num)
  have hns {w : ℂ} (hw : w∈disc) : w∉sphere (0:ℂ) |(1:ℝ)| := by
    rw [abs_one]; exact sphere_disjoint_ball.notMem_of_mem_right hw
  have hk : AnalyticOnNhd ℂ K disc :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hC).mono (fun _ hw => hns hw)
  have hpo (w : ℂ) (hw : w∈disc) : (K w).re=(f w).re := by
    rw [show K w=_ from rfl,re_circleAverage_herglotzRieszKernel_smul hR (hns hw)]
    have po := hf.circleAverage_re_herglotzRieszKernel_smul hw
    have hi : CircleIntegrable ((Complex.re ∘ herglotzRieszKernel 0 w) • f) 0 1 :=
      (hc.circleIntegrable (by norm_num)).continuousOn_smul (continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere (hns hw)))
    have eq := Complex.reCLM.circleAverage_comp_comm hi
    rw [po] at eq
    simpa [Function.comp_def,Complex.real_smul,Pi.smul_def,Pi.mul_def] using eq
  have diff := hk.sub (hf.differentiableOn.analyticOnNhd isOpen_ball)
  obtain ⟨c,hcst⟩ := diff.eq_const_of_re_eq_const (c₀:=0)
    (by intro w hw; simp [hpo w hw]) isOpen_ball ((convex_ball (0:ℂ) (1:ℝ)).isConnected (by simp))
  have z0 : (0:ℂ)∈disc := by simp [disc]
  have k0 : K 0=1 := by
    have H := Complex.ofRealCLM.circleAverage_comp_comm hR
    have hf' : DiffContOnCl ℂ f (ball 0 |(1:ℝ)|) := by simpa [disc] using hf
    have po := hf'.circleAverage
    have R := Complex.reCLM.circleAverage_comp_comm (hc.circleIntegrable (by norm_num))
    have hr : Real.circleAverage (fun ζ => (f ζ).re) 0 1=1 := by
      change Real.circleAverage (Complex.reCLM ∘ f) 0 1 = 1
      rw [R,po,f0]; rfl
    calc
      K 0 = Real.circleAverage (fun ζ => ((f ζ).re:ℂ)) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro ζ hζ
        have hn : ζ≠0 := by intro he; simp [he] at hζ
        simp [herglotzRieszKernel_def,hn]
      _ = 1 := by simpa [Function.comp_def,hr] using H
  have eq := (hcst z hz).trans (hcst 0 z0).symm
  change K z-f z=K 0-f 0 at eq
  rw [k0,f0,sub_self] at eq
  exact sub_eq_zero.mp eq

end Springer
