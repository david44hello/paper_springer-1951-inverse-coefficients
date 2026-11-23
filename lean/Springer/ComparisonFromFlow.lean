import Springer.ComparisonRightSlope
import Springer.ComparisonLeftSlope

noncomputable section
open Set Finset Complex MeasureTheory
namespace Springer

private theorem ac_sum {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (s : Finset ℕ) (f : ℕ → ℝ → E)
    (h : ∀ i∈s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun x => ∑ i ∈ s, f i x) a b := by
  induction s using Finset.induction_on with
  | empty => simpa using (LipschitzWith.const (0:E)).lipschitzOnWith.absolutelyContinuousOnInterval (a:=a) (b:=b)
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact (h i (mem_insert_self _ _)).add (ih (fun j hj => h j (mem_insert_of_mem hj)))

theorem comparison_paths_ac {s : ℝ} {H : ℝ → PowerSeries ℂ} {P : ℝ → ℂ}
    (hH : ∀ j, AbsolutelyContinuousOnInterval (fun t => (H t).coeff j) s 1)
    (hP : AbsolutelyContinuousOnInterval P s 1) (n : ℕ) (u : ℝ) (c : ℂ) :
    AbsolutelyContinuousOnInterval (fun t => comparisonValue (H t) u c n) s 1 ∧
      AbsolutelyContinuousOnInterval (fun t => comparisonBound (P t) u t c n) s 1 := by
  constructor
  · unfold comparisonValue expShift
    have hsum := ac_sum (a:=s) (b:=1) (range (2*n+1))
      (fun k t => c^k/(k.factorial:ℂ)*functionalCoeff (H t) (u:ℂ) (2*n-k))
      (fun k _ => (functional_ac hH (u:ℂ) (2*n-k)).const_smul (c^k/(k.factorial:ℂ)))
    exact hsum.sub (modelV_ac (hH 0) (u:ℂ) (2*n))
  · have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) s 1 :=
      (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
    have hz : AbsolutelyContinuousOnInterval (fun x => ‖c-(u:ℂ)*P x‖) s 1 :=
      lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (hc.sub (hP.const_smul (u:ℂ)))
    have ht : AbsolutelyContinuousOnInterval (fun x : ℝ => (x:ℂ)) s 1 :=
      Complex.ofRealCLM.lipschitzWith.lipschitzOnWith.absolutelyContinuousOnInterval
    have hU (j : ℕ) := Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval (modelU_ac ht (u:ℂ) j)
    have hV (j : ℕ) := Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval (modelV_ac ht (u:ℂ) j)
    simp only [Function.comp_def,Complex.reCLM_apply,modelU_ofReal,modelV_ofReal,Complex.ofReal_re] at hU hV
    have hp (k : ℕ) : AbsolutelyContinuousOnInterval (fun x => ‖c-(u:ℂ)*P x‖^k) s 1 := by
      induction k with
      | zero => simpa using (LipschitzWith.const (1:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval (a:=s) (b:=1)
      | succ k ih => simpa only [pow_succ,Pi.mul_def] using ih.mul hz
    simp only [comparisonBound,comparisonPolynomial_sq]
    apply AbsolutelyContinuousOnInterval.sub
    · apply ac_sum; intro k hk
      have h := (hp k).mul (hU (2*n-k))
      have h' := h.const_mul (((k.factorial:ℝ))⁻¹)
      simpa only [Pi.mul_def,div_eq_mul_inv,mul_left_comm,mul_assoc,mul_comm] using h'
    · exact hV _

/-- Proposition 6.1 deduced from the analytic coefficient evolution in Lemma 3.1. -/
theorem comparison_of_flow_retained {s : ℝ} (hs : 0 < s) (H : ℝ → PowerSeries ℂ) (P : ℝ → ℂ)
    (μ : ℝ → Measure Circle) [∀ t, IsProbabilityMeasure (μ t)] (hinit : H s=0)
    (hH : ∀ j, AbsolutelyContinuousOnInterval (fun t => (H t).coeff j) s 1)
    (hP : AbsolutelyContinuousOnInterval P s 1)
    (hd : ∀ᵐ t ∂volume.restrict (Set.Icc s 1),
      HasDerivAt P (-(∫ ξ : Circle, (ξ:ℂ) ∂μ t)/(Real.sqrt t:ℂ)) t ∧
      CoeffDerivAt H (averagedDirection (H t) (fun ξ : Circle => (Real.sqrt t:ℂ)*ξ-P t) (μ t)) t) :
    ∀ n t, t∈Set.Icc s 1 → ∀ u, u∈Set.Icc 0 1 → ∀ c : ℂ,
      ‖comparisonValue (H t) u c n‖ ≤ comparisonBound (P t) u t c n - comparisonBound (P s) u s c n := by
  apply comparison_of_evolution_slopes_retained hs.le hinit P μ
  · intro n u hu c; exact comparison_paths_ac hH hP n u c
  · intro n u hu c
    filter_upwards [hd,ae_restrict_mem measurableSet_Icc] with t h ht
    exact ⟨comparisonValue_hasDeriv (P t) c (μ t) hu.1 n h.2,
      comparisonBound_hasDeriv (μ t) (hs.trans_le ht.1) u c n h.1⟩

theorem comparison_of_flow {s : ℝ} (hs : 0 < s) (H : ℝ → PowerSeries ℂ) (P : ℝ → ℂ)
    (μ : ℝ → Measure Circle) [∀ t, IsProbabilityMeasure (μ t)] (hinit : H s=0)
    (hH : ∀ j, AbsolutelyContinuousOnInterval (fun t => (H t).coeff j) s 1)
    (hP : AbsolutelyContinuousOnInterval P s 1)
    (hd : ∀ᵐ t ∂volume.restrict (Set.Icc s 1),
      HasDerivAt P (-(∫ ξ : Circle, (ξ:ℂ) ∂μ t)/(Real.sqrt t:ℂ)) t ∧
      CoeffDerivAt H (averagedDirection (H t) (fun ξ : Circle => (Real.sqrt t:ℂ)*ξ-P t) (μ t)) t) :
    ∀ n t, t∈Set.Icc s 1 → ∀ u, u∈Set.Icc 0 1 → ∀ c : ℂ,
      ‖comparisonValue (H t) u c n‖ ≤ comparisonBound (P t) u t c n := by
  intro n t ht u hu c
  exact (comparison_of_flow_retained hs H P μ hinit hH hP hd n t ht u hu c).trans
    (sub_le_self _ (comparison_initial hu hs.le _ _ _))

end Springer
