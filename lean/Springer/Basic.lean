import Mathlib

noncomputable section
open Set Filter Function Complex
open scoped Topology
namespace Springer

def exterior : Set ℂ := {z | 1 < ‖z‖}

def disc : Set ℂ := Metric.ball 0 1

/-- In reciprocal coordinates this equals t g(1/t), with its normalized value at zero. -/
def profile (g : ℂ → ℂ) (t : ℂ) := if t=0 then 1 else t*g t⁻¹

@[simp] theorem profile_zero (g : ℂ → ℂ) : profile g 0=1 := by simp [profile]

/-- Analytic univalent exterior maps with leading Laurent coefficient one and constant term zero. -/
structure Sigma (g : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ g exterior
  univalent : InjOn g exterior
  regular : AnalyticOnNhd ℂ (profile g) disc
  centered : deriv (profile g) 0=0

def inverseProfile (g : ℂ → ℂ) := profile (invFunOn g exterior)

def taylorCoeff (f : ℂ → ℂ) (n : ℕ) := iteratedDeriv n f 0 / n.factorial

/-- Coefficient of w^(-n) in the actual exterior inverse. The normalized inverse profile
has degree shifted by one because it includes the factor t=1/w. -/
def inverseCoeff (g : ℂ → ℂ) (n : ℕ) := taylorCoeff (inverseProfile g) (n+1)

def forwardCoeff (g : ℂ → ℂ) (n : ℕ) := taylorCoeff (profile g) (n+1)

def arcMap (z : ℂ) := z-3/(4*z-2)

def trinomialMap (m : ℕ) (z : ℂ) := z+(1-1/(m:ℂ))/z+(1/(2*(m:ℂ)))/z^2

def circularArc : Set ℂ := {w | ‖w-3/2‖=2 ∧ w.re≤1/2}

def realBinom (x : ℝ) (k : ℕ) : ℝ := (∏ j ∈ Finset.range k, (x-j))/k.factorial

def sigmaBound (n : ℕ) : ℝ :=
  let q := (n+1).minFac
  realBinom (2*(n:ℝ)/(q:ℝ)) ((n+1)/q) / n

theorem inverse_germ {g : ℂ → ℂ} (hg : Sigma g) :
    AnalyticAt ℂ (inverseProfile g) 0 ∧ deriv (inverseProfile g) 0=0 ∧
    (∀ᶠ t : ℂ in 𝓝 (0:ℂ), inverseProfile g (t/profile g t) = (profile g t)⁻¹) ∧
    (∀ᶠ y : ℂ in 𝓝[≠] 0, invFunOn g exterior y⁻¹∈exterior ∧ g (invFunOn g exterior y⁻¹)=y⁻¹) := by
  let A := profile g
  let q := fun t => t/A t
  have a₀ : A 0=1 := profile_zero g
  have hA : AnalyticAt ℂ A 0 := hg.regular _ (by simp [disc])
  have hq : AnalyticAt ℂ q 0 := analyticAt_id.div hA (by rw [a₀]; norm_num)
  have q₀ : q 0=0 := by simp [q]
  have hd : HasDerivAt q 1 0 := by change HasDerivAt (id / A) 1 0; simpa [a₀] using (hasDerivAt_id (0:ℂ)).div hA.differentiableAt.hasDerivAt (by rw [a₀]; norm_num)
  have hn : deriv q 0≠0 := hd.deriv ▸ one_ne_zero
  let s := hq.hasStrictDerivAt.localInverse _ _ _ hn
  have hleft : ∀ᶠ t in 𝓝 (0:ℂ), s (q t)=t := hq.hasStrictDerivAt.eventually_left_inverse hn
  have s₀ : s 0=0 := by simpa [q₀] using (show (fun t => s (q t)) =ᶠ[𝓝 0] id from hleft).eq_of_nhds
  have hright : ∀ᶠ y in 𝓝 (0:ℂ), q (s y)=y := by simpa only [q₀] using hq.hasStrictDerivAt.eventually_right_inverse hn
  have hs : AnalyticAt ℂ s 0 := q₀ ▸ hq.analyticAt_localInverse hn
  have hs' : Tendsto s (𝓝 0) (𝓝 0) := by simpa only [s₀] using hs.continuousAt.tendsto
  have good : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖<1 ∧ A t≠0 := by
    apply (continuous_norm.continuousAt.eventually (Iio_mem_nhds (by simp : ‖(0:ℂ)‖<1))).and
    exact hA.continuousAt.eventually_ne (by rw [a₀]; norm_num)
  have calcInv (t : ℂ) (ht : t≠0) (h₁ : ‖t‖<1) (h₂ : A t≠0) :
      invFunOn g exterior (q t)⁻¹=t⁻¹ ∧ t⁻¹∈exterior ∧ g t⁻¹=(q t)⁻¹ := by
    have he : t⁻¹∈exterior := by
      change 1<‖t⁻¹‖; rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr ht)).mpr h₁
    have hv : g t⁻¹=(q t)⁻¹ := by simp [q,A,profile,ht,mul_div_cancel_left₀,div_eq_mul_inv]; field_simp
    exact ⟨hv ▸ hg.univalent.leftInvOn_invFunOn he,he,hv⟩
  have ident : inverseProfile g =ᶠ[𝓝 0] fun y => (A (s y))⁻¹ := by
    filter_upwards [hright,hs'.eventually good] with y hy hy'
    by_cases hy₀ : y=0
    · simp [inverseProfile,hy₀,s₀,a₀]
    have ht : s y≠0 := fun h => hy₀ (by rw [←hy,h,q₀])
    have E := (calcInv _ ht hy'.1 hy'.2).1
    rw [hy] at E
    rw [inverseProfile,profile,if_neg hy₀,E]
    calc
      y*(s y)⁻¹ = q (s y)*(s y)⁻¹ := by rw [hy]
      _ = _ := by dsimp only [q]; field_simp
  have hcomp := hA.comp_of_eq hs s₀
  have han := hcomp.inv (by simp [s₀,a₀])
  have hzero : HasDerivAt (fun y => (A (s y))⁻¹) 0 0 := by
    have dA : HasDerivAt A 0 (s 0) := by rw [s₀]; simpa only [A,hg.centered] using hA.differentiableAt.hasDerivAt
    change HasDerivAt (A ∘ s)⁻¹ 0 0
    simpa [s₀,a₀] using ((dA.comp 0 hs.differentiableAt.hasDerivAt).inv (by simp [s₀,a₀]))
  refine ⟨han.congr ident.symm,(hzero.congr_of_eventuallyEq ident).deriv,?_,?_⟩
  · have hQ : Tendsto q (𝓝 0) (𝓝 0) := by simpa only [q₀] using hq.continuousAt.tendsto
    filter_upwards [hQ.eventually ident,hleft] with t h hl
    exact h.trans (by rw [hl])
  · filter_upwards [hright.filter_mono nhdsWithin_le_nhds,(hs'.eventually good).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with y hy hy' (hy₀ : y≠0)
    have ht : s y≠0 := fun h => hy₀ (by rw [←hy,h,q₀])
    obtain ⟨h1,h2,h3⟩ := calcInv _ ht hy'.1 hy'.2
    rw [hy] at h1 h3
    rw [h1]; exact ⟨h2,h3⟩

end Springer
