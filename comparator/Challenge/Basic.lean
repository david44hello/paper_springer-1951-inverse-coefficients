import Mathlib

/- Frozen input: Springer/Basic.lean -/
noncomputable section
open Set Filter Function Complex
open scoped Topology
namespace Springer

def exterior : Set ℂ := {z | 1 < ‖z‖}

def disc : Set ℂ := Metric.ball 0 1

def profile (g : ℂ → ℂ) (t : ℂ) := if t=0 then 1 else t*g t⁻¹

structure Sigma (g : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ g exterior
  univalent : InjOn g exterior
  regular : AnalyticOnNhd ℂ (profile g) disc
  centered : deriv (profile g) 0=0

def inverseProfile (g : ℂ → ℂ) := profile (invFunOn g exterior)

def taylorCoeff (f : ℂ → ℂ) (n : ℕ) := iteratedDeriv n f 0 / n.factorial

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
    (∀ᶠ y : ℂ in 𝓝[≠] 0, invFunOn g exterior y⁻¹∈exterior ∧ g (invFunOn g exterior y⁻¹)=y⁻¹) := by sorry

end Springer
end
