import Springer.Dilation
import Springer.Slit

noncomputable section
open Set Complex Filter Finset
open scoped Topology
namespace Springer

/-- The mass multiplying the first coefficient in the center of the disk of Theorem 1.3. -/
def diskWeight (m : ℕ) : ℝ := (1/2:ℝ)^m * (catalan m:ℝ)

theorem diskWeight_pos (m : ℕ) : 0 < diskWeight m := by
  have hc : 0 < catalan m := by
    induction m with
    | zero => simp
    | succ n ih =>
      rw [catalan_succ]
      apply lt_of_lt_of_le _ (Finset.single_le_sum (f:=fun i : Fin (n+1) =>
        catalan i * catalan (n-i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (0 : Fin (n+1))))
      simpa using ih
  unfold diskWeight
  positivity

def DiskBound (g : ℂ → ℂ) (m : ℕ) : Prop :=
  ‖inverseCoeff g (2*m+1) + (diskWeight m:ℂ)*(forwardCoeff g 1)^(m+1)‖ ≤
    (1-(1/2:ℝ)^m)*(catalan m:ℝ)

theorem inverse_first_eq_neg_forward {g : ℂ → ℂ} (hg : Sigma g) :
    inverseCoeff g 1 = -forwardCoeff g 1 := by
  simpa [forwardCoeff] using (inverse_residue hg (n:=1) (by decide))

theorem diskBound_zero {g : ℂ → ℂ} (hg : Sigma g) : DiskBound g 0 := by
  simp [DiskBound, diskWeight, inverse_first_eq_neg_forward hg]

theorem diskBound_of_omitted_disk_bound {m : ℕ}
    (h : ∀ g : ℂ → ℂ, Sigma g → OmitsDisk g → DiskBound g m) {g : ℂ → ℂ} (hg : Sigma g) :
    DiskBound g m := by
  let C : Set (ℂ × ℂ) := {p | ‖p.2+(diskWeight m:ℂ)*p.1^(m+1)‖ ≤
    (1-(1/2:ℝ)^m)*(catalan m:ℝ)}
  have hc : IsClosed C := isClosed_le (by fun_prop) continuous_const
  exact closed_coeff_constraint hc 1 (2*m+1) h hg

theorem DiskBound.refined {g : ℂ → ℂ} {m : ℕ} (h : DiskBound g m) :
    ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ) -
      diskWeight m*(1-‖forwardCoeff g 1‖^(m+1)) := by
  let B := inverseCoeff g (2*m+1)
  let T := (diskWeight m:ℂ)*(forwardCoeff g 1)^(m+1)
  have ht : ‖T‖=diskWeight m*‖forwardCoeff g 1‖^(m+1) := by
    simp [T, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (diskWeight_pos m)]
  have ht' := norm_sub_le (B+T) T
  rw [add_sub_cancel_right, ht] at ht'
  change ‖B+T‖ ≤ _ at h
  change ‖B‖ ≤ _
  unfold diskWeight at *
  linarith only [h,ht',show (1-(1/2:ℝ)^m)*(catalan m:ℝ) =
    (catalan m:ℝ) - (1/2:ℝ)^m*(catalan m:ℝ) by ring,
    show (1/2:ℝ)^m*(catalan m:ℝ)*(1-‖forwardCoeff g 1‖^(m+1)) =
      (1/2:ℝ)^m*(catalan m:ℝ)-(1/2:ℝ)^m*(catalan m:ℝ)*‖forwardCoeff g 1‖^(m+1) by ring]

theorem DiskBound.odd {g : ℂ → ℂ} {m : ℕ} (h : DiskBound g m) (hb : ‖forwardCoeff g 1‖ ≤ 1) :
    ‖inverseCoeff g (2*m+1)‖ ≤ (catalan m:ℝ) := by
  apply h.refined.trans
  exact sub_le_self _ (mul_nonneg (diskWeight_pos m).le
    (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) hb)))

theorem DiskBound.firstCoeff_of_equality {g : ℂ → ℂ} {m : ℕ} (h : DiskBound g m)
    (hb : ‖forwardCoeff g 1‖ ≤ 1) (he : ‖inverseCoeff g (2*m+1)‖=(catalan m:ℝ)) :
    ‖forwardCoeff g 1‖=1 := by
  apply le_antisymm hb
  by_contra! hlt
  have hp : ‖forwardCoeff g 1‖^(m+1) < 1 :=
    pow_lt_one₀ (norm_nonneg _) hlt (Nat.succ_ne_zero m)
  have hstrict := mul_pos (diskWeight_pos m) (sub_pos.mpr hp)
  have H := h.refined
  linarith

theorem slit_odd_attains {b : ℂ} (hb : ‖b‖=1) (m : ℕ) :
    ‖inverseCoeff (slitMap b) (2*m+1)‖=(catalan m:ℝ) := by
  rw [slit_inverse_odd hb.le, norm_mul, norm_neg, norm_pow, hb, one_pow, mul_one]
  simp

end Springer
